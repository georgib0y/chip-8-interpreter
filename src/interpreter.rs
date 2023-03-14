use std::error::Error;
use std::fmt::{Display, Formatter};
use std::time::{Duration, Instant};
use bevy::prelude::Resource;
use bevy::utils::tracing::field::display;

use rand::prelude::*;

const FONT: [u8;5*16] = [
    0xF0, 0x90, 0x90, 0x90, 0xF0, // 0
    0x20, 0x60, 0x20, 0x20, 0x70, // 1
    0xF0, 0x10, 0xF0, 0x80, 0xF0, // 2
    0xF0, 0x10, 0xF0, 0x10, 0xF0, // 3
    0x90, 0x90, 0xF0, 0x10, 0x10, // 4
    0xF0, 0x80, 0xF0, 0x10, 0xF0, // 5
    0xF0, 0x80, 0xF0, 0x90, 0xF0, // 6
    0xF0, 0x10, 0x20, 0x40, 0x40, // 7
    0xF0, 0x90, 0xF0, 0x90, 0xF0, // 8
    0xF0, 0x90, 0xF0, 0x10, 0xF0, // 9
    0xF0, 0x90, 0xF0, 0x90, 0x90, // A
    0xE0, 0x90, 0xE0, 0x90, 0xE0, // B
    0xF0, 0x80, 0x80, 0x80, 0xF0, // C
    0xE0, 0x90, 0x90, 0x90, 0xE0, // D
    0xF0, 0x80, 0xF0, 0x80, 0xF0, // E
    0xF0, 0x80, 0xF0, 0x80, 0x80  // F
];

const FONT_START_ADDR: u16 = 0x050;

const PROG_START_ADDR: u16 = 0x200;


#[derive(Debug)]
pub enum RuntimeError {
    MemNotFound(u16),
    StackUnderflow,
    UnknownInstruction(u16),
}

impl Error for RuntimeError {}

impl Display for RuntimeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeError::MemNotFound(addr) => write!(f, "Memory location not found: {addr:#06x} (possibly could have overrun pc?)"),
            RuntimeError::StackUnderflow => write!(f, "Stack has underflowed"),
            RuntimeError::UnknownInstruction(addr) => write!(f, "Unknown instruction: {addr:#06x}")
        }
    }
}


#[derive(Debug, Resource)]
pub struct Interpreter {
    pub memory: Vec<u8>,
    pub display: Vec<[bool;64]>,
    pub registers: [u8;16],
    pub pc: u16,
    pub i: u16,
    pub stack: Vec<u16>,
    pub duration_count: u8,
    pub sound_count: u8,
}

impl Default for Interpreter {
    fn default() -> Self {
        Interpreter {
            memory: vec![0; 4096],
            display: vec![[false;64];32],
            registers: [0;16],
            pc: 0,
            i: 0,
            stack: Vec::new(),
            duration_count: 0,
            sound_count: 0,
        }
    }
}

impl Interpreter {
    pub fn new_with_bytes(bytes: Vec<u8>) -> Self {
        let mut interpreter = Interpreter::default();

        // load fonts
        interpreter.load_bytes_at_addr(FONT_START_ADDR, FONT.to_vec());
        // load the given program
        interpreter.load_bytes_at_addr(PROG_START_ADDR, bytes);
        interpreter.pc = PROG_START_ADDR;


        interpreter
    }

    fn load_bytes_at_addr(&mut self, start_addr: u16, bytes: Vec<u8>) {
        self.memory.iter_mut()
            .skip(start_addr as usize)
            .zip(bytes.into_iter())
            .for_each(|(mem, byte)| *mem = byte);
    }

    fn fetch_instruction(&mut self) -> Result<u16, RuntimeError> {
        let msb = *self.memory.get(self.pc as usize)
            .ok_or_else(|| RuntimeError::MemNotFound(self.pc))? as u16;

        let lsb = *self.memory.get((self.pc+1) as usize)
            .ok_or_else(|| RuntimeError::MemNotFound(self.pc+1))? as u16;

        self.pc += 2;

        Ok( msb << 8 | lsb )
    }

    // 0x00E0
    fn clear_display(&mut self) { self.display = vec![[false;64];32]; }

    // 0x2NNN
    fn call_subroutine(&mut self, addr: u16) {
        self.stack.push(self.pc);
        self.pc = addr;
    }

    // 0x00EE
    fn ret_from_subroutine(&mut self) -> Result<(), RuntimeError> {
        if let Some(addr) = self.stack.pop() {
            self.pc = addr;
            Ok(())
        } else {
            Err(RuntimeError::StackUnderflow)
        }
    }

    // 0x1NNN
    fn jump_to_addr(&mut self, addr: u16) { self.pc = addr; }

    // 0x6XNN
    fn set_vx_to_byte(&mut self, vx: u8, byte: u8) {
        self.registers[vx as usize] = byte;
    }

    // 0x7XNN
    fn add_byte_to_vx(&mut self, vx: u8, byte: u8) {
        let (sum, _) = self.registers[vx as usize].overflowing_add(byte);
        self.registers[vx as usize] = sum;
    }

    // 0x3XNN
    fn skip_if_eq(&mut self, vx: u8, byte: u8) {
        if self.registers[vx as usize] == byte {
            self.pc += 2;
        }
    }

    // 0x4XNN
    fn skip_if_neq(&mut self, vx: u8, byte: u8) {
        if self.registers[vx as usize] != byte {
            self.pc += 2;
        }
    }


    fn skip_if_regs_eq(&mut self, vx: u8, vy: u8) {
        if self.registers[vx as usize] == self.registers[vy as usize] {
            self.pc += 2;
        }
    }

    fn skip_if_regs_neq(&mut self, vx: u8, vy: u8) {
        if self.registers[vx as usize] != self.registers[vy as usize] {
            self.pc += 2;
        }
    }

    fn set_vx_to_vy(&mut self, vx: u8, vy: u8) {
        self.registers[vx as usize] = self.registers[vy as usize];
    }

    fn set_vx_or_vy(&mut self, vx: u8, vy: u8) {
        self.registers[vx as usize] |= self.registers[vy as usize];
    }

    fn set_vx_and_vy(&mut self, vx: u8, vy: u8) {
        self.registers[vx as usize] &= self.registers[vy as usize];
    }

    fn set_vx_xor_vy(&mut self, vx: u8, vy: u8) {
        self.registers[vx as usize] ^= self.registers[vy as usize];
    }

    fn add_vy_to_vx(&mut self, vx: u8, vy: u8) {
        let (sum, overflow) = self.registers[vx as usize]
            .overflowing_add(self.registers[vy as usize]);

        self.registers[vx as usize] = sum;
        self.registers[0xF] = overflow as u8;
    }

    fn vx_sub_vy(&mut self, vx: u8, vy: u8) {
        let (sub, overflow) = self.registers[vx as usize]
            .overflowing_sub(self.registers[vy as usize]);

        self.registers[vx as usize] = sub;
        // vf is set to 1 if the lefthand is bigger than the right hand
        // in other words if underflow then vf = 0, else vf = 1
        self.registers[0xF] = !overflow as u8;
    }


    fn set_vx_shr_xy(&mut self, vx: u8, vy: u8) {
        // this is an optional COSMAC VIP step will break some programs
        self.set_vx_to_vy(vx, vy);

        self.registers[0xF] = (self.registers[vx as usize] & 0x1 != 0) as u8;
        self.registers[vx as usize] >>= 1;
    }


    fn vy_sub_vx(&mut self, vx: u8, vy: u8) {
        let (sub, overflow) = self.registers[vy as usize]
            .overflowing_sub(self.registers[vx as usize]);

        self.registers[vx as usize] = sub;
        // vf is set to 1 if the lefthand is bigger than the right hand
        // in other words if underflow then vf = 0, else vf = 1
        self.registers[0xF] = !overflow as u8;
    }

    fn set_vx_shl_xy(&mut self, vx: u8, vy: u8) {
        // this is an optional COSMAC VIP step will break some programs
        self.set_vx_to_vy(vx, vy);

        self.registers[0xF] = (self.registers[vx as usize] & 0x80 != 0) as u8;
        self.registers[vx as usize] <<= 1;
    }

    fn set_index(&mut self, addr: u16) {
        self.i = addr;
    }

    fn jump_with_offset(&mut self, addr: u16) {
        self.pc = addr + self.registers[0x0] as u16;
    }

    fn set_vx_rand(&mut self, vx: u8, nn: u8) {
        self.registers[vx as usize] = nn & thread_rng().gen::<u8>();
    }

    fn skip_if_held(&mut self, vx: u8, curr_held: Option<u8>) {
        if let Some(held) = curr_held {
            if self.registers[vx as usize] == held { self.pc += 2 }
        }
    }

    fn skip_if_not_held(&mut self, vx: u8, curr_held: Option<u8>) {
        self.pc += 2;

        if let Some(held) = curr_held {
            if self.registers[vx as usize] == held { self.pc -= 2 }
        }
    }

    fn read_delay_timer(&mut self, vx: u8) {
        self.registers[vx as usize] = self.duration_count;
    }

    fn set_delay_timer(&mut self, vx: u8) {
        self.duration_count = self.registers[vx as usize];
    }

    fn set_sound_timer(&mut self, vx: u8) {
        self.sound_count = self.registers[vx as usize];
    }

    fn add_to_index(&mut self, vx: u8) {
        self.i += self.registers[vx as usize] as u16;
    }

    fn get_key(&mut self, vx: u8, curr_key: Option<u8>) {
        // if there is no key pressed at the moment, reurn pc to the previous instruction (this one)
        match curr_key {
            Some(key) => self.registers[vx as usize] = key,
            None => self.pc -= 2,
        }
    }

    fn set_i_to_font_char(&mut self, vx: u8) {
        let (sum, overflow) = self.i
            .overflowing_add(FONT_START_ADDR + self.registers[vx as usize] as u16);

        self.i = sum;
        self.registers[0xF] = overflow as u8;
    }

    fn byte_to_decimal(&mut self, vx: u8) {
        let byte = self.registers[vx as usize];
        let ones = byte % 10;
        let tens = ((byte - ones) / 10) % 10;
        let huns = ((byte - tens - ones) / 100) % 10;

        self.memory[self.i as usize] = huns;
        self.memory[self.i as usize + 1] = tens;
        self.memory[self.i as usize + 2] = ones;
    }

    fn store_registers(&mut self, vx: u8) {
        for reg in 0..=vx {
            self.memory[self.i as usize + reg as usize] = self.registers[reg as usize];
        }
    }

    fn load_registers(&mut self, vx: u8) {
        for reg in 0..=vx {
            self.registers[reg as usize] = self.memory[self.i as usize + reg as usize];
        }
    }


    fn draw(&mut self, vx: u8, vy: u8, n: u8) {
        let x_start = self.registers[vx as usize] as usize % self.display[0].len();
        let y_start = self.registers[vy as usize] as usize % self.display.len();

        let mut collision = false;

        let sprite = self.memory.iter()
            .skip(self.i as usize)
            .take(n as usize)
            .flat_map(|byte| (0..8).rev().map(|shift| (*byte >> shift) & 1 == 1));

        self.display.iter_mut()
            .skip(y_start)
            .take(n as usize)
            .flat_map(|row| row.iter_mut().skip(x_start).take(8))
            .zip(sprite)
            .for_each(|(pixel, sprite)| {
                collision |= *pixel && sprite;
                *pixel ^= sprite;
            });

        self.set_vx_to_byte(0xF, collision as u8);
    }

    pub fn process_next_instruction(&mut self, curr_key: Option<u8>) -> Result<(), RuntimeError> {
        let instruction = self.fetch_instruction()?;


        let high_nibble: u8 = (instruction >> 12) as u8;
        let n: u8 = instruction as u8 & 0xF;
        let nn: u8 = instruction as u8 & 0xFF;
        let nnn: u16 = instruction & 0xFFF;
        let x: u8 = (instruction >> 8) as u8 & 0xF;
        let y: u8 = (instruction >> 4) as u8 & 0xF;

        match high_nibble {
            0x0 => {
                if instruction == 0x00E0 { self.clear_display(); }
                if instruction == 0x00EE { self.ret_from_subroutine()?; }
                // else do nothing as 0NNN should not be implemented
            }

            0x1 => self.jump_to_addr(nnn),

            0x2 => self.call_subroutine(nnn),

            0x3 => self.skip_if_eq(x, nn),

            0x4 => self.skip_if_neq(x, nn),

            0x5 => self.skip_if_regs_eq(x, y),

            0x6 => self.set_vx_to_byte(x, nn),

            0x7 => self.add_byte_to_vx(x, nn),

            0x8 => match n {
                0x0 => self.set_vx_to_vy(x, y),
                0x1 => self.set_vx_or_vy(x, y),
                0x2 => self.set_vx_and_vy(x, y),
                0x3 => self.set_vx_xor_vy(x, y),
                0x4 => self.add_vy_to_vx(x, y),
                0x5 => self.vx_sub_vy(x, y),
                0x6 => self.set_vx_shr_xy(x, y),
                0x7 => self.vy_sub_vx(x, y),
                0xE => self.set_vx_shl_xy(x, y),
                _ => Err(RuntimeError::UnknownInstruction(instruction))?
            },

            0x9 => self.skip_if_regs_neq(x, y),

            0xA => self.set_index(nnn),

            0xB => self.jump_with_offset(nnn),

            0xC => self.set_vx_rand(x, nn),

            0xD => self.draw(x, y, n),

            0xE => match nn {
                    0x9E => self.skip_if_held(x, curr_key),
                    0xA1 => self.skip_if_not_held(x, curr_key),
                    _ => Err(RuntimeError::UnknownInstruction(instruction))?
                }

            0xF => {
                match nn {
                    0x07 => self.read_delay_timer(x),
                    0x15 => self.set_delay_timer(x),
                    0x18 => self.set_sound_timer(x),

                    0x1E => self.add_to_index(x),

                    0x0A => self.get_key(x, curr_key),

                    0x29 => self.set_i_to_font_char(x),

                    0x33 => self.byte_to_decimal(x),

                    0x55 => self.store_registers(x),
                    0x65 => self.load_registers(x),

                    _ => Err(RuntimeError::UnknownInstruction(instruction))?
                }
            },

            _ => Err(RuntimeError::UnknownInstruction(instruction))?

        }
        Ok(())
    }


}

impl Display for Interpreter {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut output = String::new();

        for row in self.display.iter() {
            output.push_str(&row.iter()
                .fold(String::new(), |out, b|
                    format!("{out}{}", if *b { " # "} else { " . "} )
                )
            );

            output.push_str("\n");
        }

        write!(f, "{output}")
    }
}
