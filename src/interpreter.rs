use std::error::Error;
use std::fmt::{Display, Formatter};
use std::time::{Duration, Instant};

use rand::prelude::*;

#[derive(Debug)]
enum RuntimeError {
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



pub struct Interpreter {
    memory: Vec<u8>,
    display: Vec<[bool;64]>,
    registers: [u8;16],
    pc: u16,
    i: u16,
    stack: Vec<u16>,
    duration_count: u8,
    sound_count: u8,
}

impl Interpreter {
    pub fn new() -> Interpreter {
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

    fn load_bytes(&mut self, start_addr: u16, bytes: Vec<u8>) {
        self.memory.iter_mut()
            .skip(start_addr as usize)
            .zip(bytes.into_iter())
            .for_each(|(mem, byte)| *mem = byte);

        self.pc = start_addr;
    }

    fn fetch_instruction(&mut self) -> Result<u16, RuntimeError> {
        let msb = *self.memory.get(self.pc as usize).ok_or_else(|| RuntimeError::MemNotFound(self.pc))?;
        let lsb = *self.memory.get((self.pc+1) as usize).ok_or_else(|| RuntimeError::MemNotFound(self.pc+1))?;

        self.pc += 2;

        Ok( ((msb as u16) << 8) + lsb as u16 )
    }

    fn clear_display(&mut self) { self.display = vec![[false;64];32]; }

    fn call_subroutine(&mut self, addr: u16) {
        self.stack.push(self.pc);
        self.pc = addr;
    }

    fn ret_from_subroutine(&mut self) -> Result<(), RuntimeError> {
        if let Some(addr) = self.stack.pop() {
            self.pc = addr;
            Ok(())
        } else {
            Err(RuntimeError::StackUnderflow)
        }
    }

    fn jump_to_addr(&mut self, addr: u16) { self.pc = addr; }

    fn set_vx_to_byte(&mut self, vx: u8, byte: u8) {
        self.registers[vx as usize] = byte;
    }

    fn add_byte_to_vx(&mut self, vx: u8, byte: u8) {
        let (sum, _) = self.registers[vx as usize].overflowing_add(byte);
        self.registers[vx as usize] = sum;
    }

    fn skip_if_eq(&mut self, vx: u8, byte: u8) {
        if self.registers[vx as usize] == byte {
            self.pc += 2;
        }
    }

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
        self.registers[0xF] = overflow as u8;
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
        self.registers[0xF] = overflow as u8;
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

    // fn set

    fn draw(&mut self, x_reg: u8, y_reg: u8, n: u8) {
        let x = self.registers[x_reg as usize] % self.display[0].len() as u8;
        let y = self.registers[y_reg as usize] % self.display.len() as u8;


        let sprites: Vec<_> = self.memory.iter()
            .skip(self.i as usize)
            .take(n as usize)
            .map(|byte| vec![
                (byte & 0x80) != 0, (byte & 0x40) != 0, (byte & 0x20) != 0, (byte & 0x10) != 0,
                (byte & 0x8) != 0, (byte & 0x4) != 0, (byte & 0x2) != 0, (byte & 0x1) != 0,
            ])
            .collect();

        let mut collision = false;

        self.display.iter_mut().skip(y as usize)
            .map(|row| row.iter_mut().skip(x as usize))
            .zip(sprites.into_iter())
            .for_each(|(row, sprite)| row
                .zip(sprite.into_iter())
                .for_each(|(x, s)| {
                    if *x && s { collision = true; }
                    *x ^= s
                })
            );

        self.set_vx_to_byte(0xF, collision as u8);
    }

    fn start(&mut self) -> Result<(), RuntimeError> {
        loop {
            let instruction = self.fetch_instruction()?;

            let high_nibble: u8 = (instruction >> 0xFFF) as u8;
            let n: u8 = instruction as u8 & 0xF;
            let nn: u8 = instruction as u8 & 0xFF;
            let nnn: u16 = instruction & 0xFFF;
            let x: u8 = (instruction >> 0xFF) as u8 & 0xF;
            let y: u8 = (instruction >> 0xF) as u8 & 0xF;

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
                        // 0x9E => self.skip_if_held(x),
                        // 0xA1 => self.skip_if_not_held(x),
                        _ => Err(RuntimeError::UnknownInstruction(instruction))?
                    }

            // 0xF => {},

            _ => Err(RuntimeError::UnknownInstruction(instruction))?


        }
    }
}
}

impl Display for Interpreter {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut output = String::new();

        for row in self.display.iter().rev() {
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
