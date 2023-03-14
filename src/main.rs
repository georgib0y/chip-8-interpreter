use std::error::Error;
use std::fmt::Display;
use std::fs::File;
use std::io::{BufReader, Read, stdin, stdout};
use std::time::{Duration, Instant};

use bevy::prelude::*;
use bevy::time::FixedTimestep;
use bevy::utils::HashMap;
use crate::interpreter::Interpreter;

mod interpreter;

const FAST_RATE_HZ: f64 = 700.0;
const FAST_RATE_SEC: f64 = 1.0 / FAST_RATE_HZ;

const SLOW_RATE_HZ: f64 = 60.0;
const SLOW_RATE_SEC: f64 = 1.0 / SLOW_RATE_HZ;

const PIXEL_WIDTH: f32 = 10.0;
const SQUARE_SIZE: Option<Vec2> = Some( Vec2::new(PIXEL_WIDTH, PIXEL_WIDTH) );

const ON_COLOUR: Color = Color::rgb(1.0, 1.0, 1.0);
const OFF_COLOUR: Color = Color::rgb(0.0, 0.0, 0.0);


fn main() {
    let mut program: Vec<u8> = Vec::new();
    // let file = File::open("ibm_test.ch8").unwrap();
    // let file = File::open("test_opcode.ch8").unwrap();
    let file = File::open("bc_test.ch8").unwrap();
    let mut reader = BufReader::new(file);

    reader.read_to_end(&mut program).unwrap();

    // let mut interpreter = Interpreter::new_with_bytes(program);
    // loop{
    //     interpreter.process_next_instruction(None).unwrap();
    //     println!("{interpreter}");
    // }

    App::new()
        .init_resource::<Interpreter>()
        .add_plugins(DefaultPlugins)
        .insert_resource(Interpreter::new_with_bytes(program))
        .init_resource::<KeyBinds>()
        .add_startup_system(setup_display)
        .add_system_set(
            SystemSet::new()
                .with_run_criteria(FixedTimestep::step(FAST_RATE_SEC))
                .with_system(processor)
        )
        .add_system_set(
            SystemSet::new()
                .with_run_criteria(FixedTimestep::step(SLOW_RATE_SEC))
                .with_system(display_update)
                .with_system(delay_and_sound)
        )
        .run();

}

#[derive(Resource)]
struct KeyBinds(HashMap<KeyCode, u8>);

impl Default for KeyBinds {
    fn default() -> Self {
        let mut keybinds = HashMap::new();

        keybinds.insert(KeyCode::Key1, 0x0);
        keybinds.insert(KeyCode::Key2, 0x1);
        keybinds.insert(KeyCode::Key3, 0x2);
        keybinds.insert(KeyCode::Key4,0x3);
        keybinds.insert(KeyCode::Q, 0x4);
        keybinds.insert(KeyCode::W, 0x5);
        keybinds.insert(KeyCode::E, 0x6);
        keybinds.insert(KeyCode::R, 0x7);
        keybinds.insert(KeyCode::A, 0x8);
        keybinds.insert(KeyCode::S, 0x9);
        keybinds.insert(KeyCode::D, 0xA);
        keybinds.insert(KeyCode::F, 0xB);
        keybinds.insert(KeyCode::Z, 0xC);
        keybinds.insert(KeyCode::X, 0xD);
        keybinds.insert(KeyCode::C, 0xE);
        keybinds.insert(KeyCode::Y, 0xF);

        KeyBinds(keybinds)
    }
}

#[derive(Component)]
struct PixelCoord {
    x: usize,
    y: usize,
}

impl PixelCoord {
    fn chip8_y(&self) -> usize { 31 - self.y }
}

fn setup_display(mut commands: Commands) {
    commands.spawn(Camera2dBundle::default());

    for y in 0..32 {
        for x in 0..64 {
            let x_coord = x as f32 * PIXEL_WIDTH;
            let y_coord = y as f32 * PIXEL_WIDTH;

            commands.spawn((
                PixelCoord { x, y },
                SpriteBundle {
                    sprite: Sprite {
                        color: OFF_COLOUR,
                        custom_size: SQUARE_SIZE,
                        ..default()
                    },

                    transform: Transform::from_xyz(x_coord, y_coord, 1.0),
                    ..default()
                })
            );
        }
    }
}

fn processor(
    mut interpreter: ResMut<Interpreter>,
    keys: Res<Input<KeyCode>>,
    keybinds: Res<KeyBinds>,
) {
    let curr_key = keys.get_pressed().next()
        .and_then(|key| keybinds.0.get(key))
        .and_then(|code| Some(*code));

    interpreter.process_next_instruction(curr_key).unwrap();
}

fn delay_and_sound(
    mut interpreter: ResMut<Interpreter>,
) {
    interpreter.sound_count = interpreter.sound_count.saturating_sub(1);
    interpreter.duration_count = interpreter.duration_count.saturating_sub(1);
}

fn display_update(
    mut query: Query<(&PixelCoord, &mut Sprite)>,
    interpreter: Res<Interpreter>,
) {
    // println!("{}", interpreter.to_string());

    query.iter_mut()
        .for_each(|(coord, mut sprite)| {
            sprite.color = if interpreter.display[coord.chip8_y()][coord.x] {
                ON_COLOUR
            } else {
                OFF_COLOUR
            };
        })
}