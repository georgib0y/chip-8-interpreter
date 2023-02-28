use std::error::Error;
use std::io::{Read, stdin, stdout};
use std::time::{Duration, Instant};

use bevy::prelude::*;

mod interpreter;

fn main() {

    App::new()
        .add_plugins(DefaultPlugins)
        .add_startup_system(setup_display)
        .run();

}

fn setup_display(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<ColorMaterial>>
) {
    commands.spawn(Camera2dBundle::default());

    commands.spawn(SpriteBundle {
        sprite: Sprite {
            color: Color::rgb(1.0,1.0,1.0),
            custom_size: Some(Vec2::new(50.0, 50.0)),
            ..default()
        },
        ..default()
    });

}
