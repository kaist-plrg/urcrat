use std::{fs::File, path::PathBuf};

use clap::Parser;
use urcrat::*;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    log_file: Option<PathBuf>,
    input: PathBuf,
}

fn main() {
    let args = Args::parse();

    if let Some(log) = args.log_file {
        let log_file = File::create(log).unwrap();
        tracing_subscriber::fmt()
            .with_max_level(tracing::Level::INFO)
            .with_ansi(false)
            .with_writer(log_file)
            .init();
    }

    let file = args.input.join("c2rust-lib.rs");
    // steensgaard::analyze_path(&file);
    relational::analyze_str(
        "
    union U { x: i32, y: f32 }
    fn f(u: U) -> i32 {
        u.x + u.y as i32
    }
    ",
    );
}
