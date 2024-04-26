use std::{fs::File, path::PathBuf};

use clap::{Parser, Subcommand};
use urcrat::*;

#[derive(Subcommand, Debug)]
enum Command {
    May {
        #[arg(short, long)]
        dump: Option<PathBuf>,
    },
    Must {
        #[arg(short, long)]
        may: Option<PathBuf>,
        #[arg(short, long)]
        r#union: Vec<String>,
    },
}

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    log: Option<PathBuf>,

    input: PathBuf,

    #[command(subcommand)]
    command: Command,
}

fn main() {
    let args = Args::parse();

    if let Some(log) = args.log {
        let log_file = File::create(log).unwrap();
        tracing_subscriber::fmt()
            .with_max_level(tracing::Level::INFO)
            .with_ansi(false)
            .with_writer(log_file)
            .init();
    }

    let file = args.input.join("c2rust-lib.rs");
    let start = std::time::Instant::now();
    match args.command {
        Command::May { dump } => {
            let solutions = points_to::analyze_path(&file);
            if let Some(dump) = dump {
                let s = points_to::solutions_to_string(&solutions);
                std::fs::write(dump, s).unwrap();
            }
        }
        Command::Must { may, r#union } => {
            let solutions = may.map(|file| {
                let s = std::fs::read(file).unwrap();
                points_to::solutions_from_slice(&s)
            });
            let conf = analysis::Config {
                solutions,
                unions: r#union.into_iter().collect(),
            };
            analysis::analyze_path(&file, &conf);
        }
    }
    let elapsed = start.elapsed();
    println!("{}", elapsed.as_millis());
}
