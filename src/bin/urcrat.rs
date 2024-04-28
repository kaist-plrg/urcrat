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
    let elapsed = match args.command {
        Command::May { dump } => {
            let start = std::time::Instant::now();
            let solutions = points_to::analyze_path(&file);
            let elapsed = start.elapsed();
            if let Some(dump) = dump {
                let arr = points_to::serialize_solutions(&solutions);
                std::fs::write(dump, arr).unwrap();
            }
            elapsed
        }
        Command::Must { may, r#union } => {
            let solutions = may.map(|file| {
                let arr = std::fs::read(file).unwrap();
                points_to::deserialize_solutions(&arr)
            });
            let conf = analysis::Config {
                solutions,
                unions: r#union.into_iter().collect(),
            };
            let start = std::time::Instant::now();
            analysis::analyze_path(&file, &conf);
            start.elapsed()
        }
    };
    println!("{}", elapsed.as_millis());
}
