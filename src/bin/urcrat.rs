use std::{
    fs::{self, File},
    path::{Path, PathBuf},
};

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
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
}

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    log: Option<PathBuf>,
    #[arg(short, long)]
    verbose: bool,

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
    match args.command {
        Command::May { dump } => {
            let solutions = may_analysis::analyze_path(&file);
            if let Some(dump) = dump {
                let arr = may_analysis::serialize_solutions(&solutions);
                std::fs::write(dump, arr).unwrap();
            }
        }
        Command::Must {
            may,
            r#union,
            output,
        } => {
            let transform = output.is_some();
            let file = if let Some(mut output) = output {
                output.push(args.input.file_name().unwrap());
                if output.exists() {
                    assert!(output.is_dir());
                    clear_dir(&output);
                } else {
                    fs::create_dir(&output).unwrap();
                }
                copy_dir(&args.input, &output, true);
                output.join("c2rust-lib.rs")
            } else {
                file
            };
            let solutions = may.map(|file| {
                let arr = std::fs::read(file).unwrap();
                may_analysis::deserialize_solutions(&arr)
            });
            let conf = tag_analysis::Config {
                solutions,
                unions: r#union.into_iter().collect(),
                transform,
                verbose: args.verbose,
            };
            let stat = tag_analysis::analyze_path(&file, &conf);
            println!("{}", stat);
        }
    }
}

fn clear_dir(path: &Path) {
    for entry in fs::read_dir(path).unwrap() {
        let entry_path = entry.unwrap().path();
        if entry_path.is_dir() {
            let name = entry_path.file_name().unwrap();
            if name != "target" {
                fs::remove_dir_all(entry_path).unwrap();
            }
        } else {
            fs::remove_file(entry_path).unwrap();
        }
    }
}

fn copy_dir(src: &Path, dst: &Path, root: bool) {
    for entry in fs::read_dir(src).unwrap() {
        let src_path = entry.unwrap().path();
        let name = src_path.file_name().unwrap();
        let dst_path = dst.join(name);
        if src_path.is_file() {
            fs::copy(src_path, dst_path).unwrap();
        } else if src_path.is_dir() && (!root || name != "target") {
            fs::create_dir(&dst_path).unwrap();
            copy_dir(&src_path, &dst_path, false);
        }
    }
}
