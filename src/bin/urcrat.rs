use std::{fs::File, path::PathBuf};

use clap::Parser;
use urcrat::*;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    log_file: Option<PathBuf>,
    #[arg(short, long)]
    include_union: Vec<String>,
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
    // let conf = analysis::Config {
    //     unions: args.include_union.into_iter().collect(),
    // };
    // analysis::analyze_path(&file, &conf);
    let start = std::time::Instant::now();
    points_to::analyze_path(&file);
    let elapsed = start.elapsed();
    println!("{}", elapsed.as_millis());
}
