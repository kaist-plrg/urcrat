use std::path::PathBuf;

use clap::Parser;
use urcrat::*;

#[derive(Parser, Debug)]
struct Args {
    input: PathBuf,
}

fn main() {
    let args = Args::parse();
    let file = args.input.join("c2rust-lib.rs");
    analysis::analyze(&file);
}
