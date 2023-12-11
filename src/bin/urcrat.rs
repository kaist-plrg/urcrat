use std::path::PathBuf;

use clap::Parser;
use urcrat::*;

#[derive(Parser, Debug)]
struct Args {
    input: PathBuf,
}

fn main() {
    // let args = Args::parse();
    // let file = args.input.join("c2rust-lib.rs");
    // analysis::analyze(&file);
    steensgaard::analyze_str(
        "
    unsafe fn f() {
        let mut x: i32 = 0;
        let mut y: *mut i32 = &mut x;
        let mut z: *mut i32 = &mut *y;
    }
    ",
    );
}
