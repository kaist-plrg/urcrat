use std::path::PathBuf;

use rustc_ast::{ast::*, ptr::P};
use rustc_ast_pretty::pprust;
use rustc_parse::parser::{ForceCollect, Parser};
use rustc_session::parse::ParseSess;
use rustc_span::{FileName, RealFileName};
use thin_vec::ThinVec;

// use memoize::memoize;
use crate::compile_util::{make_config, path_to_input, run_compiler};

#[inline]
pub fn new_silent_parse_sess() -> ParseSess {
    ParseSess::with_silent_emitter(
        vec![
            rustc_session::DEFAULT_LOCALE_RESOURCE,
            rustc_parse::DEFAULT_LOCALE_RESOURCE,
        ],
        format!("this error occuured in src/astfix/hole.rs"),
        true,
    )
}

#[inline]
pub fn new_parse_sess() -> ParseSess {
    ParseSess::new(vec![
        rustc_session::DEFAULT_LOCALE_RESOURCE,
        rustc_parse::DEFAULT_LOCALE_RESOURCE,
    ])
}

#[inline]
pub fn new_parser_from_sess_str(parse_sess: &ParseSess, s: String) -> Parser<'_> {
    let file_name = FileName::Custom("main.rs".to_string());
    rustc_parse::new_parser_from_source_str(parse_sess, file_name, s).unwrap()
}

#[inline]
pub fn parse_crate(raw: String) -> Crate {
    let parse_sess = new_silent_parse_sess();
    let mut parser = new_parser_from_sess_str(&parse_sess, raw);
    parser.parse_crate_mod().unwrap()
}

#[macro_export]
macro_rules! krate {
    ($($arg:tt)*) => {{
        parse_crate(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_item(item: String) -> Item {
    let parse_sess = new_silent_parse_sess();
    let mut parser = new_parser_from_sess_str(&parse_sess, item);
    parser
        .parse_item(ForceCollect::No)
        .unwrap()
        .unwrap()
        .into_inner()
}

#[macro_export]
macro_rules! item {
    ($($arg:tt)*) => {{
        parse_item(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_items(items: String) -> ThinVec<P<Item>> {
    let krate = parse_crate(items);
    krate.items
}

#[macro_export]
macro_rules! items {
    ($($arg:tt)*) => {{
        parse_items(format!($($arg)*))
    }};
}

// #[memoize]
#[inline]
pub fn parse_expr(raw: String) -> Expr {
    let parse_sess = new_silent_parse_sess();
    let mut parser = new_parser_from_sess_str(&parse_sess, raw);
    parser.parse_expr().unwrap().into_inner()
}

#[macro_export]
macro_rules! expr {
    ($($arg:tt)*) => {{
        parse_expr(format!($($arg)*))
    }};
}

// #[memoize]
#[inline]
pub fn parse_stmt(raw: String) -> Stmt {
    let parse_sess = new_silent_parse_sess();
    let mut parser = new_parser_from_sess_str(&parse_sess, raw);
    parser
        .parse_stmt_without_recovery(true, ForceCollect::No)
        .unwrap()
        .unwrap()
}

#[macro_export]
macro_rules! stmt {
    ($($arg:tt)*) => {{
        parse_stmt(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_pat(raw: String) -> Pat {
    let parse_sess = new_silent_parse_sess();
    let mut parser = new_parser_from_sess_str(&parse_sess, raw);
    parser
        .parse_pat_allow_top_guard(
            None,
            rustc_parse::parser::RecoverComma::No,
            rustc_parse::parser::RecoverColon::No,
            rustc_parse::parser::CommaRecoveryMode::LikelyTuple,
        )
        .unwrap()
        .into_inner()
}

#[macro_export]
macro_rules! pat {
    ($($arg:tt)*) => {{
        parse_pat(format!($($arg)*))
    }};
}

fn collect_rs_files(entry: &PathBuf) -> Vec<PathBuf> {
    let dir = entry.parent().unwrap();
    walkdir::WalkDir::new(dir)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|entry| {
            entry.file_type().is_file() && entry.path().extension().map_or(false, |ext| ext == "rs")
        })
        .map(|entry| entry.into_path())
        .collect()
}

pub fn format_project(file: PathBuf) {
    let config = make_config(path_to_input(&file));
    run_compiler(config, |_| {
        let parse_sess = new_silent_parse_sess();

        for path in collect_rs_files(&file) {
            println!("Formatting file: {}", path.display());
            let src = std::fs::read_to_string(&path).unwrap();
            let mut parser = rustc_parse::new_parser_from_source_str(
                &parse_sess,
                FileName::Real(RealFileName::LocalPath(path.clone())),
                src,
            )
            .unwrap();
            let krate = parser.parse_crate_mod().unwrap();
            print!("Krate: {}", pprust::crate_to_string_for_macros(&krate));
            std::fs::write(path, pprust::crate_to_string_for_macros(&krate)).unwrap();
        }
    })
    .unwrap();
}
