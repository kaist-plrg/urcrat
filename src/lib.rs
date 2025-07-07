#![warn(absolute_paths_not_starting_with_crate)]
#![warn(elided_lifetimes_in_paths)]
#![warn(explicit_outlives_requirements)]
#![warn(ffi_unwind_calls)]
#![warn(keyword_idents)]
#![warn(let_underscore_drop)]
#![warn(macro_use_extern_crate)]
#![warn(meta_variable_misuse)]
#![warn(missing_abi)]
#![warn(missing_copy_implementations)]
#![warn(missing_debug_implementations)]
#![warn(non_ascii_idents)]
#![warn(private_bounds)]
#![warn(private_interfaces)]
#![warn(rust_2021_incompatible_closure_captures)]
#![warn(rust_2021_incompatible_or_patterns)]
#![warn(rust_2021_prefixes_incompatible_syntax)]
#![warn(rust_2021_prelude_collisions)]
#![warn(single_use_lifetimes)]
#![warn(trivial_casts)]
#![warn(trivial_numeric_casts)]
#![warn(unreachable_pub)]
#![warn(unsafe_op_in_unsafe_fn)]
#![warn(unused_extern_crates)]
#![warn(unused_import_braces)]
#![warn(unused_lifetimes)]
#![warn(unused_macro_rules)]
#![warn(unused_qualifications)]
#![warn(dead_code)]
#![warn(variant_size_differences)]
#![feature(rustc_private)]
#![feature(iter_intersperse)]
#![feature(box_into_inner)]
#![feature(box_patterns)]
#![feature(macro_metavar_expr)]
#![feature(extract_if)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_feature;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;
extern crate smallvec;
extern crate thin_vec;

pub mod alloc_finder;
#[macro_use]
pub mod astutil;
pub mod bitset;
pub mod compile_util;
pub mod disjoint_set;
pub mod graph;
pub mod may_analysis;
pub mod must_analysis;
pub mod tag_analysis;
pub mod ty_finder;
pub mod ty_shape;
pub mod unsafety;
