use std::collections::HashSet;

use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;

use super::*;
use crate::compile_util;

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    let input = compile_util::str_to_input(code);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, f).unwrap();
}

fn find_fn(name: &str, tcx: TyCtxt<'_>) -> LocalDefId {
    let hir = tcx.hir();
    hir.items()
        .find_map(|item_id| {
            let item = hir.item(item_id);
            if item.ident.name.as_str() != name {
                return None;
            }
            Some(item_id.owner_id.def_id)
        })
        .unwrap()
}

fn analyze_fn_with<F>(types: &str, params: &str, code: &str, f: F)
where F: FnOnce(AnalysisResults, LocalDefId, TyCtxt<'_>) + Send {
    let name = "foo";
    let code = format!(
        "
        extern crate libc;
        {}
        unsafe extern \"C\" fn {}({}) {{
            {}
        }}
    ",
        types, name, params, code
    );
    run_compiler(&code, |tcx| {
        let res = analyze(tcx);
        let def_id = find_fn(name, tcx);
        f(res, def_id, tcx);
    });
}

fn analyze_fn<F>(code: &str, f: F)
where F: FnOnce(AnalysisResults, LocalDefId, TyCtxt<'_>) + Send {
    analyze_fn_with("", "", code, f);
}

fn root(f: LocalDefId, i: usize) -> Loc {
    Loc::new_root(LocRoot::Local(f, Local::from_usize(i)))
}

fn set<T: Eq + std::hash::Hash, I: IntoIterator<Item = T>>(i: I) -> HashSet<T> {
    HashSet::from_iter(i)
}

#[test]
fn test_eq_ref() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        ",
        |res, f, _| {
            assert_eq!(res.get(&root(f, 1)), None);
            assert_eq!(res.get(&root(f, 2)), Some(&set([root(f, 1)])));
            assert_eq!(res.get(&root(f, 3)), Some(&set([root(f, 1)])));
        },
    );
}

#[test]
fn test_eq_ref_join() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _6 = &mut _2
    // _5 = &raw mut (*_6)
    // _8 = &mut _2
    // _7 = &raw mut (*_8)
    // _3 = move _7
    analyze_fn(
        "
        let mut x1: libc::c_int = 0 as libc::c_int;
        let mut x2: libc::c_int = 0 as libc::c_int;
        let mut y1: *mut libc::c_int = &mut x1;
        let mut y2: *mut libc::c_int = &mut x2;
        y1 = &mut x2;
        ",
        |res, f, _| {
            assert_eq!(res.get(&root(f, 1)), None);
            assert_eq!(res.get(&root(f, 2)), None);
            assert_eq!(res.get(&root(f, 3)), Some(&set([root(f, 1), root(f, 2)])));
            assert_eq!(res.get(&root(f, 4)), Some(&set([root(f, 1)])));
            assert_eq!(res.get(&root(f, 5)), Some(&set([root(f, 2)])));
            assert_eq!(res.get(&root(f, 6)), Some(&set([root(f, 2)])));
            assert_eq!(res.get(&root(f, 7)), Some(&set([root(f, 2)])));
            assert_eq!(res.get(&root(f, 8)), Some(&set([root(f, 2)])));
        },
    );
}

#[test]
fn test_eq_ref_join_2() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _6 = &mut _2
    // _5 = &raw mut (*_6)
    // _8 = &mut _3
    // _7 = &raw mut (*_8)
    // _10 = &mut _5
    // _9 = &raw mut (*_10)
    // _12 = &mut _5
    // _11 = &raw mut (*_12)
    // _7 = move _11
    analyze_fn(
        "
        let mut x1: libc::c_int = 0 as libc::c_int;
        let mut x2: libc::c_int = 0 as libc::c_int;
        let mut y1: *mut libc::c_int = &mut x1;
        let mut y2: *mut libc::c_int = &mut x2;
        let mut z1: *mut *mut libc::c_int = &mut y1;
        let mut z2: *mut *mut libc::c_int = &mut y2;
        z1 = &mut y2;
        ",
        |res, f, _| {
            assert_eq!(res.get(&root(f, 1)), None);
            assert_eq!(res.get(&root(f, 2)), None);
            assert_eq!(res.get(&root(f, 3)), Some(&set([root(f, 1)])));
            assert_eq!(res.get(&root(f, 4)), Some(&set([root(f, 1)])));
            assert_eq!(res.get(&root(f, 5)), Some(&set([root(f, 2)])));
            assert_eq!(res.get(&root(f, 6)), Some(&set([root(f, 2)])));
            assert_eq!(res.get(&root(f, 7)), Some(&set([root(f, 3), root(f, 5)])));
            assert_eq!(res.get(&root(f, 8)), Some(&set([root(f, 3)])));
            assert_eq!(res.get(&root(f, 9)), Some(&set([root(f, 5)])));
            assert_eq!(res.get(&root(f, 10)), Some(&set([root(f, 5)])));
            assert_eq!(res.get(&root(f, 11)), Some(&set([root(f, 5)])));
            assert_eq!(res.get(&root(f, 12)), Some(&set([root(f, 5)])));
        },
    );
}
