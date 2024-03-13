use std::collections::HashSet;

use rustc_middle::{
    mir::{BasicBlock, Local, Location},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use super::*;
use crate::compile_util;

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    let input = compile_util::str_to_input(code);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, f).unwrap();
}

fn find(name: &str, tcx: TyCtxt<'_>) -> LocalDefId {
    let hir = tcx.hir();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        if item.ident.name.as_str() == name {
            return item_id.owner_id.def_id;
        }
    }
    panic!("{}", name)
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
        let def_id = find(name, tcx);
        f(res, def_id, tcx);
    });
}

fn analyze_fn<F>(code: &str, f: F)
where F: FnOnce(AnalysisResults, LocalDefId, TyCtxt<'_>) + Send {
    analyze_fn_with("", "", code, f);
}

fn ro(f: LocalDefId, i: usize) -> Loc {
    Loc::new_root(LocRoot::Local(f, Local::from_usize(i)))
}

fn gl(f: LocalDefId) -> Loc {
    Loc::new_root(LocRoot::Global(f))
}

fn al(f: LocalDefId, block: usize, statement_index: usize) -> Loc {
    let block = BasicBlock::from_usize(block);
    Loc::new_root(LocRoot::Alloc(
        f,
        Location {
            block,
            statement_index,
        },
    ))
}

fn lo<I: IntoIterator<Item = usize>>(f: LocalDefId, i: usize, proj: I) -> Loc {
    Loc::new(
        LocRoot::Local(f, Local::from_usize(i)),
        proj.into_iter().collect(),
    )
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
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_eq_after() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _2 = _3
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        z = y;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_eq_before() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = _2
    // _3 = move _4
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // _2 = move _5
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
        z = y;
        y = &mut x;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_eq_before_after() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _5 = _3
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _3 = move _6
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut x;
        let mut w: *mut libc::c_int = z;
        z = &mut y;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1), ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1), ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_eq_subset() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _6 = &mut _2
    // _5 = &raw mut (*_6)
    // _5 = _3
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut x;
        let mut w: *mut libc::c_int = &mut y;
        w = z;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1), ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_eq_propagate() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _3 = _2
    // _4 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = _3
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // _2 = move _5
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut libc::c_int = y;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        w = z;
        y = &mut x;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_eq_deref_after() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _5 = &mut _2
    // _4 = &raw mut (*_5)
    // _6 = (*_4)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut *mut libc::c_int = &mut y;
        let mut w: *mut libc::c_int = *z;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_eq_deref_before() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = const 0_usize as *mut *mut i32 (PointerFromExposedAddress)
    // _5 = (*_4)
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _4 = move _6
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut *mut libc::c_int = 0 as *mut *mut libc::c_int;
        let mut w: *mut libc::c_int = *z;
        z = &mut y;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_eq_deref_subset() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _6 = &mut _3
    // _5 = &raw mut (*_6)
    // _8 = &mut _2
    // _7 = &raw mut (*_8)
    // _9 = (*_5)
    // _7 = move _9
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut x;
        let mut w: *mut *mut libc::c_int = &mut z;
        let mut v: *mut libc::c_int = &mut y;
        v = *w;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 1), ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 8)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 9)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_eq_deref_propagate() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _5 = &mut _2
    // _4 = &raw mut (*_5)
    // _6 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _7 = _6
    // _8 = (*_4)
    // _6 = move _8
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut *mut libc::c_int = &mut y;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut v: *mut libc::c_int = w;
        w = *z;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 8)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_deref_eq_after() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = &mut _2
    // _3 = &raw mut (*_4)
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // (*_3) = move _5
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut *mut libc::c_int = &mut y;
        *z = &mut x;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_deref_eq_before() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _3 = const 0_usize as *mut *mut i32 (PointerFromExposedAddress)
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // (*_3) = move _4
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _3 = move _6
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut *mut libc::c_int = 0 as *mut *mut libc::c_int;
        *z = &mut x;
        z = &mut y;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_deref_eq_subset() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _6 = &mut _3
    // _5 = &raw mut (*_6)
    // _8 = &mut _2
    // _7 = &raw mut (*_8)
    // (*_5) = move _7
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut x;
        let mut w: *mut *mut libc::c_int = &mut z;
        *w = &mut y;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1), ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 8)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_deref_eq_propagate() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = &mut _2
    // _3 = &raw mut (*_4)
    // _5 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _6 = _2
    // _5 = move _6
    // _8 = &mut _1
    // _7 = &raw mut (*_8)
    // (*_3) = move _7
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut *mut libc::c_int = &mut y;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        w = y;
        *z = &mut x;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 8)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_array_aggregate() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _3 = [move _4, move _6]
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut p: [*mut libc::c_int; 2] = [&mut x, &mut y];
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&lo(f, 3, [0])), Some(&set([ro(f, 1), ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_array_eq_ref() {
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _1 = [move _2; 2]
    // _3 = const 0_i32
    // _4 = const 0_i32
    // _6 = &mut _3
    // _5 = &raw mut (*_6)
    // _8 = const 0_i32
    // _7 = move _8 as usize (IntToInt)
    // _9 = const 2_usize
    // _10 = Lt(_7, _9)
    // _1[_7] = move _5
    // _12 = &mut _4
    // _11 = &raw mut (*_12)
    // _14 = const 1_i32
    // _13 = move _14 as usize (IntToInt)
    // _15 = const 2_usize
    // _16 = Lt(_13, _15)
    // _1[_13] = move _11
    analyze_fn(
        "
        let mut p: [*mut libc::c_int; 2] = [0 as *mut libc::c_int; 2];
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        p[0 as libc::c_int as usize] = &mut x;
        p[1 as libc::c_int as usize] = &mut y;
        ",
        |res, f, _| {
            assert_eq!(res.get(&lo(f, 1, [0])), Some(&set([ro(f, 3), ro(f, 4)])));
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&ro(f, 3)), None);
            assert_eq!(res.get(&ro(f, 4)), None);
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(f, 7)), None);
            assert_eq!(res.get(&ro(f, 8)), None);
            assert_eq!(res.get(&ro(f, 9)), None);
            assert_eq!(res.get(&ro(f, 10)), None);
            assert_eq!(res.get(&ro(f, 11)), Some(&set([ro(f, 4)])));
            assert_eq!(res.get(&ro(f, 12)), Some(&set([ro(f, 4)])));
            assert_eq!(res.get(&ro(f, 13)), None);
            assert_eq!(res.get(&ro(f, 14)), None);
            assert_eq!(res.get(&ro(f, 15)), None);
            assert_eq!(res.get(&ro(f, 16)), None);
        },
    );
}

#[test]
fn test_struct_aggregate() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _8 = const 0_i32
    // _3 = s { x: move _4, y: move _6, z: move _8 }
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
            pub z: libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: s = {
            let mut init = s {
                x: &mut x,
                y: &mut y,
                z: 0 as libc::c_int,
            };
            init
        };
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&ro(f, 3)), None);
            assert_eq!(res.get(&lo(f, 3, [0])), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&lo(f, 3, [1])), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&lo(f, 3, [2])), None);
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_struct_eq_ref() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _4 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _5 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _3 = s { x: move _4, y: move _5 }
    // _7 = &mut _1
    // _6 = &raw mut (*_7)
    // (_3.0: *mut i32) = move _6
    // _9 = &mut _2
    // _8 = &raw mut (*_9)
    // (_3.1: *mut i32) = move _8
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: s = s {
            x: 0 as *mut libc::c_int,
            y: 0 as *mut libc::c_int,
        };
        z.x = &mut x;
        z.y = &mut y;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&ro(f, 3)), None);
            assert_eq!(res.get(&lo(f, 3, [0])), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&lo(f, 3, [1])), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 4)), None);
            assert_eq!(res.get(&ro(f, 5)), None);
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 8)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 9)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_struct_eq() {
    // _1 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _2 = s { x: move _3 }
    // _6 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _5 = s { x: move _6 }
    // _5 = _2
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: s = {
            let mut init = s { x: &mut x };
            init
        };
        let mut z: s = s { x: 0 as *mut libc::c_int };
        z = y;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&lo(f, 2, [0])), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), None);
            assert_eq!(res.get(&lo(f, 5, [0])), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_struct_deref_eq_after() {
    // _1 = const 0_i32
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = s { x: move _3 }
    // _5 = &mut _2
    // _4 = &raw mut (*_5)
    // _7 = &mut _1
    // _6 = &raw mut (*_7)
    // ((*_4).0: *mut i32) = move _6
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: s = s { x: 0 as *mut libc::c_int };
        let mut z: *mut s = &mut y;
        (*z).x = &mut x;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&lo(f, 2, [0])), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), None);
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_struct_deref_eq_before() {
    // _1 = const 0_i32
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = s { x: move _3 }
    // _4 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // ((*_4).0: *mut i32) = move _5
    // _8 = &mut _2
    // _7 = &raw mut (*_8)
    // _4 = move _7
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: s = s { x: 0 as *mut libc::c_int };
        let mut z: *mut s = 0 as *mut s;
        (*z).x = &mut x;
        z = &mut y;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&lo(f, 2, [0])), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), None);
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 8)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_struct_eq_deref_after() {
    // _1 = const 0_i32
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _3 = s { x: move _4 }
    // _2 = _3
    // _7 = &mut _2
    // _6 = &raw mut (*_7)
    // _8 = ((*_6).0: *mut i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: s = {
            let mut init = s { x: &mut x };
            init
        };
        let mut z: *mut s = &mut y;
        let mut w: *mut libc::c_int = (*z).x;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&lo(f, 2, [0])), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), None);
            assert_eq!(res.get(&lo(f, 3, [0])), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 8)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_struct_eq_deref_before() {
    // _1 = const 0_i32
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _3 = s { x: move _4 }
    // _2 = _3
    // _6 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _7 = ((*_6).0: *mut i32)
    // _9 = &mut _2
    // _8 = &raw mut (*_9)
    // _6 = move _8
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: s = {
            let mut init = s { x: &mut x };
            init
        };
        let mut z: *mut s = 0 as *mut s;
        let mut w: *mut libc::c_int = (*z).x;
        z = &mut y;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&lo(f, 2, [0])), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), None);
            assert_eq!(res.get(&lo(f, 3, [0])), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 8)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 9)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_struct_field_ref() {
    // _1 = s { x: const 0_i32 }
    // _3 = &mut (_1.0: i32)
    // _2 = &raw mut (*_3)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "",
        "
        let mut x: s = s { x: 0 };
        let mut y: *mut libc::c_int = &mut x.x;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([lo(f, 1, [0])])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([lo(f, 1, [0])])));
        },
    );
}

#[test]
fn test_struct_field_deref_ref_after() {
    // _1 = s { x: const 0_i32 }
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _5 = &mut ((*_2).0: i32)
    // _4 = &raw mut (*_5)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "",
        "
        let mut x: s = s { x: 0 };
        let mut y: *mut s = &mut x;
        let mut z: *mut libc::c_int = &mut (*y).x;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([lo(f, 1, [0])])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([lo(f, 1, [0])])));
        },
    );
}

#[test]
fn test_struct_field_deref_ref_before() {
    // _1 = s { x: const 0_i32 }
    // _2 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _4 = &mut ((*_2).0: i32)
    // _3 = &raw mut (*_4)
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // _2 = move _5
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "",
        "
        let mut x: s = s { x: 0 };
        let mut y: *mut s = 0 as *mut s;
        let mut z: *mut libc::c_int = &mut (*y).x;
        y = &mut x;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([lo(f, 1, [0])])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([lo(f, 1, [0])])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_union_aggregate() {
    // _1 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _2 = u { x: move _3 }
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: *mut libc::c_int,
            pub y: *mut libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: u = u { y: &mut x };
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&lo(f, 2, [0])), None);
            assert_eq!(res.get(&lo(f, 2, [1])), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_copy_for_deref() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = &mut _2
    // _3 = &raw mut (*_4)
    // _6 = &mut _3
    // _5 = &raw mut (*_6)
    // _8 = &mut _1
    // _7 = &raw mut (*_8)
    // _9 = deref_copy (*_5)
    // (*_9) = move _7
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut *mut libc::c_int = &mut y;
        let mut w: *mut *mut *mut libc::c_int = &mut z;
        **w = &mut x;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 8)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 9)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_static() {
    // _3 = const {alloc1: *mut i32}
    // _2 = &mut (*_3)
    // _1 = &raw mut (*_2)
    analyze_fn_with(
        "
        pub static mut x: libc::c_int = 0;
        ",
        "",
        "
        let mut y: *mut libc::c_int = &mut x;
        ",
        |res, f, tcx| {
            let x = find("x", tcx);
            assert_eq!(res.get(&ro(f, 1)), Some(&set([gl(x)])));
            assert_eq!(res.get(&ro(f, 2)), Some(&set([gl(x)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([gl(x)])));
        },
    );
}

#[test]
fn test_byte_literal() {
    // _4 = const b"\x00"
    // _3 = &raw const (*_4)
    // _2 = move _3 as *const u8 (PointerCoercion(ArrayToPointer))
    // _1 = move _2 as *const i8 (PtrToPtr)
    analyze_fn(
        "
        let mut x: *const libc::c_char = b\"\\0\" as *const u8 as *const libc::c_char;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), Some(&set([al(f, 0, 0)])));
            assert_eq!(res.get(&ro(f, 2)), Some(&set([al(f, 0, 0)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([al(f, 0, 0)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([al(f, 0, 0)])));
        },
    );
}

#[test]
fn test_call() {
    // _2 = const 0_i32
    // _4 = &mut _2
    // _3 = &raw mut (*_4)
    // _1 = move _3
    // _0 = _1
    //
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = g(_2)
    // _5 = const 0_i32
    // _7 = &mut _5
    // _6 = &raw mut (*_7)
    // _4 = move _6
    analyze_fn_with(
        "
        pub unsafe extern \"C\" fn g(mut x: *mut libc::c_int) -> *mut libc::c_int {
            let mut y: libc::c_int = 0 as libc::c_int;
            x = &mut y;
            return x;
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut libc::c_int = g(y);
        let mut w: libc::c_int = 0 as libc::c_int;
        z = &mut w;
        ",
        |res, f, tcx| {
            let g = find("g", tcx);
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(
                res.get(&ro(f, 4)),
                Some(&set([ro(f, 1), ro(f, 5), ro(g, 2)]))
            );
            assert_eq!(res.get(&ro(f, 5)), None);
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 5)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 5)])));
            assert_eq!(res.get(&ro(g, 0)), Some(&set([ro(f, 1), ro(g, 2)])));
            assert_eq!(res.get(&ro(g, 1)), Some(&set([ro(f, 1), ro(g, 2)])));
            assert_eq!(res.get(&ro(g, 2)), None);
            assert_eq!(res.get(&ro(g, 3)), Some(&set([ro(g, 2)])));
            assert_eq!(res.get(&ro(g, 4)), Some(&set([ro(g, 2)])));
        },
    );
}

#[test]
fn test_fn_ptr_some() {
    // _0 = _1
    //
    // _2 = g as unsafe extern "C" fn(*mut i32) -> *mut i32 (PointerCoercion(ReifyFnPointer))
    // _1 = std::option::Option::<unsafe extern "C" fn(*mut i32) -> *mut i32>::Some(move _2)
    analyze_fn_with(
        "
        pub unsafe extern \"C\" fn g(mut x: *mut libc::c_int) -> *mut libc::c_int {
            return x;
        }
        ",
        "",
        "
        let mut x: Option::<unsafe extern \"C\" fn(*mut libc::c_int) -> *mut libc::c_int> = Some(
            g as unsafe extern \"C\" fn(*mut libc::c_int) -> *mut libc::c_int,
        );
        ",
        |res, f, tcx| {
            let g = find("g", tcx);
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&lo(f, 1, [0])), Some(&set([gl(g)])));
            assert_eq!(res.get(&ro(f, 2)), Some(&set([gl(g)])));
        },
    );
}

#[test]
fn test_fn_ptr_after() {
    // _0 = _1
    //
    // _2 = g as unsafe extern "C" fn(*mut i32) -> *mut i32 (PointerCoercion(ReifyFnPointer))
    // _1 = std::option::Option::<unsafe extern "C" fn(*mut i32) -> *mut i32>::Some(move _2)
    // _3 = const 0_i32
    // _5 = &mut _3
    // _4 = &raw mut (*_5)
    // _7 = std::option::Option::<unsafe extern "C" fn(*mut i32) -> *mut i32>::unwrap(_1)
    // _6 = move _7(_4)
    analyze_fn_with(
        "
        pub unsafe extern \"C\" fn g(mut x: *mut libc::c_int) -> *mut libc::c_int {
            return x;
        }
        ",
        "",
        "
        let mut x: Option::<unsafe extern \"C\" fn(*mut libc::c_int) -> *mut libc::c_int> = Some(
            g as unsafe extern \"C\" fn(*mut libc::c_int) -> *mut libc::c_int,
        );
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut y;
        let mut w: *mut libc::c_int = x.unwrap()(z);
        ",
        |res, f, tcx| {
            let g = find("g", tcx);
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&lo(f, 1, [0])), Some(&set([gl(g)])));
            assert_eq!(res.get(&ro(f, 2)), Some(&set([gl(g)])));
            assert_eq!(res.get(&ro(f, 3)), None);
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([gl(g)])));
            assert_eq!(res.get(&ro(g, 0)), Some(&set([ro(f, 3)])));
            assert_eq!(res.get(&ro(g, 1)), Some(&set([ro(f, 3)])));
        },
    );
}

#[test]
fn test_fn_ptr_before() {
    // _0 = _1
    //
    // _1 = std::option::Option::<unsafe extern "C" fn(*mut i32) -> *mut i32>::None
    // _2 = const 0_i32
    // _4 = &mut _2
    // _3 = &raw mut (*_4)
    // _7 = _1
    // _6 = std::option::Option::<unsafe extern "C" fn(*mut i32) -> *mut i32>::unwrap(move _7)
    // _5 = move _6(_3)
    // _9 = g as unsafe extern "C" fn(*mut i32) -> *mut i32 (PointerCoercion(ReifyFnPointer))
    // _8 = std::option::Option::<unsafe extern "C" fn(*mut i32) -> *mut i32>::Some(move _9)
    // _1 = move _8
    analyze_fn_with(
        "
        pub unsafe extern \"C\" fn g(mut x: *mut libc::c_int) -> *mut libc::c_int {
            return x;
        }
        ",
        "",
        "
        let mut x: Option::<unsafe extern \"C\" fn(*mut libc::c_int) -> *mut libc::c_int> = None;
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut y;
        let mut w: *mut libc::c_int = x.unwrap()(z);
        x = Some(g as unsafe extern \"C\" fn(*mut libc::c_int) -> *mut libc::c_int);
        ",
        |res, f, tcx| {
            let g = find("g", tcx);
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&lo(f, 1, [0])), Some(&set([gl(g)])));
            assert_eq!(res.get(&ro(f, 2)), None);
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([gl(g)])));
            assert_eq!(res.get(&ro(f, 7)), None);
            assert_eq!(res.get(&lo(f, 7, [0])), Some(&set([gl(g)])));
            assert_eq!(res.get(&ro(f, 8)), None);
            assert_eq!(res.get(&lo(f, 8, [0])), Some(&set([gl(g)])));
            assert_eq!(res.get(&ro(f, 9)), Some(&set([gl(g)])));
            assert_eq!(res.get(&ro(g, 0)), Some(&set([ro(f, 2)])));
            assert_eq!(res.get(&ro(g, 1)), Some(&set([ro(f, 2)])));
        },
    );
}

#[test]
fn test_array_as_mut_ptr() {
    // _1 = [const 0_i32; 2]
    // _4 = &mut _1
    // _3 = move _4 as &mut [i32] (PointerCoercion(Unsize))
    // _2 = core::slice::<impl [i32]>::as_mut_ptr(move _3)
    analyze_fn(
        "
        let mut x: [libc::c_int; 2] = [0; 2];
        let mut y: *mut libc::c_int = x.as_mut_ptr();
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([lo(f, 1, [0])])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([ro(f, 1)])));
        },
    );
}

#[test]
fn test_array_offset() {
    // _1 = [const 0_i32; 2]
    // _7 = &mut _1
    // _6 = move _7 as &mut [i32] (PointerCoercion(Unsize))
    // _5 = core::slice::<impl [i32]>::as_mut_ptr(move _6) -> [return: bb1, unwind continue]
    // _9 = const 1_i32
    // _8 = move _9 as isize (IntToInt)
    // _4 = std::ptr::mut_ptr::<impl *mut i32>::offset(move _5, move _8) -> [return: bb2, unwind continue]
    // _3 = &mut (*_4)
    // _2 = &raw mut (*_3)
    analyze_fn(
        "
        let mut x: [libc::c_int; 2] = [0; 2];
        let mut y: *mut libc::c_int = &mut *x.as_mut_ptr().offset(1 as libc::c_int as isize)
            as *mut libc::c_int;
        ",
        |res, f, _| {
            assert_eq!(res.get(&ro(f, 1)), None);
            assert_eq!(res.get(&ro(f, 2)), Some(&set([lo(f, 1, [0])])));
            assert_eq!(res.get(&ro(f, 3)), Some(&set([lo(f, 1, [0])])));
            assert_eq!(res.get(&ro(f, 4)), Some(&set([lo(f, 1, [0])])));
            assert_eq!(res.get(&ro(f, 5)), Some(&set([lo(f, 1, [0])])));
            assert_eq!(res.get(&ro(f, 6)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 7)), Some(&set([ro(f, 1)])));
            assert_eq!(res.get(&ro(f, 8)), None);
            assert_eq!(res.get(&ro(f, 9)), None);
        },
    );
}
