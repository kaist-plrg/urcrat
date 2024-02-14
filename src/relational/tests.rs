use std::collections::HashMap;

use rustc_middle::{
    mir::{Location, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use super::*;
use crate::*;

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

fn find_return(def_id: LocalDefId, tcx: TyCtxt<'_>) -> Location {
    let body = tcx.optimized_mir(def_id);
    let (bb, bbd) = body
        .basic_blocks
        .iter_enumerated()
        .find(|(_, bbd)| bbd.terminator().kind == TerminatorKind::Return)
        .unwrap();
    Location {
        block: bb,
        statement_index: bbd.statements.len(),
    }
}

fn analyze_fn_with<F>(types: &str, params: &str, code: &str, f: F)
where F: FnOnce(Graph, AnalysisResults, TyCtxt<'_>) + Send {
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
        let loc = find_return(def_id, tcx);
        let state = res.functions[&def_id][&loc].clone();
        let AbsMem::Mem(graph) = state else { panic!() };
        f(graph, res, tcx);
    });
}

fn analyze_fn<F>(code: &str, f: F)
where F: FnOnce(Graph, AnalysisResults, TyCtxt<'_>) + Send {
    analyze_fn_with("", "", code, f);
}

fn get_nodes<'a>(g: &'a Graph, i: impl Iterator<Item = usize>) -> HashMap<usize, &'a Node> {
    i.map(|n| (n, g.get_local_node(n))).collect()
}

fn get_ids(g: &Graph, i: impl Iterator<Item = usize>) -> HashMap<usize, usize> {
    i.map(|n| (n, g.get_local_id(n))).collect()
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
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            let i = get_ids(&g, 1..=3);
            assert_eq!(n[&2].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&3].as_ptr(), &AbsLoc::new_root(i[&1]));

            assert_eq!(g.get_local_as_int(1), Some(0));
        },
    );
}

#[test]
fn test_eq() {
    // _1 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = _1
    // _4 = &mut _2
    // _3 = &raw mut (*_4)
    analyze_fn(
        "
        let mut x: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut y: *mut libc::c_int = x;
        let mut z: *mut *mut libc::c_int = &mut y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            let i = get_ids(&g, 1..=4);
            assert_eq!(n[&1].as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&3].as_ptr(), &AbsLoc::new_root(i[&2]));
            assert_eq!(n[&4].as_ptr(), &AbsLoc::new_root(i[&2]));
        },
    );
}

#[test]
fn test_eq_deref() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = (*_2)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: libc::c_int = *y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            let i = get_ids(&g, 1..=4);
            assert_eq!(n[&1].as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&2].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&3].as_ptr(), &AbsLoc::new_root(i[&1]));

            assert_eq!(g.get_local_as_int(1), Some(0));
        },
    );
}

#[test]
fn test_deref_eq() {
    // _1 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = const 0_i32
    // (*_1) = _2
    analyze_fn(
        "
        let mut x: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        *x = y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=2);
            let n11 = &g.nodes[n[&1].as_ptr().root()];
            assert_eq!(n11.as_ptr(), n[&2].as_ptr());

            assert_eq!(g.get_local_as_int(2), Some(0));
        },
    );
}

#[test]
fn test_eq_struct() {
    // _2 = const 0_i32
    // _3 = const 1_i32
    // _1 = s { x: move _2, y: move _3 }
    // _4 = (_1.0: i32)
    // _5 = (_1.1: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut x: s = {
            let mut init = s {
                x: 0 as libc::c_int,
                y: 1 as libc::c_int,
            };
            init
        };
        let mut y: s = x;
        let mut z: libc::c_int = y.x;
        let mut w: libc::c_int = y.y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=5);
            assert_eq!(n[&1].field(0).as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&1].field(1).as_ptr(), n[&3].as_ptr());
            assert_eq!(n[&2].as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&3].as_ptr(), n[&5].as_ptr());
        },
    );
}

#[test]
fn test_eq_struct_2() {
    // _3 = const 0_i32
    // _4 = const 1_i32
    // _2 = s { x: move _3, y: move _4 }
    // _6 = const 2_i32
    // _7 = const 3_i32
    // _5 = s { x: move _6, y: move _7 }
    // _1 = t { x: _2, y: _5 }
    // _8 = (_1.0: s)
    // _9 = (_1.1: s)
    // _10 = (_8.0: i32)
    // _11 = (_9.1: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: s,
            pub y: s,
        }
        ",
        "",
        "
        let mut x: t = {
            let mut init = t {
                x: {
                    let mut init = s {
                        x: 0 as libc::c_int,
                        y: 1 as libc::c_int,
                    };
                    init
                },
                y: {
                    let mut init = s {
                        x: 2 as libc::c_int,
                        y: 3 as libc::c_int,
                    };
                    init
                },
            };
            init
        };
        let mut y: s = x.x;
        let mut z: s = x.y;
        let mut w: libc::c_int = y.x;
        let mut v: libc::c_int = z.y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=11);
            assert_eq!(n[&2].field(0).as_ptr(), n[&3].as_ptr());
            assert_eq!(n[&2].field(1).as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&5].field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&5].field(1).as_ptr(), n[&7].as_ptr());
            assert_eq!(n[&1].field(0).field(0).as_ptr(), n[&3].as_ptr());
            assert_eq!(n[&1].field(0).field(1).as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&1].field(1).field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&1].field(1).field(1).as_ptr(), n[&7].as_ptr());
            assert_eq!(n[&8].field(0).as_ptr(), n[&3].as_ptr());
            assert_eq!(n[&8].field(1).as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&9].field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&9].field(1).as_ptr(), n[&7].as_ptr());
            assert_eq!(n[&10].as_ptr(), n[&3].as_ptr());
            assert_eq!(n[&11].as_ptr(), n[&7].as_ptr());
        },
    );
}

#[test]
fn test_eq_ref_struct() {
    // _3 = const 0_i32
    // _4 = const 2_i32
    // _2 = s { x: move _3, y: move _4 }
    // _1 = _2
    // _6 = &mut (_1.0: i32)
    // _5 = &raw mut (*_6)
    // _7 = const 1_i32
    // (*_5) = move _7
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut x: s = {
            let mut init = s {
                x: 0 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut y: *mut libc::c_int = &mut x.x;
        *y = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=7);
            let i = get_ids(&g, 1..=7);

            assert_eq!(n[&2].field(0).as_ptr(), n[&3].as_ptr());

            assert_eq!(n[&1].field(1).as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&2].field(1).as_ptr(), n[&4].as_ptr());

            assert_eq!(n[&1].field(0).as_ptr(), n[&7].as_ptr());

            assert_eq!(n[&5].as_ptr(), &AbsLoc::new(i[&1], vec![AccElem::Int(0)]));
            assert_eq!(n[&6].as_ptr(), &AbsLoc::new(i[&1], vec![AccElem::Int(0)]));
        },
    );
}

#[test]
fn test_eq_deref_struct() {
    // _3 = const 1_i32
    // _4 = const 2_i32
    // _2 = s { x: move _3, y: move _4 }
    // _1 = _2
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // _7 = ((*_5).0: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut x: s = {
            let mut init = s {
                x: 1 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut y: *mut s = &mut x;
        let mut z: libc::c_int = (*y).x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=7);
            let i = get_ids(&g, 1..=7);

            assert_eq!(n[&1].field(0).as_ptr(), n[&3].as_ptr());
            assert_eq!(n[&2].field(0).as_ptr(), n[&3].as_ptr());
            assert_eq!(n[&7].as_ptr(), n[&3].as_ptr());

            assert_eq!(n[&1].field(1).as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&2].field(1).as_ptr(), n[&4].as_ptr());

            assert_eq!(n[&5].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&6].as_ptr(), &AbsLoc::new_root(i[&1]));
        },
    );
}

#[test]
fn test_deref_struct_eq() {
    // _3 = const 0_i32
    // _4 = const 2_i32
    // _2 = s { x: move _3, y: move _4 }
    // _1 = _2
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // _7 = const 1_i32
    // ((*_5).0: i32) = move _7
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut x: s = {
            let mut init = s {
                x: 0 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut y: *mut s = &mut x;
        (*y).x = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=7);
            let i = get_ids(&g, 1..=7);

            assert_eq!(n[&2].field(0).as_ptr(), n[&3].as_ptr());

            assert_eq!(n[&1].field(1).as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&2].field(1).as_ptr(), n[&4].as_ptr());

            assert_eq!(n[&1].field(0).as_ptr(), n[&7].as_ptr());

            assert_eq!(n[&5].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&6].as_ptr(), &AbsLoc::new_root(i[&1]));
        },
    );
}

#[test]
fn test_eq_ref_deref() {
    // _3 = const 0_i32
    // _4 = const 2_i32
    // _2 = s { x: move _3, y: move _4 }
    // _1 = _2
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // _8 = &mut ((*_5).0: i32)
    // _7 = &raw mut (*_8)
    // _9 = const 1_i32
    // (*_7) = move _9
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut x: s = {
            let mut init = s {
                x: 0 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut y: *mut s = &mut x;
        let mut z: *mut libc::c_int = &mut (*y).x;
        *z = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=9);
            let i = get_ids(&g, 1..=9);

            assert_eq!(n[&2].field(0).as_ptr(), n[&3].as_ptr());

            assert_eq!(n[&1].field(1).as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&2].field(1).as_ptr(), n[&4].as_ptr());

            assert_eq!(n[&1].field(0).as_ptr(), n[&9].as_ptr());

            assert_eq!(n[&5].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&6].as_ptr(), &AbsLoc::new_root(i[&1]));

            assert_eq!(n[&7].as_ptr(), &AbsLoc::new(i[&1], vec![AccElem::Int(0)]));
            assert_eq!(n[&8].as_ptr(), &AbsLoc::new(i[&1], vec![AccElem::Int(0)]));
        },
    );
}

#[test]
fn test_eq_union() {
    // _1 = const 0_i32
    // _2 = u { x: _1 }
    // _3 = (_2.1: i32)
    // _5 = &mut _3
    // _4 = &raw mut (*_5)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "",
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: u = u { y: x };
        let mut z: libc::c_int = y.y;
        let mut w: *mut libc::c_int = &mut z;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            assert_eq!(n[&2].field(1).as_ptr(), n[&1].as_ptr());
            assert_eq!(n[&3].as_ptr(), n[&1].as_ptr());
        },
    );
}

#[test]
fn test_eq_array() {
    // _1 = [const 0_i32; 2]
    // _4 = const 0_i32
    // _3 = move _4 as usize (IntToInt)
    // _5 = const 2_usize
    // _6 = Lt(_3, _5)
    // _2 = _1[_3]
    // _9 = const 1_i32
    // _8 = move _9 as usize (IntToInt)
    // _10 = const 2_usize
    // _11 = Lt(_8, _10)
    // _7 = _1[_8]
    analyze_fn(
        "
        let mut x: [libc::c_int; 2] = [0; 2];
        let mut y: libc::c_int = x[0 as libc::c_int as usize];
        let mut z: libc::c_int = x[1 as libc::c_int as usize];
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=11);
            assert_eq!(n[&1].field(0).as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&1].field(1).as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&3].as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&4].as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&7].as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&10].as_ptr(), n[&5].as_ptr());
            assert_eq!(n[&8].as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&9].as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&11].as_ptr(), n[&6].as_ptr());

            assert_eq!(g.get_local_as_int(2), Some(0));
            assert_eq!(g.get_local_as_int(5), Some(2));
            assert_eq!(g.get_local_as_int(6), Some(1));
        },
    );
}

#[test]
fn test_eq_array_symbolic() {
    // _2 = [const 0_i32; 1]
    // _3 = const 1_i32
    // _4 = _1 as usize (IntToInt)
    // _5 = const 1_usize
    // _6 = Lt(_4, _5)
    // _2[_4] = move _3
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: [libc::c_int; 1] = [0; 1];
        y[x as usize] = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=6);
            assert_eq!(n[&1].as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&2].symbolic(&[1, 4]).unwrap().as_ptr(), n[&5].as_ptr());
            assert_eq!(n[&3].as_ptr(), n[&5].as_ptr());

            assert_eq!(g.get_local_as_int(3), Some(1));
            assert_eq!(g.get_local_as_int(6), None);
        },
    );
}

#[test]
fn test_eq_array_symbolic_struct() {
    // _2 = ((*_1).0: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "mut x: *mut s",
        "
        let mut y: libc::c_int = (*x).x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=2);
            let n11 = &g.nodes[n[&1].as_ptr().root()];
            assert_eq!(n11.field(0).as_ptr(), n[&2].as_ptr());
        },
    );
}

#[test]
fn test_eq_array_symbolic_invalidated() {
    // _2 = [const 0_i32; 1]
    // _3 = const 1_i32
    // _5 = _1
    // _4 = move _5 as usize (IntToInt)
    // _6 = const 1_usize
    // _7 = Lt(_4, _6)
    // _2[_4] = move _3
    // _8 = const 2_i32
    // _1 = move _8
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: [libc::c_int; 1] = [0; 1];
        y[x as usize] = 1 as libc::c_int;
        x = 2 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=8);
            assert_eq!(n[&1].as_ptr(), n[&8].as_ptr());
            assert_eq!(n[&2].symbolic(&[4, 5]).unwrap().as_ptr(), n[&3].as_ptr());
            assert_eq!(n[&4].as_ptr(), n[&5].as_ptr());

            assert_eq!(g.get_local_as_int(1), Some(2));
            assert_eq!(g.get_local_as_int(3), Some(1));
            assert_eq!(g.get_local_as_int(4), None);
            assert_eq!(g.get_local_as_int(6), Some(1));
            assert_eq!(g.get_local_as_int(7), None);
        },
    );
}

#[test]
fn test_join_int() {
    // _2 = const 0_i32
    // _3 = const 0_i32
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _4 = const 1_i32
    // _2 = move _4
    // _5 = const 1_i32
    // _3 = move _5
    // goto -> bb2
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = 0 as libc::c_int;
        if x != 0 {
            y = 1 as libc::c_int;
            z = 1 as libc::c_int;
        }
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=3);
            assert_eq!(n[&2].as_ptr(), n[&3].as_ptr());
            assert_eq!(g.get_local_as_int(2), None);
        },
    );
}

#[test]
fn test_filter() {
    // _2 = const 1_i32
    // _3 = const 2_i32
    // _4 = const 3_i32
    // switchInt(_1) -> [1: bb2, 2: bb3, otherwise: bb1]
    // _4 = _1
    // goto -> bb4
    // _2 = _1
    // goto -> bb4
    // _3 = _1
    // goto -> bb4
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 1 as libc::c_int;
        let mut z: libc::c_int = 2 as libc::c_int;
        let mut w: libc::c_int = 3 as libc::c_int;
        match x {
            1 => y = x,
            2 => z = x,
            _ => w = x,
        };
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(2), Some(1));
            assert_eq!(g.get_local_as_int(3), Some(2));
            assert_eq!(g.get_local_as_int(4), None);
        },
    );
}

#[test]
fn test_filter_if_eq() {
    // _2 = const 0_i32
    // _4 = const 0_i32
    // _3 = Eq(_1, move _4)
    // switchInt(move _3) -> [0: bb2, otherwise: bb1]
    // _2 = _1
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        if x == 0 as libc::c_int {
            y = x;
        }
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(2), Some(0));
        },
    );
}

#[test]
fn test_filter_if_ne() {
    // _2 = const 1_i32
    // _4 = const 0_i32
    // _3 = Ne(_1, move _4)
    // switchInt(move _3) -> [0: bb2, otherwise: bb1]
    // _5 = const 0_i32
    // _2 = move _5
    // _2 = _1
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 1 as libc::c_int;
        if x != 0 as libc::c_int {
            y = 0 as libc::c_int;
        } else {
            y = x;
        };
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(2), Some(0));
        },
    );
}

#[test]
fn test_join_same() {
    // _2 = const 0_i32
    // _3 = _2
    // _5 = &mut _3
    // _4 = &raw mut (*_5)
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _4 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // goto -> bb2
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = y;
        let mut w: *mut libc::c_int = &mut z;
        if x != 0 {
            w = 0 as *mut libc::c_int;
        }
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=3);
            assert_eq!(n[&2].as_ptr(), n[&3].as_ptr());
        },
    );
}

#[test]
fn test_join_diff() {
    // _2 = const 0_i32
    // _3 = _2
    // _4 = _2
    // _6 = &mut _3
    // _5 = &raw mut (*_6)
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _7 = const 1_i32
    // _4 = move _7
    // _9 = &mut _4
    // _8 = &raw mut (*_9)
    // _5 = move _8
    // goto -> bb2
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = y;
        let mut w: libc::c_int = y;
        let mut v: *mut libc::c_int = &mut z;
        if x != 0 {
            w = 1 as libc::c_int;
            v = &mut w;
        }
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=4);
            assert_eq!(n[&2].as_ptr(), n[&3].as_ptr());
            assert_ne!(n[&2].as_ptr(), n[&4].as_ptr());
        },
    );
}

#[test]
fn test_join_loop() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // goto -> bb1
    // _4 = _1
    // _5 = const 10_i32
    // _3 = Lt(move _4, move _5)
    // switchInt(move _3) -> [0: bb3, otherwise: bb2]
    // _6 = const 1_i32
    // _1 = Add(_1, move _6)
    // _7 = _1
    // _2 = move _7
    // goto -> bb1
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        while x < 10 as libc::c_int {
            x += 1 as libc::c_int;
            y = x;
        }
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=2);
            assert_eq!(n[&1].as_ptr(), n[&2].as_ptr());
            assert_eq!(g.get_local_as_int(1), None);
        },
    );
}

#[test]
fn test_deref_eq_invalidate() {
    // _2 = const 0_i32
    // _3 = const 0_i32
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _5 = &mut _2
    // _4 = &raw mut (*_5)
    // goto -> bb3
    // _6 = &mut _3
    // _4 = &raw mut (*_6)
    // goto -> bb3
    // _7 = const 1_i32
    // (*_4) = move _7
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = 0 as libc::c_int;
        let mut w: *mut libc::c_int = if x != 0 { &mut y } else { &mut z };
        *w = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=3);
            assert_eq!(n[&2].obj, Obj::default());
            assert_eq!(n[&3].obj, Obj::default());
        },
    );
}

#[test]
fn test_call_invalidate() {
    // _2 = const 0_i32
    // (*_1) = move _2
    //
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = foo::f(_2)
    analyze_fn(
        "
        unsafe fn f(mut x: *mut libc::c_int) {
            *x = 0 as libc::c_int;
        }
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        f(y);
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            let i = get_ids(&g, 1..=3);
            assert_eq!(n[&2].as_ptr(), &AbsLoc::new_root(i[&1]));
            assert_eq!(n[&3].as_ptr(), &AbsLoc::new_root(i[&1]));

            assert_eq!(g.get_local_as_int(1), None);
        },
    );
}

#[test]
fn test_indirect_call_invalidate() {
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _3 = foo::f as unsafe fn(*mut i32) (PointerCoercion(ReifyFnPointer))
    // _2 = std::option::Option::<unsafe fn(*mut i32)>::Some(move _3)
    // goto -> bb3
    // _4 = foo::g as unsafe fn(*mut i32) (PointerCoercion(ReifyFnPointer))
    // _2 = std::option::Option::<unsafe fn(*mut i32)>::Some(move _4)
    // goto -> bb3
    // _5 = const 0_i32
    // _7 = &mut _5
    // _6 = &raw mut (*_7)
    // _10 = _2
    // _9 = std::option::Option::<unsafe fn(*mut i32)>::unwrap(move _10)
    // _8 = move _9(_6)
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        unsafe fn f(mut x: *mut libc::c_int) {
            *x = 0 as libc::c_int;
        }
        unsafe fn g(mut x: *mut libc::c_int) {}
        let mut h: Option::<unsafe fn(*mut libc::c_int) -> ()> = if x != 0 {
            Some(f as unsafe fn(*mut libc::c_int) -> ())
        } else {
            Some(g as unsafe fn(*mut libc::c_int) -> ())
        };
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: *mut libc::c_int = &mut y;
        h.unwrap()(z);
        ",
        |g, _, _| {
            let n = get_nodes(&g, 5..=7);
            let i = get_ids(&g, 5..=7);
            assert_eq!(n[&6].as_ptr(), &AbsLoc::new_root(i[&5]));
            assert_eq!(n[&7].as_ptr(), &AbsLoc::new_root(i[&5]));

            assert_eq!(g.get_local_as_int(5), None);
        },
    );
}

#[test]
fn test_memcpy_invalidate() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _6 = &mut _1
    // _5 = &raw mut (*_6)
    // _4 = move _5 as *mut libc::c_void (PtrToPtr)
    // _9 = &mut _2
    // _8 = &raw mut (*_9)
    // _7 = move _8 as *const libc::c_void (PtrToPtr)
    // _11 = std::mem::size_of::<i32>()
    // _10 = move _11 as u64 (IntToInt)
    // _3 = foo::memcpy(move _4, move _7, move _10)
    analyze_fn(
        "
        extern \"C\" {
            fn memcpy(
                _: *mut libc::c_void,
                _: *const libc::c_void,
                _: libc::c_ulong,
            ) -> *mut libc::c_void;
        }
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        memcpy(
            &mut x as *mut libc::c_int as *mut libc::c_void,
            &mut y as *mut libc::c_int as *const libc::c_void,
            ::std::mem::size_of::<libc::c_int>() as libc::c_ulong,
        );
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(1), None);
            assert_eq!(g.get_local_as_int(2), Some(0));
        },
    );
}

#[test]
fn test_as_mut_ptr() {
    // _1 = [const 0_i32; 1]
    // _4 = &mut _1
    // _3 = move _4 as &mut [i32] (PointerCoercion(Unsize))
    // _2 = core::slice::<impl [i32]>::as_mut_ptr(move _3)
    // _5 = const 1_i32
    // (*_2) = move _5
    analyze_fn(
        "
        let mut x: [libc::c_int; 1] = [0; 1];
        let mut y: *mut libc::c_int = x.as_mut_ptr();
        *y = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=5);
            assert_eq!(n[&1].field(0).as_ptr(), n[&5].as_ptr());

            assert_eq!(g.get_local_as_int(5), Some(1));
        },
    );
}

#[test]
fn test_write_volatile() {
    // _1 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _5 = const 1_i32
    // _2 = std::ptr::write_volatile::<i32>(move _3, move _5)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        ::std::ptr::write_volatile(&mut x as *mut libc::c_int, 1 as libc::c_int);
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=5);
            assert_eq!(n[&1].obj.as_ptr(), n[&5].obj.as_ptr());
            assert_eq!(g.get_local_as_int(1), Some(1));
        },
    );
}

#[test]
fn test_read_volatile() {
    // _1 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _8 = &_1
    // _7 = &raw const (*_8)
    // _6 = std::ptr::read_volatile::<i32>(move _7)
    // _9 = const 1_i32
    // _5 = Add(move _6, move _9)
    // _2 = std::ptr::write_volatile::<i32>(move _3, move _5)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        ::std::ptr::write_volatile(
            &mut x as *mut libc::c_int,
            ::std::ptr::read_volatile::<libc::c_int>(&x as *const libc::c_int)
                + 1 as libc::c_int,
        );
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=9);
            assert_eq!(n[&1].obj.as_ptr(), n[&5].obj.as_ptr());
            assert_eq!(n[&1].obj.as_ptr(), n[&9].obj.as_ptr());
            assert_eq!(g.get_local_as_int(1), Some(1));
            assert_eq!(g.get_local_as_int(6), Some(0));
        },
    );
}

#[test]
fn test_offset_array() {
    // _1 = [const 0_i32; 2]
    // _4 = &mut _1
    // _3 = move _4 as &mut [i32] (PointerCoercion(Unsize))
    // _2 = core::slice::<impl [i32]>::as_mut_ptr(move _3)
    // _5 = const 1_i32
    // _7 = _2
    // _9 = const 1_i32
    // _8 = move _9 as isize (IntToInt)
    // _6 = std::ptr::mut_ptr::<impl *mut i32>::offset(move _7, move _8)
    // (*_6) = move _5
    analyze_fn(
        "
        let mut x: [libc::c_int; 2] = [0; 2];
        let mut y: *mut libc::c_int = x.as_mut_ptr();
        *y.offset(1 as libc::c_int as isize) = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=5);
            assert_eq!(n[&1].field(1).as_ptr(), n[&5].as_ptr());

            assert_eq!(g.get_local_as_int(5), Some(1));
        },
    );
}

#[test]
fn test_offset_array_symbolic() {
    // _2 = [const 0_i32; 1]
    // _5 = &mut _2
    // _4 = move _5 as &mut [i32] (PointerCoercion(Unsize))
    // _3 = core::slice::<impl [i32]>::as_mut_ptr(move _4) -> [return: bb1, unwind continue]
    // _6 = const 1_i32
    // _8 = _3
    // _9 = _1 as isize (IntToInt)
    // _7 = std::ptr::mut_ptr::<impl *mut i32>::offset(move _8, move _9) -> [return: bb2, unwind continue]
    // (*_7) = move _6
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: [libc::c_int; 1] = [0; 1];
        let mut z: *mut libc::c_int = y.as_mut_ptr();
        *z.offset(x as isize) = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=6);
            assert_eq!(n[&2].symbolic(&[1, 9]).unwrap().as_ptr(), n[&6].as_ptr());

            assert_eq!(g.get_local_as_int(6), Some(1));
        },
    );
}

#[test]
fn test_offset() {
    // _2 = const 0_i32
    // _5 = const 1_i32
    // _4 = move _5 as isize (IntToInt)
    // _3 = std::ptr::mut_ptr::<impl *mut i32>::offset(_1, move _4)
    // (*_3) = move _2
    analyze_fn_with(
        "",
        "mut x: *mut libc::c_int",
        "
        *x.offset(1 as libc::c_int as isize) = 0 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            assert_eq!(n[&1].obj.as_ptr().root(), n[&3].obj.as_ptr().root());
            assert_eq!(n[&1].obj.as_ptr().projection()[0], AccElem::Int(0));
            assert_eq!(n[&3].obj.as_ptr().projection()[0], AccElem::Int(1));

            let n11 = &g.nodes[n[&3].as_ptr().root()].field(1);
            assert_eq!(n11.as_ptr(), n[&2].as_ptr());
        },
    );
}

#[test]
fn test_offset_twice() {
    // _2 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _5 = _1 as isize (IntToInt)
    // _4 = std::ptr::mut_ptr::<impl *mut s>::offset(_2, move _5)
    // _3 = ((*_4).0: i32)
    // _8 = _1 as isize (IntToInt)
    // _7 = std::ptr::mut_ptr::<impl *mut s>::offset(_2, move _8)
    // _6 = ((*_7).0: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "mut x: libc::c_int",
        "
        let mut s: *mut s = 0 as *mut s;
        let mut y: libc::c_int = (*s.offset(x as isize)).x;
        let mut z: libc::c_int = (*s.offset(x as isize)).x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 3..=6);
            assert_eq!(n[&3].obj.as_ptr().root(), n[&6].obj.as_ptr().root());
        },
    );
}

#[test]
fn test_offset_twice_struct() {
    // _3 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _2 = t { s: move _3 }
    // _6 = (_2.0: *mut s)
    // _8 = ((*_1).0: i32)
    // _7 = move _8 as isize (IntToInt)
    // _5 = std::ptr::mut_ptr::<impl *mut s>::offset(move _6, move _7)
    // _4 = ((*_5).0: i32)
    // _11 = (_2.0: *mut s)
    // _13 = ((*_1).0: i32)
    // _12 = move _13 as isize (IntToInt)
    // _10 = std::ptr::mut_ptr::<impl *mut s>::offset(move _11, move _12)
    // _9 = ((*_10).0: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub s: *mut s,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct r {
            pub x: libc::c_int,
        }
        ",
        "mut r: *mut r",
        "
        let mut t: t = t { s: 0 as *mut s };
        let mut x: libc::c_int = (*(t.s).offset((*r).x as isize)).x;
        let mut y: libc::c_int = (*(t.s).offset((*r).x as isize)).x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 4..=9);
            assert_eq!(n[&4].obj.as_ptr().root(), n[&9].obj.as_ptr().root());
        },
    );
}

#[test]
fn test_offset_switch() {
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub s: *mut s,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct r {
            pub x: libc::c_int,
        }
        ",
        "mut r: *mut r",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut t: t = t { s: 0 as *mut s };
        let mut x: libc::c_int = (*(t.s).offset((*r).x as isize)).x;
        match x {
            0 => {
                y = (*(t.s).offset((*r).x as isize)).x;
            }
            1 => {
                y = (*(t.s).offset((*r).x as isize)).x - 1 as libc::c_int;
            }
            _ => {}
        };
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(2), Some(0));
        },
    );
}

#[test]
fn test_offset_twice_2() {
    // _3 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _6 = _1 as isize (IntToInt)
    // _5 = std::ptr::mut_ptr::<impl *mut s>::offset(_3, move _6)
    // _4 = ((*_5).0: i32)
    // _9 = _2 as isize (IntToInt)
    // _8 = std::ptr::mut_ptr::<impl *mut s>::offset(_3, move _9)
    // _7 = ((*_8).0: i32)
    // _12 = _1 as isize (IntToInt)
    // _11 = std::ptr::mut_ptr::<impl *mut s>::offset(_3, move _12)
    // _10 = ((*_11).0: i32)
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "mut x: libc::c_int, mut y: libc::c_int",
        "
        let mut s: *mut s = 0 as *mut s;
        let mut a: libc::c_int = (*s.offset(x as isize)).x;
        let mut b: libc::c_int = (*s.offset(y as isize)).x;
        let mut c: libc::c_int = (*s.offset(x as isize)).x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 4..=10);
            assert_eq!(n[&4].obj.as_ptr().root(), n[&10].obj.as_ptr().root(),);
            assert_ne!(n[&4].obj.as_ptr().root(), n[&7].obj.as_ptr().root(),);
        },
    );
}

#[test]
fn test_write_twice() {
    // _3 = [const 0_i32; 2]
    // _4 = const 0_i32
    // _5 = _1 as usize (IntToInt)
    // _6 = const 2_usize
    // _7 = Lt(_5, _6)
    // _3[_5] = move _4
    // _8 = const 1_i32
    // _9 = _2 as usize (IntToInt)
    // _10 = const 2_usize
    // _11 = Lt(_9, _10)
    // _3[_9] = move _8
    analyze_fn_with(
        "",
        "mut x: libc::c_int, mut y: libc::c_int",
        "
        let mut z: [libc::c_int; 2] = [0; 2];
        z[x as usize] = 0 as libc::c_int;
        z[y as usize] = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 3..=8);
            assert_eq!(n[&3].symbolic(&[2, 9]).unwrap().as_ptr(), n[&8].as_ptr());
            assert_eq!(n[&3].symbolic(&[1, 5]), None);
        },
    );
}

#[test]
fn test_for_switch() {
    // _2 = const 0_usize as *mut s (PointerFromExposedAddress)
    // _3 = const 0_i32
    // goto -> bb1
    // switchInt(_1) -> [0: bb4, otherwise: bb2]
    // switchInt(((*_2).0: i32)) -> [0: bb3, otherwise: bb1]
    // _4 = ((*_2).0: i32)
    // _3 = move _4
    // goto -> bb1
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
        }
        ",
        "b: bool",
        "
        let mut s: *mut s = 0 as *mut s;
        let mut x: libc::c_int = 0 as libc::c_int;
        while b {
            match (*s).x {
                0 => { x = (*s).x; }
                _ => {}
            }
        }
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(3), Some(0));
        },
    );
}
