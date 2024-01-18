use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{Location, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::def_id::DefId;

use super::*;
use crate::*;

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    let input = compile_util::str_to_input(code);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, f).unwrap();
}

fn find_fn(name: &str, tcx: TyCtxt<'_>) -> DefId {
    let hir = tcx.hir();
    hir.items()
        .find_map(|item_id| {
            let item = hir.item(item_id);
            if item.ident.name.as_str() != name {
                return None;
            }
            Some(item_id.owner_id.to_def_id())
        })
        .unwrap()
}

fn find_return(def_id: DefId, tcx: TyCtxt<'_>) -> Location {
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

            // assert_eq!(n[&1].field(1).as_ptr(), n[&4].as_ptr());
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

            // assert_eq!(n[&1].field(1).as_ptr(), n[&4].as_ptr());
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

            // assert_eq!(n[&1].field(1).as_ptr(), n[&4].as_ptr());
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
            assert_eq!(n[&2].symbolic_obj().as_ptr(), n[&5].as_ptr());
            assert_eq!(n[&3].as_ptr(), n[&5].as_ptr());

            assert_eq!(n[&2].symbolic_index(), HashSet::from_iter([1, 4]));

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
            assert_eq!(n[&2].symbolic_obj().as_ptr(), n[&3].as_ptr());
            assert_eq!(n[&4].as_ptr(), n[&5].as_ptr());

            assert_eq!(n[&2].symbolic_index(), HashSet::from_iter([4, 5]));

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
