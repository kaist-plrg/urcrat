use std::collections::HashMap;

use rustc_abi::FieldIdx;
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
        #[macro_use]
        extern crate c2rust_bitfields;
        {}
        unsafe extern \"C\" fn {}({}) {{
            {}
        }}
    ",
        types, name, params, code
    );
    run_compiler(&code, |tcx| {
        let res = analyze(tcx, false);
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
            let dn1 = g.obj_at_location(n[&1].as_ptr()).unwrap();
            assert_eq!(dn1.as_ptr(), n[&2].as_ptr());

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

            assert_eq!(
                n[&5].as_ptr(),
                &AbsLoc::new(i[&1], vec![AccElem::Field(FieldIdx::from_u32(0), false)])
            );
            assert_eq!(
                n[&6].as_ptr(),
                &AbsLoc::new(i[&1], vec![AccElem::Field(FieldIdx::from_u32(0), false)])
            );
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

            assert_eq!(
                n[&7].as_ptr(),
                &AbsLoc::new(i[&1], vec![AccElem::Field(FieldIdx::from_u32(0), false)])
            );
            assert_eq!(
                n[&8].as_ptr(),
                &AbsLoc::new(i[&1], vec![AccElem::Field(FieldIdx::from_u32(0), false)])
            );
        },
    );
}

#[test]
fn test_eq_union_first() {
    // _2 = const 0_i32
    // _1 = u { x: move _2 }
    // _3 = (_1.0: i32)
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
        let mut x: u = u { x: 0 as libc::c_int };
        let mut y: libc::c_int = x.x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            let Obj::Struct(fs, is_union) = &n[&1].obj else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 1);
            assert_eq!(
                fs.get(&FieldIdx::from_u32(0)).unwrap().as_ptr(),
                n[&2].as_ptr()
            );
            assert_eq!(
                fs.get(&FieldIdx::from_u32(0)).unwrap().as_ptr(),
                n[&3].as_ptr()
            );
            assert_eq!(fs.get(&FieldIdx::from_u32(1)), None);
        },
    );
}

#[test]
fn test_eq_union_second() {
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
            let Obj::Struct(fs, is_union) = &n[&2].obj else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 1);
            assert_eq!(fs.get(&FieldIdx::from_u32(0)), None);
            assert_eq!(
                fs.get(&FieldIdx::from_u32(1)).unwrap().as_ptr(),
                n[&1].as_ptr()
            );
            assert_eq!(
                fs.get(&FieldIdx::from_u32(1)).unwrap().as_ptr(),
                n[&3].as_ptr()
            );
        },
    );
}

#[test]
fn test_union_field_eq() {
    // _2 = const 0_i32
    // _1 = u { x: move _2 }
    // _3 = const 1_i32
    // (_1.1: i32) = move _3
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
        let mut x: u = u { x: 0 as libc::c_int };
        x.y = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=3);
            let Obj::Struct(fs, is_union) = &n[&1].obj else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 1);
            assert_eq!(fs.get(&FieldIdx::from_u32(0)), None);
            assert_eq!(
                fs.get(&FieldIdx::from_u32(1)).unwrap().as_ptr(),
                n[&3].as_ptr()
            );
        },
    );
}

#[test]
fn test_union_eq_first() {
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
        pub union u {
            pub x: s,
            pub y: s,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: libc::c_int,
            pub y: u,
        }
        ",
        "",
        "
        let mut x: t = t {
            x: 0,
            y: u { x: s { x: 0, y: 0 } },
        };
        let mut y: t = x;
        let mut z: *mut t = &mut y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            let Obj::Struct(fs, is_union) = n[&4].field(1) else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 1);
            assert_eq!(
                n[&4].field(1).field(0).field(0).as_ptr(),
                n[&1].field(1).field(0).field(0).as_ptr()
            );
            assert_eq!(
                n[&4].field(1).field(0).field(1).as_ptr(),
                n[&1].field(1).field(0).field(1).as_ptr()
            );
        },
    );
}

#[test]
fn test_union_eq_second() {
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
        pub union u {
            pub x: s,
            pub y: s,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct t {
            pub x: libc::c_int,
            pub y: u,
        }
        ",
        "",
        "
        let mut x: t = {
            let mut init = t {
                x: 0 as libc::c_int,
                y: u {
                    y: {
                        let mut init = s {
                            x: 0 as libc::c_int,
                            y: 0 as libc::c_int,
                        };
                        init
                    },
                },
            };
            init
        };
        let mut y: t = x;
        let mut z: *mut t = &mut y;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=7);
            let Obj::Struct(fs, is_union) = n[&7].field(1) else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 1);
            assert_eq!(
                n[&7].field(1).field(1).field(0).as_ptr(),
                n[&1].field(1).field(1).field(0).as_ptr()
            );
            assert_eq!(
                n[&7].field(1).field(1).field(1).as_ptr(),
                n[&1].field(1).field(1).field(1).as_ptr()
            );
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
            assert_eq!(n[&1].index(0).as_ptr(), n[&2].as_ptr());
            assert_eq!(n[&1].index(1).as_ptr(), n[&2].as_ptr());
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
            let n = get_nodes(&g, 1..=5);
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
            let dn1 = g.obj_at_location(n[&1].as_ptr()).unwrap();
            assert_eq!(dn1.field(0).as_ptr(), n[&2].as_ptr());
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
            let n = get_nodes(&g, (1..=6).chain(8..=8));
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
fn test_filter_twice() {
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        if x == 0 as libc::c_int || x == 1 as libc::c_int {
            if x == 1 as libc::c_int {
                y = 0 as libc::c_int;
            } else {
                y = x;
            }
        }
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
fn test_eq_invalidate() {
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
    // _2 = move _7
    analyze_fn_with(
        "",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut z: libc::c_int = 0 as libc::c_int;
        let mut w: *mut libc::c_int = if x != 0 { &mut y } else { &mut z };
        y = 1 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 4..=4);
            let dn4 = g.obj_at_location(n[&4].as_ptr()).unwrap();
            assert_eq!(dn4, &Obj::Top);
            assert_eq!(g.get_local_as_int(2), Some(1));
            assert_eq!(g.get_local_as_int(3), Some(0));
        },
    );
}

#[test]
fn test_struct_eq_invalidate() {
    // _4 = const 1_i32
    // _5 = const 2_i32
    // _3 = s { x: move _4, y: move _5 }
    // _2 = _3
    // _6 = _2
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _8 = &mut _2
    // _7 = &raw mut (*_8)
    // goto -> bb3
    // _9 = &mut _6
    // _7 = &raw mut (*_9)
    // goto -> bb3
    // _10 = const 3_i32
    // (_6.0: i32) = move _10
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                x: 1 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut z: s = y;
        let mut w: *mut s = if x != 0 { &mut y } else { &mut z };
        z.x = 3 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=7);
            assert_eq!(n[&2].field(0).as_ptr(), n[&3].field(0).as_ptr());
            assert_eq!(n[&2].field(1).as_ptr(), n[&3].field(1).as_ptr());
            assert_ne!(n[&2].field(0).as_ptr(), n[&6].field(0).as_ptr());
            assert_eq!(n[&2].field(1).as_ptr(), n[&6].field(1).as_ptr());
            let dn7 = g.obj_at_location(n[&7].as_ptr()).unwrap();
            assert_eq!(dn7.field(0), &Obj::Top);
            assert_eq!(n[&2].field(1).as_ptr(), dn7.field(1).as_ptr());
        },
    );
}

#[test]
fn test_struct_eq_field_invalidate() {
    // _4 = const 1_i32
    // _5 = const 1_i32
    // _3 = s { x: move _4, y: move _5 }
    // _2 = _3
    // _6 = _2
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _8 = &mut (_2.0: i32)
    // _7 = &raw mut (*_8)
    // goto -> bb3
    // _9 = &mut (_6.0: i32)
    // _7 = &raw mut (*_9)
    // goto -> bb3
    // switchInt(move _1) -> [0: bb5, otherwise: bb4]
    // _11 = &mut (_2.1: i32)
    // _10 = &raw mut (*_11)
    // goto -> bb6
    // _12 = &mut (_6.1: i32)
    // _10 = &raw mut (*_12)
    // goto -> bb6
    // _13 = const 2_i32
    // (_6.0: i32) = move _13
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                x: 1 as libc::c_int,
                y: 1 as libc::c_int,
            };
            init
        };
        let mut z: s = y;
        let mut w: *mut libc::c_int = if x != 0 { &mut y.x } else { &mut z.x };
        let mut v: *mut libc::c_int = if x != 0 { &mut y.y } else { &mut z.y };
        z.x = 2 as libc::c_int;
        ",
        |g, _, _| {
            let n = get_nodes(&g, (2..=7).chain(10..=10));
            assert_eq!(n[&2].field(0).as_ptr(), n[&2].field(1).as_ptr());
            assert_eq!(n[&2].field(0).as_ptr(), n[&3].field(0).as_ptr());
            assert_eq!(n[&2].field(0).as_ptr(), n[&3].field(1).as_ptr());
            assert_ne!(n[&2].field(0).as_ptr(), n[&6].field(0).as_ptr());
            assert_eq!(n[&2].field(0).as_ptr(), n[&6].field(1).as_ptr());
            let dn7 = g.obj_at_location(n[&7].as_ptr()).unwrap();
            assert_eq!(dn7, &Obj::Top);
            let dn10 = g.obj_at_location(n[&10].as_ptr()).unwrap();
            assert_eq!(dn10.as_ptr(), n[&2].field(0).as_ptr());
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
            assert_eq!(n[&2].obj, Obj::Top);
            assert_eq!(n[&3].obj, Obj::Top);
        },
    );
}

#[test]
fn test_deref_struct_eq_invalidate() {
    // _4 = const 1_i32
    // _5 = const 2_i32
    // _3 = s { x: move _4, y: move _5 }
    // _2 = _3
    // _6 = _2
    // _7 = const 3_i32
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _9 = &mut _2
    // _8 = &raw mut (*_9)
    // goto -> bb3
    // _10 = &mut _6
    // _8 = &raw mut (*_10)
    // goto -> bb3
    // ((*_8).0: i32) = _7
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                x: 1 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut z: s = y;
        let mut w: libc::c_int = 3 as libc::c_int;
        let mut v: *mut s = if x != 0 { &mut y } else { &mut z };
        (*v).x = w;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=8);
            assert_eq!(n[&2].field(0), &Obj::Top);
            assert_eq!(n[&3].field(0).as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&6].field(0), &Obj::Top);
            assert_eq!(n[&2].field(1).as_ptr(), n[&3].field(1).as_ptr());
            assert_eq!(n[&2].field(1).as_ptr(), n[&6].field(1).as_ptr());
            let dn8 = g.obj_at_location(n[&8].as_ptr()).unwrap();
            assert_eq!(dn8.field(0).as_ptr(), n[&7].as_ptr());
            assert_eq!(dn8.field(1).as_ptr(), n[&2].field(1).as_ptr());
        },
    );
}

#[test]
fn test_deref_struct_eq_field_invalidate() {
    // _4 = const 1_i32
    // _5 = const 2_i32
    // _3 = s { x: move _4, y: move _5 }
    // _2 = _3
    // _6 = _2
    // _7 = const 3_i32
    // switchInt(move _1) -> [0: bb2, otherwise: bb1]
    // _9 = &mut (_2.0: i32)
    // _8 = &raw mut (*_9)
    // goto -> bb3
    // _10 = &mut (_6.1: i32)
    // _8 = &raw mut (*_10)
    // goto -> bb3
    // (*_8) = _7
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        ",
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                x: 1 as libc::c_int,
                y: 2 as libc::c_int,
            };
            init
        };
        let mut z: s = y;
        let mut w: libc::c_int = 3 as libc::c_int;
        let mut v: *mut libc::c_int = if x != 0 { &mut y.x } else { &mut z.y };
        *v = w;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 2..=8);
            assert_eq!(n[&2].field(0), &Obj::Top);
            assert_eq!(n[&2].field(1).as_ptr(), n[&5].as_ptr());
            assert_eq!(n[&3].field(0).as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&3].field(1).as_ptr(), n[&5].as_ptr());
            assert_eq!(n[&6].field(0).as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&6].field(1), &Obj::Top);
            let dn8 = g.obj_at_location(n[&8].as_ptr()).unwrap();
            assert_eq!(dn8.as_ptr(), n[&7].as_ptr());
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
    analyze_fn_with(
        "
        extern \"C\" {
            fn memcpy(
                _: *mut libc::c_void,
                _: *const libc::c_void,
                _: libc::c_ulong,
            ) -> *mut libc::c_void;
        }
        ",
        "",
        "
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
            assert_eq!(n[&1].index(0).as_ptr(), n[&5].as_ptr());

            assert_eq!(g.get_local_as_int(5), Some(1));
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
            assert_eq!(n[&1].index(1).as_ptr(), n[&5].as_ptr());

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
            assert_eq!(n[&1].as_ptr().root(), n[&3].as_ptr().root());
            assert_eq!(n[&1].as_ptr().projection()[0], AccElem::num_index(0));
            assert_eq!(n[&3].as_ptr().projection()[0], AccElem::num_index(1));

            let n11 = &g.nodes[n[&3].as_ptr().root()].index(1);
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
            assert_eq!(n[&3].as_ptr().root(), n[&6].as_ptr().root());
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
            assert_eq!(n[&4].as_ptr().root(), n[&9].as_ptr().root());
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
            assert_eq!(n[&4].as_ptr().root(), n[&10].as_ptr().root(),);
            assert_ne!(n[&4].as_ptr().root(), n[&7].as_ptr().root(),);
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
            let n = get_nodes(&g, [3, 8].into_iter());
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
                0 => x = (*s).x,
                _ => {}
            }
        }
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(3), Some(0));
        },
    );
}

#[test]
fn test_loop_offset() {
    // _2 = const 0_i32
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = _3
    // goto -> bb1
    // switchInt(_1) -> [0: bb6, otherwise: bb2]
    // switchInt((*_4)) -> [0: bb3, otherwise: bb4]
    // _5 = (*_4)
    // _2 = move _5
    // goto -> bb4
    // _7 = _4
    // _6 = std::ptr::mut_ptr::<impl *mut i32>::offset(move _7, const 1_isize)
    // _4 = move _6
    // goto -> bb1
    analyze_fn_with(
        "",
        "b: bool",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut libc::c_int = w;
        while b {
            match *z {
                0 => y = *z,
                _ => {}
            }
            z = z.offset(1);
        }
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(2), Some(0));
        },
    );
}

#[test]
fn test_loop_offset_struct() {
    // _2 = const 0_i32
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = _3
    // goto -> bb1
    // switchInt(_1) -> [0: bb6, otherwise: bb2]
    // switchInt((*_4)) -> [0: bb3, otherwise: bb4]
    // _5 = (*_4)
    // _2 = move _5
    // goto -> bb4
    // _7 = _4
    // _6 = std::ptr::mut_ptr::<impl *mut i32>::offset(move _7, const 1_isize)
    // _4 = move _6
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
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut w: *mut s = 0 as *mut s;
        let mut z: *mut s = w;
        while b {
            match (*z).x {
                0 => y = (*z).x,
                _ => {}
            }
            z = z.offset(1);
        }
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(2), Some(0));
        },
    );
}

#[test]
fn test_bitfield_write() {
    // _2 = [const 0_u8; 1]
    // _3 = [const 0_u8; 3]
    // _1 = s { x: const 0_i32, y_z: move _2, c2rust_padding: move _3 }
    // _4 = const 0_i32
    // (_1.0: i32) = move _4
    // _6 = &mut _1
    // _7 = const 1_i32
    // _5 = s::set_y(move _6, move _7) -> [return: bb1, unwind continue]
    // _9 = &mut _1
    // _10 = const 2_i32
    // _8 = s::set_z(move _9, move _10) -> [return: bb2, unwind continue]
    analyze_fn_with(
        "
        #[derive(Copy, Clone, BitfieldStruct)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            #[bitfield(name = \"y\", ty = \"libc::c_int\", bits = \"0..=2\")]
            #[bitfield(name = \"z\", ty = \"libc::c_int\", bits = \"3..=7\")]
            pub y_z: [u8; 1],
            #[bitfield(padding)]
            pub c2rust_padding: [u8; 3],
        }
        ",
        "",
        "
        let mut x: s = s {
            x: 0,
            y_z: [0; 1],
            c2rust_padding: [0; 3],
        };
        x.x = 0 as libc::c_int;
        x.set_y(1 as libc::c_int);
        x.set_z(2 as libc::c_int);
        ",
        |g, _, _| {
            let n = get_nodes(&g, [1, 4, 7, 10].into_iter());
            assert_eq!(n[&1].field(0).as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&1].field(3).as_ptr(), n[&7].as_ptr());
            assert_eq!(n[&1].field(4).as_ptr(), n[&10].as_ptr());
        },
    );
}

#[test]
fn test_bitfield_read() {
    // _3 = [const 0_u8; 1]
    // _4 = [const 0_u8; 3]
    // _5 = const 0_i32
    // _2 = s { x: move _5, y_z: move _3, c2rust_padding: move _4 }
    // _7 = &mut _2
    // _8 = const 1_i32
    // _6 = s::set_y(move _7, move _8) -> [return: bb1, unwind continue]
    // _10 = &mut _2
    // _11 = const 2_i32
    // _9 = s::set_z(move _10, move _11) -> [return: bb2, unwind continue]
    // _1 = _2
    // _12 = (_1.0: i32)
    // _14 = &_1
    // _13 = s::y(move _14) -> [return: bb3, unwind continue]
    // _16 = &_1
    // _15 = s::z(move _16) -> [return: bb4, unwind continue]
    analyze_fn_with(
        "
        #[derive(Copy, Clone, BitfieldStruct)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            #[bitfield(name = \"y\", ty = \"libc::c_int\", bits = \"0..=2\")]
            #[bitfield(name = \"z\", ty = \"libc::c_int\", bits = \"3..=7\")]
            pub y_z: [u8; 1],
            #[bitfield(padding)]
            pub c2rust_padding: [u8; 3],
        }
        ",
        "",
        "
        let mut x: s = {
            let mut init = s {
                y_z: [0; 1],
                c2rust_padding: [0; 3],
                x: 0 as libc::c_int,
            };
            init.set_y(1 as libc::c_int);
            init.set_z(2 as libc::c_int);
            init
        };
        let mut y: libc::c_int = x.x;
        let mut z: libc::c_int = x.y();
        let mut w: libc::c_int = x.z();
        ",
        |g, _, _| {
            let n = get_nodes(&g, [1, 2, 5, 8, 11, 12, 13, 15].into_iter());
            assert_eq!(n[&1].field(0).as_ptr(), n[&5].as_ptr());
            assert_eq!(n[&1].field(3).as_ptr(), n[&8].as_ptr());
            assert_eq!(n[&1].field(4).as_ptr(), n[&11].as_ptr());
            assert_eq!(n[&2].field(0).as_ptr(), n[&5].as_ptr());
            assert_eq!(n[&2].field(3).as_ptr(), n[&8].as_ptr());
            assert_eq!(n[&2].field(4).as_ptr(), n[&11].as_ptr());
            assert_eq!(n[&12].as_ptr(), n[&5].as_ptr());
            assert_eq!(n[&13].as_ptr(), n[&8].as_ptr());
            assert_eq!(n[&15].as_ptr(), n[&11].as_ptr());
        },
    );
}

#[test]
fn test_bitfield_eq_invalidate() {
    // _4 = [const 0_u8; 1]
    // _5 = [const 0_u8; 3]
    // _6 = const 0_i32
    // _3 = s { x: move _6, y_z: move _4, c2rust_padding: move _5 }
    // _8 = &mut _3
    // _9 = const 0_i32
    // _7 = s::set_y(move _8, move _9) -> [return: bb1, unwind continue]
    // _11 = &mut _3
    // _12 = const 0_i32
    // _10 = s::set_z(move _11, move _12) -> [return: bb2, unwind continue]
    // _2 = _3
    // _15 = [const 0_u8; 1]
    // _16 = [const 0_u8; 3]
    // _17 = const 0_i32
    // _14 = s { x: move _17, y_z: move _15, c2rust_padding: move _16 }
    // _19 = &mut _14
    // _20 = const 0_i32
    // _18 = s::set_y(move _19, move _20) -> [return: bb3, unwind continue]
    // _22 = &mut _14
    // _23 = const 0_i32
    // _21 = s::set_z(move _22, move _23) -> [return: bb4, unwind continue]
    // _13 = _14
    // switchInt(move _1) -> [0: bb6, otherwise: bb5]
    // _25 = &mut _2
    // _24 = &raw mut (*_25)
    // goto -> bb7
    // _26 = &mut _13
    // _24 = &raw mut (*_26)
    // goto -> bb7
    // _28 = &mut _2
    // _29 = const 1_i32
    // _27 = s::set_y(move _28, move _29) -> [return: bb8, unwind continue]
    analyze_fn_with(
        "
        #[derive(Copy, Clone, BitfieldStruct)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            #[bitfield(name = \"y\", ty = \"libc::c_int\", bits = \"0..=2\")]
            #[bitfield(name = \"z\", ty = \"libc::c_int\", bits = \"3..=7\")]
            pub y_z: [u8; 1],
            #[bitfield(padding)]
            pub c2rust_padding: [u8; 3],
        }
        ",
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                y_z: [0; 1],
                c2rust_padding: [0; 3],
                x: 0 as libc::c_int,
            };
            init.set_y(0 as libc::c_int);
            init.set_z(0 as libc::c_int);
            init
        };
        let mut z: s = {
            let mut init = s {
                y_z: [0; 1],
                c2rust_padding: [0; 3],
                x: 0 as libc::c_int,
            };
            init.set_y(0 as libc::c_int);
            init.set_z(0 as libc::c_int);
            init
        };
        let mut w: *mut s = if x != 0 { &mut y } else { &mut z };
        y.set_y(1 as libc::c_int);
        ",
        |g, _, _| {
            let n = get_nodes(&g, [2, 3, 6, 13, 14, 24, 29].into_iter());
            assert_eq!(n[&2].field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&2].field(3).as_ptr(), n[&29].as_ptr());
            assert_eq!(n[&2].field(4).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&3].field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&3].field(3).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&3].field(4).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&13].field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&13].field(3).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&13].field(4).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&14].field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&14].field(3).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&14].field(4).as_ptr(), n[&6].as_ptr());
            let dn24 = g.obj_at_location(n[&24].as_ptr()).unwrap();
            assert_eq!(dn24.field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(dn24.field(3), &Obj::Top);
            assert_eq!(dn24.field(4).as_ptr(), n[&6].as_ptr());
        },
    );
}

#[test]
fn test_bitfield_deref_eq_invalidate() {
    // _4 = [const 0_u8; 1]
    // _5 = [const 0_u8; 3]
    // _6 = const 0_i32
    // _3 = s { x: move _6, y_z: move _4, c2rust_padding: move _5 }
    // _8 = &mut _3
    // _9 = const 0_i32
    // _7 = s::set_y(move _8, move _9) -> [return: bb1, unwind continue]
    // _11 = &mut _3
    // _12 = const 0_i32
    // _10 = s::set_z(move _11, move _12) -> [return: bb2, unwind continue]
    // _2 = _3
    // _15 = [const 0_u8; 1]
    // _16 = [const 0_u8; 3]
    // _17 = const 0_i32
    // _14 = s { x: move _17, y_z: move _15, c2rust_padding: move _16 }
    // _19 = &mut _14
    // _20 = const 0_i32
    // _18 = s::set_y(move _19, move _20) -> [return: bb3, unwind continue]
    // _22 = &mut _14
    // _23 = const 0_i32
    // _21 = s::set_z(move _22, move _23) -> [return: bb4, unwind continue]
    // _13 = _14
    // switchInt(move _1) -> [0: bb6, otherwise: bb5]
    // _25 = &mut _2
    // _24 = &raw mut (*_25)
    // goto -> bb7
    // _26 = &mut _13
    // _24 = &raw mut (*_26)
    // goto -> bb7
    // _28 = &mut (*_24)
    // _29 = const 1_i32
    // _27 = s::set_y(move _28, move _29) -> [return: bb8, unwind continue]
    analyze_fn_with(
        "
        #[derive(Copy, Clone, BitfieldStruct)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            #[bitfield(name = \"y\", ty = \"libc::c_int\", bits = \"0..=2\")]
            #[bitfield(name = \"z\", ty = \"libc::c_int\", bits = \"3..=7\")]
            pub y_z: [u8; 1],
            #[bitfield(padding)]
            pub c2rust_padding: [u8; 3],
        }
        ",
        "mut x: libc::c_int",
        "
        let mut y: s = {
            let mut init = s {
                y_z: [0; 1],
                c2rust_padding: [0; 3],
                x: 0 as libc::c_int,
            };
            init.set_y(0 as libc::c_int);
            init.set_z(0 as libc::c_int);
            init
        };
        let mut z: s = {
            let mut init = s {
                y_z: [0; 1],
                c2rust_padding: [0; 3],
                x: 0 as libc::c_int,
            };
            init.set_y(0 as libc::c_int);
            init.set_z(0 as libc::c_int);
            init
        };
        let mut w: *mut s = if x != 0 { &mut y } else { &mut z };
        (*w).set_y(1 as libc::c_int);
        ",
        |g, _, _| {
            let n = get_nodes(&g, [2, 3, 6, 13, 14, 24, 29].into_iter());
            assert_eq!(n[&2].field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&2].field(3), &Obj::Top);
            assert_eq!(n[&2].field(4).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&3].field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&3].field(3).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&3].field(4).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&13].field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&13].field(3), &Obj::Top);
            assert_eq!(n[&13].field(4).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&14].field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&14].field(3).as_ptr(), n[&6].as_ptr());
            assert_eq!(n[&14].field(4).as_ptr(), n[&6].as_ptr());
            let dn24 = g.obj_at_location(n[&24].as_ptr()).unwrap();
            assert_eq!(dn24.field(0).as_ptr(), n[&6].as_ptr());
            assert_eq!(dn24.field(3).as_ptr(), n[&29].as_ptr());
            assert_eq!(dn24.field(4).as_ptr(), n[&6].as_ptr());
        },
    );
}

#[test]
fn test_union_invalidate() {
    // _2 = u { x: const 0_i32 }
    // _1 = s { x: const 0_i32, y: move _2 }
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _3 = g(move _4) -> [return: bb1, unwind continue]
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: u,
        }
        pub unsafe extern \"C\" fn g(mut x: *mut s) {
            let mut y: u = u { x: 0 as libc::c_int };
            (*x).y = y;
        }
        ",
        "",
        "
        let mut x: s = s { x: 0, y: u { x: 0 } };
        g(&mut x);
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=1);
            let Obj::Struct(fs, is_union) = &n[&1].field(1) else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 0);
        },
    );
}

#[test]
fn test_union_field_invalidate() {
    // _2 = u { x: const 0_i32 }
    // _1 = s { x: const 0_i32, y: move _2 }
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _3 = g(move _4) -> [return: bb1, unwind continue]
    analyze_fn_with(
        "
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union u {
            pub x: libc::c_int,
            pub y: libc::c_int,
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct s {
            pub x: libc::c_int,
            pub y: u,
        }
        pub unsafe extern \"C\" fn g(mut x: *mut s) {
            (*x).y.y = 0 as libc::c_int;
        }
        ",
        "",
        "
        let mut x: s = s { x: 0, y: u { x: 0 } };
        g(&mut x);
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=1);
            let Obj::Struct(fs, is_union) = &n[&1].field(1) else { unreachable!() };
            assert!(is_union);
            assert_eq!(fs.len(), 0);
        },
    );
}

#[test]
fn test_eq_static() {
    // _1 = const 1_i32
    // _2 = const {alloc1: *mut i32}
    // (*_2) = move _1
    // _4 = const {alloc1: *mut i32}
    // _3 = (*_4)
    analyze_fn_with(
        "
        pub static mut x: libc::c_int = 0 as libc::c_int;
        ",
        "",
        "
        x = 1 as libc::c_int;
        let mut y: libc::c_int = x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=4);
            assert_eq!(n[&1].as_ptr(), n[&3].as_ptr());
            assert_eq!(n[&2].as_ptr(), n[&4].as_ptr());
        },
    );
}

#[test]
fn test_static_invalidate() {
    // _1 = const 1_i32
    // _2 = const {alloc1: *mut i32}
    // (*_2) = move _1
    // _3 = g() -> [return: bb1, unwind continue]
    // _5 = const {alloc1: *mut i32}
    // _4 = (*_5)
    analyze_fn_with(
        "
        pub static mut x: libc::c_int = 0 as libc::c_int;
        pub unsafe extern \"C\" fn g() {
            x = 2 as libc::c_int;
        }
        ",
        "",
        "
        x = 1 as libc::c_int;
        g();
        let mut y: libc::c_int = x;
        ",
        |g, _, _| {
            let n = get_nodes(&g, 1..=5);
            assert_ne!(n[&1].as_ptr(), n[&4].as_ptr());
            assert_eq!(n[&2].as_ptr(), n[&5].as_ptr());
        },
    );
}

#[test]
fn test_switch_filter() {
    // _2 = const 0_i32
    // switchInt(_1) -> [1: bb2, 2: bb3, otherwise: bb1]
    // _5 = const 3_i32
    // _2 = move _5
    // goto -> bb4
    // _3 = const 1_i32
    // _2 = move _3
    // goto -> bb4
    // _4 = const 2_i32
    // _2 = move _4
    // goto -> bb4
    // _6 = const 0_i32
    // switchInt(_2) -> [1: bb6, 2: bb6, otherwise: bb5]
    // _8 = _2
    // _6 = move _8
    // goto -> bb7
    // _7 = const 3_i32
    // _6 = move _7
    // goto -> bb7
    analyze_fn_with(
        "
        ",
        "mut x: libc::c_int",
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        match x {
            1 => {
                y = 1 as libc::c_int;
            }
            2 => {
                y = 2 as libc::c_int;
            }
            _ => {
                y = 3 as libc::c_int;
            }
        }
        let mut z: libc::c_int = 0 as libc::c_int;
        match y {
            1 | 2 => {
                z = 3 as libc::c_int;
            }
            _ => {
                z = y;
            }
        };
        ",
        |g, _, _| {
            assert_eq!(g.get_local_as_int(6), Some(3));
        },
    );
}
