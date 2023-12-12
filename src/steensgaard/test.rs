use super::*;

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    let input = compile_util::str_to_input(code);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, f);
}

fn analyze_fn<F: FnOnce(Vec<VarId>, Vec<Type>) + Send>(code: &str, f: F) {
    let name = "foo";
    let code = format!("extern crate libc;unsafe fn {}(){{{}}}", name, code);
    run_compiler(&code, |tcx| {
        let res = analyze(tcx);
        let (def_id, n) = find_fn(name, tcx);
        let x: Vec<_> = (0..n).map(|i| res.local(def_id, i)).collect();
        let t: Vec<_> = x.iter().map(|x| res.var_ty(*x)).collect();
        f(x, t);
    });
}

fn find_fn(name: &str, tcx: TyCtxt<'_>) -> (LocalDefId, u32) {
    let hir = tcx.hir();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        if matches!(item.kind, ItemKind::Fn(_, _, _)) && item.ident.name.as_str() == name {
            let local_def_id = item.owner_id.def_id;
            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let locals = body.local_decls.len();
            return (local_def_id, locals as _);
        }
    }
    panic!()
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
        |x, t| {
            assert_ne!(x[2], x[3]);
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_ref_twice() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _2 = move _4
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        y = &mut x;
        ",
        |x, t| {
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[5].var_ty, x[1]);
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
        |x, t| {
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[5].var_ty, x[1]);
            assert_eq!(t[6].var_ty, x[1]);
            assert_eq!(t[7].var_ty, x[1]);
            assert_eq!(t[8].var_ty, x[1]);
            assert_eq!(x[1], x[2]);
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
        |x, t| {
            assert_eq!(t[7].var_ty, x[3]);
            assert_eq!(t[8].var_ty, x[3]);
            assert_eq!(t[9].var_ty, x[3]);
            assert_eq!(t[10].var_ty, x[3]);
            assert_eq!(t[11].var_ty, x[3]);
            assert_eq!(t[12].var_ty, x[3]);
            assert_eq!(x[3], x[5]);

            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[6].var_ty, x[1]);
            assert_eq!(x[1], x[2]);

            assert_ne!(x[3], x[4]);
            assert_ne!(x[3], x[6]);
        },
    );
}

#[test]
fn test_eq() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = _2
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
        z = y;
        ",
        |x, t| {
            assert_ne!(x[2], x[3]);
            assert_ne!(x[2], x[4]);
            assert_ne!(x[3], x[4]);
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_bot() {
    // _1 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = _1
    analyze_fn(
        "
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
        z = y;
        ",
        |x, t| {
            assert_ne!(x[1], x[2]);
            assert_ne!(t[1], t[2]);
        },
    );
}

#[test]
fn test_eq_bot2() {
    // _1 = const 0_i32
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _3 = _2
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _3 = move _4
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
        z = y;
        z = &mut x;
        ",
        |x, t| {
            assert_ne!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[5].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_pending() {
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
        |x, t| {
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[5].var_ty, x[1]);
            assert_eq!(t[6].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_pending_2() {
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
        |x, t| {
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[5].var_ty, x[1]);
            assert_eq!(t[6].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_join() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _3 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _4 = const 0_i32
    // _6 = &mut _2
    // _5 = &raw mut (*_6)
    // _8 = &mut _3
    // _7 = &raw mut (*_8)
    // _10 = &mut _4
    // _9 = &raw mut (*_10)
    // _3 = move _9
    // _12 = &mut _2
    // _11 = &raw mut (*_12)
    // _3 = move _11
    // _14 = &mut _3
    // _13 = &raw mut (*_14)
    analyze_fn(
        "
        let mut p: libc::c_int = 0 as libc::c_int;
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut z: libc::c_int = 0 as libc::c_int;
        let mut a: *mut libc::c_int = &mut x;
        let mut b: *mut *mut libc::c_int = &mut y;
        if p != 0 {
            y = &mut z;
        } else {
            y = &mut x;
        }
        let mut c: *mut *mut libc::c_int = &mut y;
        ",
        |x, t| {
            assert_eq!(t[7].var_ty, x[3]);
            assert_eq!(t[8].var_ty, x[3]);
            assert_eq!(t[13].var_ty, x[3]);
            assert_eq!(t[14].var_ty, x[3]);

            assert_eq!(t[3].var_ty, x[2]);
            assert_eq!(t[5].var_ty, x[2]);
            assert_eq!(t[6].var_ty, x[2]);
            assert_eq!(t[9].var_ty, x[2]);
            assert_eq!(t[10].var_ty, x[2]);
            assert_eq!(t[11].var_ty, x[2]);
            assert_eq!(t[12].var_ty, x[2]);
            assert_eq!(x[2], x[4]);
        },
    );
}

#[test]
fn test_eq_deref() {
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
        |x, t| {
            assert_eq!(t[4].var_ty, x[2]);
            assert_eq!(t[5].var_ty, x[2]);
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[6].var_ty, x[1]);
        },
    );
}

#[test]
fn test_deref_eq() {
    // _1 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = const 0_i32
    // _6 = &mut _4
    // _5 = &raw mut (*_6)
    // (*_2) = _5
    analyze_fn(
        "
        let mut x: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut y: *mut *mut libc::c_int = &mut x;
        let mut z: libc::c_int = 0 as libc::c_int;
        let mut w: *mut libc::c_int = &mut z;
        *y = w;
        ",
        |x, t| {
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[1].var_ty, x[4]);
            assert_eq!(t[5].var_ty, x[4]);
            assert_eq!(t[6].var_ty, x[4]);
        },
    );
}
