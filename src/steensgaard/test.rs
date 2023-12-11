use super::*;

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    let input = compile_util::str_to_input(code);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, f);
}

fn find_fn(name: &str, tcx: TyCtxt<'_>) -> LocalDefId {
    let hir = tcx.hir();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        if matches!(item.kind, ItemKind::Fn(_, _, _)) && item.ident.name.as_str() == name {
            return item.owner_id.def_id;
        }
    }
    panic!()
}

#[test]
fn test_eq_ref() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    run_compiler(
        "
        extern crate libc;
        unsafe fn f() {
            let mut x: libc::c_int = 0 as libc::c_int;
            let mut y: *mut libc::c_int = &mut x;
        }
        ",
        |tcx| {
            let res = analyze(tcx);
            let f = find_fn("f", tcx);
            let x1 = res.local(f, 1);
            let x2 = res.local(f, 2);
            let x3 = res.local(f, 3);
            let t2 = res.var_ty(x2);
            let t3 = res.var_ty(x3);
            assert_ne!(x2, x3);
            assert_eq!(t2.var_ty, x1);
            assert_eq!(t3.var_ty, x1);
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
    run_compiler(
        "
        extern crate libc;
        unsafe fn f() {
            let mut x: libc::c_int = 0 as libc::c_int;
            let mut y: *mut libc::c_int = &mut x;
            let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
            z = y;
        }
        ",
        |tcx| {
            let res = analyze(tcx);
            let f = find_fn("f", tcx);
            let x1 = res.local(f, 1);
            let x2 = res.local(f, 2);
            let x3 = res.local(f, 3);
            let x4 = res.local(f, 4);
            let t2 = res.var_ty(x2);
            let t3 = res.var_ty(x3);
            let t4 = res.var_ty(x4);
            assert_ne!(x2, x3);
            assert_ne!(x2, x4);
            assert_ne!(x3, x4);
            assert_eq!(t2.var_ty, x1);
            assert_eq!(t3.var_ty, x1);
            assert_eq!(t4.var_ty, x1);
        },
    );
}

#[test]
fn test_eq_bot() {
    // _1 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _2 = _1
    run_compiler(
        "
        extern crate libc;
        unsafe fn f() {
            let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
            let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
            z = y;
        }
        ",
        |tcx| {
            let res = analyze(tcx);
            let f = find_fn("f", tcx);
            let x1 = res.local(f, 1);
            let x2 = res.local(f, 2);
            let t1 = res.var_ty(x1);
            let t2 = res.var_ty(x2);
            assert_ne!(x1, x2);
            assert_ne!(t1, t2);
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
    run_compiler(
        "
        extern crate libc;
        unsafe fn f() {
            let mut x: libc::c_int = 0 as libc::c_int;
            let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
            let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
            z = y;
            z = &mut x;
        }
        ",
        |tcx| {
            let res = analyze(tcx);
            let f = find_fn("f", tcx);
            let x1 = res.local(f, 1);
            let x2 = res.local(f, 2);
            let x3 = res.local(f, 3);
            let x4 = res.local(f, 4);
            let x5 = res.local(f, 5);
            let t2 = res.var_ty(x2);
            let t3 = res.var_ty(x3);
            let t4 = res.var_ty(x4);
            let t5 = res.var_ty(x5);
            assert_ne!(t2.var_ty, x1);
            assert_eq!(t3.var_ty, x1);
            assert_eq!(t4.var_ty, x1);
            assert_eq!(t5.var_ty, x1);
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
    run_compiler(
        "
        extern crate libc;
        unsafe fn f() {
            let mut x: libc::c_int = 0 as libc::c_int;
            let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
            let mut z: *mut libc::c_int = 0 as *mut libc::c_int;
            z = y;
            y = &mut x;
        }
        ",
        |tcx| {
            let res = analyze(tcx);
            let f = find_fn("f", tcx);
            let x1 = res.local(f, 1);
            let x2 = res.local(f, 2);
            let x3 = res.local(f, 3);
            let x4 = res.local(f, 4);
            let x5 = res.local(f, 5);
            let x6 = res.local(f, 6);
            let t2 = res.var_ty(x2);
            let t3 = res.var_ty(x3);
            let t4 = res.var_ty(x4);
            let t5 = res.var_ty(x5);
            let t6 = res.var_ty(x6);
            assert_eq!(t2.var_ty, x1);
            assert_eq!(t3.var_ty, x1);
            assert_eq!(t4.var_ty, x1);
            assert_eq!(t5.var_ty, x1);
            assert_eq!(t6.var_ty, x1);
        },
    );
}
