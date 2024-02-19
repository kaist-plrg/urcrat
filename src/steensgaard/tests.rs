use super::*;

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    let input = compile_util::str_to_input(code);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, f).unwrap();
}

fn analyze_fn_with_params<F>(params: &str, code: &str, f: F)
where F: FnOnce(Vec<VarId>, Vec<Type>, AnalysisResults, TyCtxt<'_>) + Send {
    let name = "foo";
    let code = format!(
        "
        #![feature(c_variadic)]
        extern crate libc;
        extern \"C\" {{
            fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
            fn realloc(_: *mut libc::c_void, _: libc::c_ulong) -> *mut libc::c_void;
        }}
        unsafe extern \"C\" fn {}({}) {{
            {}
        }}
    ",
        name, params, code
    );
    run_compiler(&code, |tcx| {
        let res = analyze(tcx);
        let (x, t) = get_xts(CallStr::Empty, name, &res, tcx);
        f(x, t, res, tcx);
    });
}

fn get_xt(cstr: CallStr, name: &str, res: &AnalysisResults, tcx: TyCtxt<'_>) -> (VarId, Type) {
    let (def_id, _) = find_item(name, tcx);
    let x = res.global(cstr, def_id);
    let t = res.var_ty(x);
    (x, t)
}

fn get_xts(
    cstr: CallStr,
    name: &str,
    res: &AnalysisResults,
    tcx: TyCtxt<'_>,
) -> (Vec<VarId>, Vec<Type>) {
    let (def_id, n) = find_item(name, tcx);
    let x: Vec<_> = (0..n).map(|i| res.local(cstr, def_id, i)).collect();
    let t = x.iter().map(|x| res.var_ty(*x)).collect();
    (x, t)
}

fn analyze_fn<F>(code: &str, f: F)
where F: FnOnce(Vec<VarId>, Vec<Type>, AnalysisResults, TyCtxt<'_>) + Send {
    analyze_fn_with_params("", code, f);
}

fn find_item(name: &str, tcx: TyCtxt<'_>) -> (LocalDefId, u32) {
    let hir = tcx.hir();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        if item.ident.name.as_str() == name {
            let local_def_id = item.owner_id.def_id;
            let locals = if matches!(item.kind, ItemKind::Fn(_, _, _)) {
                let body = tcx.optimized_mir(local_def_id.to_def_id());
                body.local_decls.len()
            } else {
                0
            };
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
        |x, t, _, _| {
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
        |x, t, _, _| {
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
        |x, t, _, _| {
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
        |x, t, _, _| {
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
        |x, t, _, _| {
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
        |_, t, _, _| {
            assert_ne!(t[1].var_ty, t[2].var_ty);
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
        |x, t, _, _| {
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
        |x, t, _, _| {
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
        |x, t, _, _| {
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
        |x, t, _, _| {
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
        |x, t, _, _| {
            assert_eq!(t[4].var_ty, x[2]);
            assert_eq!(t[5].var_ty, x[2]);
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[6].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_deref_bot() {
    // _1 = const 0_usize as *mut *mut i32 (PointerFromExposedAddress)
    // _2 = (*_1)
    // _3 = const 0_i32
    // _5 = &mut _3
    // _4 = &raw mut (*_5)
    // _2 = move _4
    // _6 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _8 = &mut _6
    // _7 = &raw mut (*_8)
    // _1 = move _7
    analyze_fn(
        "
        let mut y: *mut *mut libc::c_int = 0 as *mut *mut libc::c_int;
        let mut x: *mut libc::c_int = *y;
        let mut z: libc::c_int = 0 as libc::c_int;
        x = &mut z;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        y = &mut w;
        ",
        |x, t, _, _| {
            assert_eq!(t[1].var_ty, x[6]);
            assert_eq!(t[7].var_ty, x[6]);
            assert_eq!(t[8].var_ty, x[6]);

            assert_eq!(t[2].var_ty, x[3]);
            assert_eq!(t[4].var_ty, x[3]);
            assert_eq!(t[5].var_ty, x[3]);
            assert_eq!(t[6].var_ty, x[3]);
        },
    );
}

#[test]
fn test_eq_deref_pending() {
    // _1 = const 0_usize as *mut *mut i32 (PointerFromExposedAddress)
    // _2 = const 0_usize as *mut *mut i32 (PointerFromExposedAddress)
    // _3 = _1
    // _2 = move _3
    // _4 = (*_1)
    // _5 = const 0_i32
    // _7 = &mut _5
    // _6 = &raw mut (*_7)
    // _4 = move _6
    // _8 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _10 = &mut _8
    // _9 = &raw mut (*_10)
    // _1 = move _9
    analyze_fn(
        "
        let mut y1: *mut *mut libc::c_int = 0 as *mut *mut libc::c_int;
        let mut y2: *mut *mut libc::c_int = 0 as *mut *mut libc::c_int;
        y2 = y1;
        let mut x: *mut libc::c_int = *y1;
        let mut z: libc::c_int = 0 as libc::c_int;
        x = &mut z;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        y1 = &mut w;
        ",
        |x, t, _, _| {
            assert_eq!(t[1].var_ty, x[8]);
            assert_eq!(t[2].var_ty, x[8]);
            assert_eq!(t[3].var_ty, x[8]);
            assert_eq!(t[9].var_ty, x[8]);
            assert_eq!(t[10].var_ty, x[8]);

            assert_eq!(t[4].var_ty, x[5]);
            assert_eq!(t[6].var_ty, x[5]);
            assert_eq!(t[7].var_ty, x[5]);
            assert_eq!(t[8].var_ty, x[5]);
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
        |x, t, _, _| {
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[1].var_ty, x[4]);
            assert_eq!(t[5].var_ty, x[4]);
            assert_eq!(t[6].var_ty, x[4]);
        },
    );
}

#[test]
fn test_deref_eq_bot() {
    // _1 = const 0_usize as *mut *mut i32 (PointerFromExposedAddress)
    // _2 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _3 = _2
    // (*_1) = move _3
    // _4 = const 0_i32
    // _6 = &mut _4
    // _5 = &raw mut (*_6)
    // _2 = move _5
    // _7 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _9 = &mut _7
    // _8 = &raw mut (*_9)
    // _1 = move _8
    analyze_fn(
        "
        let mut x: *mut *mut libc::c_int = 0 as *mut *mut libc::c_int;
        let mut y: *mut libc::c_int = 0 as *mut libc::c_int;
        *x = y;
        let mut z: libc::c_int = 0 as libc::c_int;
        y = &mut z;
        let mut w: *mut libc::c_int = 0 as *mut libc::c_int;
        x = &mut w;
        ",
        |x, t, _, _| {
            assert_eq!(t[8].var_ty, x[7]);
            assert_eq!(t[9].var_ty, x[7]);
            assert_eq!(t[1].var_ty, x[7]);

            assert_eq!(t[2].var_ty, x[4]);
            assert_eq!(t[3].var_ty, x[4]);
            assert_eq!(t[5].var_ty, x[4]);
            assert_eq!(t[6].var_ty, x[4]);
            assert_eq!(t[7].var_ty, x[4]);
        },
    );
}

#[test]
fn test_deref_eq_deref() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = const 1_i32
    // (*_2) = Add((*_2), move _4)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        *y += 1 as libc::c_int;
        ",
        |x, t, _, _| {
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_alloc() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _6 = std::mem::size_of::<i32>()
    // _5 = move _6 as u64 (IntToInt)
    // _4 = malloc(move _5)
    // _2 = move _4 as *mut i32 (PtrToPtr)
    analyze_fn(
        "
        let mut y: libc::c_int = 0 as libc::c_int;
        let mut x: *mut libc::c_int = &mut y;
        x = malloc(::std::mem::size_of::<libc::c_int>() as libc::c_ulong)
            as *mut libc::c_int;
        ",
        |x, t, _, _| {
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_alloc_bot() {
    // _4 = std::mem::size_of::<i32>()
    // _3 = move _4 as u64 (IntToInt)
    // _2 = malloc(move _3)
    // _1 = move _2 as *mut i32 (PtrToPtr)
    analyze_fn(
        "
        let mut x: *mut libc::c_int = malloc(
            ::std::mem::size_of::<libc::c_int>() as libc::c_ulong,
        ) as *mut libc::c_int;
        let mut y: *mut libc::c_int = x;
        ",
        |_, t, _, _| {
            assert_eq!(t[1].var_ty, t[2].var_ty);
        },
    );
}

#[test]
fn test_eq_alloca_bot() {
    // _4 = std::mem::size_of::<i32>()
    // _3 = move _4 as u64 (IntToInt)
    // _2 = move _3 as usize (IntToInt)
    // _1 = std::vec::from_elem::<i32>(const 0_i32, move _2)
    // _8 = move _1
    // _7 = std::vec::Vec::<i32>::leak::<'_>(move _8)
    // _6 = _7
    // _5 = core::slice::<impl [i32]>::as_mut_ptr(move _6)
    // _9 = _5
    analyze_fn(
        "
        let mut fresh0 = ::std::vec::from_elem(
            0,
            ::std::mem::size_of::<libc::c_int>() as libc::c_ulong as usize,
        );
        let mut x: *mut libc::c_int = fresh0.leak().as_mut_ptr() as *mut libc::c_int;
        let mut y: *mut libc::c_int = x;
        ",
        |_, t, _, _| {
            assert_eq!(t[5].var_ty, t[1].var_ty);
            assert_eq!(t[6].var_ty, t[1].var_ty);
            assert_eq!(t[7].var_ty, t[1].var_ty);
            assert_eq!(t[8].var_ty, t[1].var_ty);
            assert_eq!(t[9].var_ty, t[1].var_ty);
        },
    );
}

#[test]
fn test_eq_realloc() {
    // _4 = std::mem::size_of::<i32>()
    // _3 = move _4 as u64 (IntToInt)
    // _2 = malloc(move _3)
    // _1 = move _2 as *mut i32 (PtrToPtr)
    // _7 = _1 as *mut libc::c_void (PtrToPtr)
    // _9 = std::mem::size_of::<i32>()
    // _8 = move _9 as u64 (IntToInt)
    // _6 = realloc(move _7, move _8)
    // _5 = move _6 as *mut i32 (PtrToPtr)
    analyze_fn(
        "
        let mut x: *mut libc::c_int = malloc(
            ::std::mem::size_of::<libc::c_int>() as libc::c_ulong,
        ) as *mut libc::c_int;
        let mut y: *mut libc::c_int = realloc(
            x as *mut libc::c_void,
            ::std::mem::size_of::<libc::c_int>() as libc::c_ulong,
        ) as *mut libc::c_int;
        ",
        |_, t, _, _| {
            assert_eq!(t[2].var_ty, t[1].var_ty);
            assert_eq!(t[5].var_ty, t[1].var_ty);
            assert_eq!(t[6].var_ty, t[1].var_ty);
            assert_eq!(t[7].var_ty, t[1].var_ty);
        },
    );
}

#[test]
fn test_eq_realloc_bot() {
    // _3 = const 0_usize as *mut libc::c_void (PointerFromExposedAddress)
    // _5 = std::mem::size_of::<i32>()
    // _4 = move _5 as u64 (IntToInt)
    // _2 = realloc(move _3, move _4)
    // _1 = move _2 as *mut i32 (PtrToPtr)
    analyze_fn(
        "
        let mut x: *mut libc::c_int = realloc(
            0 as *mut libc::c_void,
            ::std::mem::size_of::<libc::c_int>() as libc::c_ulong,
        ) as *mut libc::c_int;
        let mut y: *mut libc::c_int = x;
        ",
        |_, t, _, _| {
            assert_eq!(t[1].var_ty, t[2].var_ty);
        },
    );
}

#[test]
fn test_eq_bstr() {
    // _2 = const 0_i32
    // _1 = move _2 as i8 (IntToInt)
    // _4 = &mut _1
    // _3 = &raw const (*_4)
    // _7 = const b"hello\x00"
    // _6 = &raw const (*_7)
    // _5 = move _6 as *const u8 (PointerCoercion(ArrayToPointer))
    // _3 = move _5 as *const i8 (PtrToPtr)
    analyze_fn(
        "
        let mut y: libc::c_char = 0 as libc::c_int as libc::c_char;
        let mut x: *const libc::c_char = &mut y;
        x = b\"hello\\0\" as *const u8 as *const libc::c_char;
        ",
        |x, t, _, _| {
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[5].var_ty, x[1]);
            assert_eq!(t[6].var_ty, x[1]);
            assert_eq!(t[7].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_bstr_bot() {
    // _4 = const b"hello\x00"
    // _3 = &raw const (*_4)
    // _2 = move _3 as *const u8 (PointerCoercion(ArrayToPointer))
    // _1 = move _2 as *const i8 (PtrToPtr)
    analyze_fn(
        "
        let mut x: *const libc::c_char = b\"hello\\0\" as *const u8 as *const libc::c_char;
        let mut y: *const libc::c_char = x;
        ",
        |_, t, _, _| {
            assert_eq!(t[1].var_ty, t[4].var_ty);
            assert_eq!(t[2].var_ty, t[4].var_ty);
            assert_eq!(t[3].var_ty, t[4].var_ty);
        },
    );
}

#[test]
fn test_eq_add() {
    // _3 = const 0_i32
    // _2 = move _3 as i8 (IntToInt)
    // _5 = const 0_i32
    // _4 = move _5 as i8 (IntToInt)
    // _1 = [move _2, move _4]
    // _8 = &mut _1
    // _7 = move _8 as &mut [i8] (PointerCoercion(Unsize))
    // _6 = core::slice::<impl [i8]>::as_mut_ptr(move _7)
    // _10 = _6
    // _9 = move _10 as i64 (PointerExposeAddress)
    // _13 = const 1_i32
    // _12 = move _13 as i64 (IntToInt)
    // _11 = Add(_9, move _12)
    // _14 = _11 as *mut i8 (PointerFromExposedAddress)
    analyze_fn(
        "
        let mut x: [libc::c_char; 2] = [
            0 as libc::c_int as libc::c_char,
            0 as libc::c_int as libc::c_char,
        ];
        let mut y: *mut libc::c_char = x.as_mut_ptr();
        let mut z: libc::c_long = y as libc::c_long;
        let mut w: libc::c_long = z + 1 as libc::c_int as libc::c_long;
        let mut v: *mut libc::c_char = w as *mut libc::c_char;
        ",
        |x, t, _, _| {
            assert_eq!(t[6].var_ty, x[1]);
            assert_eq!(t[7].var_ty, x[1]);
            assert_eq!(t[8].var_ty, x[1]);
            assert_eq!(t[9].var_ty, x[1]);
            assert_eq!(t[10].var_ty, x[1]);
            assert_eq!(t[11].var_ty, x[1]);
            assert_eq!(t[14].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_overflowing_add() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = _2 as i64 (PointerExposeAddress)
    // _6 = const 0_i32
    // _5 = move _6 as i64 (IntToInt)
    // _10 = const 0_i64
    // _9 = core::num::<impl i64>::overflowing_add(_4, move _10) -> [return: bb1, unwind continue]
    // _7 = (_9.0: i64)
    // _8 = (_9.1: bool)
    // _11 = &mut _5
    // (*_11) = _7
    // _13 = _5
    // _12 = move _13 as *mut i32 (PointerFromExposedAddress)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: libc::c_long = y as libc::c_long;
        let mut w: libc::c_long = 0 as libc::c_int as libc::c_long;
        let (fresh0, fresh1) = z.overflowing_add(0 as libc::c_long);
        *&mut w = fresh0;
        let mut v: *mut libc::c_int = w as *mut libc::c_int;
        ",
        |x, t, _, _| {
            assert_eq!(t[11].var_ty, x[5]);

            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[5].var_ty, x[1]);
            assert_eq!(t[7].var_ty, x[1]);
            assert_eq!(t[8].var_ty, x[1]);
            assert_eq!(t[9].var_ty, x[1]);
            assert_eq!(t[12].var_ty, x[1]);
            assert_eq!(t[13].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_eq() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _6 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _5 = Eq(_2, move _6)
    // _4 = move _5 as i32 (IntToInt)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: libc::c_int = (y == 0 as *mut libc::c_int) as libc::c_int;
        ",
        |x, t, _, _| {
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_ne!(t[4].var_ty, x[1]);
            assert_ne!(t[5].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_neg() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = _2 as i64 (PointerExposeAddress)
    // _5 = Neg(_4)
    // _6 = Neg(_5)
    // _7 = _6 as *mut i32 (PointerFromExposedAddress)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: libc::c_long = y as libc::c_long;
        let mut w: libc::c_long = -z;
        let mut v: libc::c_long = -w;
        let mut u: *mut libc::c_int = v as *mut libc::c_int;
        ",
        |x, t, _, _| {
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[5].var_ty, x[1]);
            assert_eq!(t[6].var_ty, x[1]);
            assert_eq!(t[7].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_not() {
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: libc::c_long = y as libc::c_long;
        let mut w: libc::c_long = -z;
        let mut v: libc::c_long = -w;
        let mut u: *mut libc::c_int = v as *mut libc::c_int;
        ",
        |x, t, _, _| {
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[5].var_ty, x[1]);
            assert_eq!(t[6].var_ty, x[1]);
            assert_eq!(t[7].var_ty, x[1]);
        },
    );
}

#[test]
fn test_eq_static() {
    // _3 = const {alloc1: *mut i32}
    // _2 = &mut (*_3)
    // _1 = &raw mut (*_2)
    analyze_fn(
        "
        static mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        ",
        |_, t, _, tcx| {
            let (def_id, _) = find_item("x", tcx);
            let x = VarId::Global(CallStr::Empty, def_id);
            assert_eq!(t[1].var_ty, x);
            assert_eq!(t[2].var_ty, x);
            assert_eq!(t[3].var_ty, x);
        },
    );
}

#[test]
fn test_eq_thread_local_static() {
    // _3 = &/*tls*/ mut foo::x
    // _2 = &mut (*_3)
    // _1 = &raw mut (*_2)
    analyze_fn(
        "
        #[thread_local]
        static mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        ",
        |_, t, _, tcx| {
            let (def_id, _) = find_item("x", tcx);
            let x = VarId::Global(CallStr::Empty, def_id);
            assert_eq!(t[1].var_ty, x);
            assert_eq!(t[2].var_ty, x);
            assert_eq!(t[3].var_ty, x);
        },
    );
}

#[test]
fn test_eq_extern_static() {
    // _3 = const {alloc1: *mut i32}
    // _2 = &mut (*_3)
    // _1 = &raw mut (*_2)
    analyze_fn(
        "
        extern \"C\" { static mut x: libc::c_int; }
        let mut y: *mut libc::c_int = &mut x;
        ",
        |_, t, _, _| {
            assert_eq!(t[1].var_ty, t[3].var_ty);
            assert_eq!(t[2].var_ty, t[3].var_ty);
        },
    );
}

#[test]
fn test_static_eq() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = const {alloc1: *mut *mut i32}
    // (*_4) = move _2
    analyze_fn(
        "
        static mut x: *mut libc::c_int = 0 as *const libc::c_int as *mut libc::c_int;
        let mut y: libc::c_int = 0 as libc::c_int;
        x = &mut y;
        ",
        |x, t, res, tcx| {
            let (xx, xt) = get_xt(CallStr::Empty, "x", &res, tcx);
            assert_eq!(t[4].var_ty, xx);
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(xt.var_ty, x[1]);
        },
    );
}

#[test]
fn test_static2() {
    analyze_fn(
        "
        static mut x: libc::c_int = 0 as libc::c_int;
        static mut y: *mut libc::c_int = unsafe {
            &x as *const libc::c_int as *mut libc::c_int
        };
        ",
        |_, _, res, tcx| {
            let (xx, _) = get_xt(CallStr::Empty, "x", &res, tcx);
            let (_, yt) = get_xt(CallStr::Empty, "y", &res, tcx);
            assert_eq!(yt.var_ty, xx);
        },
    );
}

#[test]
fn test_fn_arg() {
    // _1 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _2 = foo::g(move _3)
    analyze_fn(
        "
        fn g(mut x: *mut libc::c_int) {}
        let mut x: libc::c_int = 0;
        g(&mut x);
        ",
        |x, t, res, tcx| {
            let (f, _) = find_item("foo", tcx);
            let (_, gt) = get_xts(
                CallStr::Single(f, BasicBlock::from_usize(0)),
                "g",
                &res,
                tcx,
            );
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(gt[1].var_ty, x[1]);
        },
    );
}

#[test]
fn test_fn_ret() {
    // g
    // _0 = _1
    //
    // f
    // _1 = const 0_i32
    // _4 = &mut _1
    // _3 = &raw mut (*_4)
    // _2 = foo::g(move _3)
    analyze_fn(
        "
        fn g(mut x: *mut libc::c_int) -> *mut libc::c_int {
            return x;
        }
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = g(&mut x);
        ",
        |x, t, res, tcx| {
            let (f, _) = find_item("foo", tcx);
            let (_, gt) = get_xts(
                CallStr::Single(f, BasicBlock::from_usize(0)),
                "g",
                &res,
                tcx,
            );
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(gt[0].var_ty, x[1]);
            assert_eq!(gt[1].var_ty, x[1]);
        },
    );
}

#[test]
fn test_fn_ptr() {
    // g
    // _0 = _1
    //
    // f
    // _2 = foo::g as fn(*mut i32) -> *mut i32 (PointerCoercion(ReifyFnPointer))
    // _1 = std::option::Option::<fn(*mut i32) -> *mut i32>::Some(move _2)
    // _3 = const 0_i32
    // _5 = std::option::Option::<fn(*mut i32) -> *mut i32>::unwrap(_1)
    // _7 = &mut _3
    // _6 = &raw mut (*_7)
    // _4 = move _5(move _6)
    analyze_fn(
        "
        fn g(mut x: *mut libc::c_int) -> *mut libc::c_int {
            return x;
        }
        let mut h: Option::<fn(*mut libc::c_int) -> *mut libc::c_int> = Some(
            g as fn(*mut libc::c_int) -> *mut libc::c_int,
        );
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = h.unwrap()(&mut x);
        ",
        |x, t, res, tcx| {
            let (_, gt) = get_xt(CallStr::Empty, "g", &res, tcx);
            let (_, gts) = get_xts(CallStr::Empty, "g", &res, tcx);
            assert_eq!(t[1].fn_ty, gt.fn_ty);
            assert_eq!(t[2].fn_ty, gt.fn_ty);
            assert_eq!(t[5].fn_ty, gt.fn_ty);
            assert_eq!(t[4].var_ty, x[3]);
            assert_eq!(t[6].var_ty, x[3]);
            assert_eq!(t[7].var_ty, x[3]);
            assert_eq!(gts[0].var_ty, x[3]);
            assert_eq!(gts[1].var_ty, x[3]);
        },
    );
}

#[test]
fn test_fn_ptrs() {
    // g
    // _0 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    //
    // h
    // _0 = _1
    //
    // f
    // _1 = const 0_i32
    // _3 = _1
    // _4 = foo::g as fn(*mut i32) -> *mut i32 (PointerCoercion(ReifyFnPointer))
    // _2 = std::option::Option::<fn(*mut i32) -> *mut i32>::Some(move _4)
    // _5 = foo::h as fn(*mut i32) -> *mut i32 (PointerCoercion(ReifyFnPointer))
    // _2 = std::option::Option::<fn(*mut i32) -> *mut i32>::Some(move _5)
    // _8 = _2
    // _7 = std::option::Option::<fn(*mut i32) -> *mut i32>::unwrap(move _8)
    // _10 = &mut _1
    // _9 = &raw mut (*_10)
    // _6 = move _7(move _9)
    analyze_fn(
        "
        fn g(mut x: *mut libc::c_int) -> *mut libc::c_int {
            return 0 as *mut libc::c_int;
        }
        fn h(mut x: *mut libc::c_int) -> *mut libc::c_int {
            return x;
        }
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut i: Option::<fn(*mut libc::c_int) -> *mut libc::c_int> = if x
            != 0
        {
            Some(g as fn(*mut libc::c_int) -> *mut libc::c_int)
        } else {
            Some(h as fn(*mut libc::c_int) -> *mut libc::c_int)
        };
        let mut y: *mut libc::c_int = i.unwrap()(&mut x);
        ",
        |x, t, res, tcx| {
            let (_, gt) = get_xt(CallStr::Empty, "g", &res, tcx);
            let (_, gts) = get_xts(CallStr::Empty, "g", &res, tcx);
            let (_, ht) = get_xt(CallStr::Empty, "h", &res, tcx);
            let (_, hts) = get_xts(CallStr::Empty, "h", &res, tcx);

            assert_eq!(t[6].var_ty, x[1]);
            assert_eq!(t[9].var_ty, x[1]);
            assert_eq!(t[10].var_ty, x[1]);
            assert_eq!(gts[0].var_ty, x[1]);
            assert_eq!(gts[1].var_ty, x[1]);
            assert_eq!(hts[0].var_ty, x[1]);
            assert_eq!(hts[1].var_ty, x[1]);

            assert_eq!(t[2].fn_ty, gt.fn_ty);
            assert_eq!(t[4].fn_ty, gt.fn_ty);
            assert_eq!(t[5].fn_ty, gt.fn_ty);
            assert_eq!(t[7].fn_ty, gt.fn_ty);
            assert_eq!(t[8].fn_ty, gt.fn_ty);
            assert_eq!(ht.fn_ty, gt.fn_ty);
        },
    );
}

#[test]
fn test_offset() {
    // _1 = [const 0_i32; 2]
    // _4 = &mut _1
    // _3 = move _4 as &mut [i32] (PointerCoercion(Unsize))
    // _2 = core::slice::<impl [i32]>::as_mut_ptr(move _3)
    // _6 = _2
    // _8 = const 1_i32
    // _7 = move _8 as isize (IntToInt)
    // _5 = std::ptr::mut_ptr::<impl *mut i32>::offset(move _6, move _7)
    // _2 = move _5
    analyze_fn(
        "
        let mut x: [libc::c_int; 2] = [0; 2];
        let mut y: *mut libc::c_int = x.as_mut_ptr();
        y = y.offset(1 as libc::c_int as isize);
        ",
        |x, t, _, _| {
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[5].var_ty, x[1]);
            assert_eq!(t[6].var_ty, x[1]);
        },
    );
}

#[test]
fn test_copy_for_deref() {
    // _1 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _5 = &mut _2
    // _4 = &raw mut (*_5)
    // _6 = const 0_i32
    // _8 = &mut _6
    // _7 = &raw mut (*_8)
    // _9 = deref_copy (*_4)
    // (*_9) = move _7
    analyze_fn(
        "
        let mut x: *mut libc::c_int = 0 as *mut libc::c_int;
        let mut y: *mut *mut libc::c_int = &mut x;
        let mut z: *mut *mut *mut libc::c_int = &mut y;
        let mut w: libc::c_int = 0 as libc::c_int;
        **z = &mut w;
        ",
        |x, t, _, _| {
            assert_eq!(t[4].var_ty, x[2]);
            assert_eq!(t[5].var_ty, x[2]);

            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[9].var_ty, x[1]);

            assert_eq!(t[1].var_ty, x[6]);
            assert_eq!(t[7].var_ty, x[6]);
            assert_eq!(t[8].var_ty, x[6]);
        },
    );
}

#[test]
fn test_copy_for_deref_arr() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _6 = &mut _2
    // _5 = &raw mut (*_6)
    // _4 = [move _5]
    // _9 = const 0_i32
    // _8 = move _9 as usize (IntToInt)
    // _10 = const 1_usize
    // _11 = Lt(_8, _10)
    // _12 = deref_copy _4[_8]
    // _7 = (*_12)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: [*mut *mut libc::c_int; 1] = [&mut y];
        let mut w: *mut libc::c_int = *z[0 as libc::c_int as usize];
        ",
        |x, t, _, _| {
            assert_eq!(t[4].var_ty, x[2]);
            assert_eq!(t[5].var_ty, x[2]);
            assert_eq!(t[6].var_ty, x[2]);
            assert_eq!(t[12].var_ty, x[2]);

            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[7].var_ty, x[1]);
        },
    );
}

#[test]
fn test_write_volatile() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = _2 as i64 (PointerExposeAddress)
    // _6 = &mut _4
    // _5 = &raw mut (*_6)
    // _8 = const 0_i32
    // _7 = move _8 as i64 (IntToInt)
    // _11 = &mut _7
    // _10 = &raw mut (*_11)
    // _12 = (*_5)
    // _9 = std::ptr::write_volatile::<i64>(move _10, move _12)
    analyze_fn(
        "
        let mut z: libc::c_int = 0 as libc::c_int;
        let mut w: *mut libc::c_int = &mut z;
        let mut v: libc::c_long = w as libc::c_long;
        let mut y: *mut libc::c_long = &mut v;
        let mut x: libc::c_long = 0 as libc::c_int as libc::c_long;
        ::std::ptr::write_volatile(&mut x as *mut libc::c_long, *y);
        ",
        |x, t, _, _| {
            assert_eq!(t[5].var_ty, x[4]);
            assert_eq!(t[6].var_ty, x[4]);

            assert_eq!(t[10].var_ty, x[7]);
            assert_eq!(t[11].var_ty, x[7]);

            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[7].var_ty, x[1]);
            assert_eq!(t[12].var_ty, x[1]);
        },
    );
}

#[test]
fn test_read_volatile() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = _2 as i64 (PointerExposeAddress)
    // _7 = &mut _4
    // _6 = &raw mut (*_7)
    // _11 = &_4
    // _10 = &raw const (*_11)
    // _9 = std::ptr::read_volatile::<i64>(move _10)
    // _13 = const 0_i32
    // _12 = move _13 as i64 (IntToInt)
    // _8 = Add(move _9, move _12)
    // _5 = std::ptr::write_volatile::<i64>(move _6, move _8)
    // _15 = _4
    // _14 = move _15 as *mut i32 (PointerFromExposedAddress)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y: *mut libc::c_int = &mut x;
        let mut z: libc::c_long = y as libc::c_long;
        ::std::ptr::write_volatile(
            &mut z as *mut libc::c_long,
            ::std::ptr::read_volatile::<libc::c_long>(&z as *const libc::c_long)
                + 0 as libc::c_int as libc::c_long,
        );
        let mut w: *mut libc::c_int = z as *mut libc::c_int;
        ",
        |x, t, _, _| {
            assert_eq!(t[6].var_ty, x[4]);
            assert_eq!(t[7].var_ty, x[4]);
            assert_eq!(t[10].var_ty, x[4]);
            assert_eq!(t[11].var_ty, x[4]);

            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[8].var_ty, x[1]);
            assert_eq!(t[9].var_ty, x[1]);
            assert_eq!(t[14].var_ty, x[1]);
            assert_eq!(t[15].var_ty, x[1]);
        },
    );
}

#[test]
fn test_variadic() {
    // h
    // _5 = &mut _1
    // _4 = <std::ffi::VaList<'_, '_> as std::ops::DerefMut>::deref_mut(move _5)
    // _3 = _4
    // _2 = std::ffi::VaListImpl::<'_>::arg::<*mut i32>(move _3)
    // _0 = _2
    //
    // g
    // _9 = const false
    // _5 = &_2
    // _4 = <std::ffi::VaListImpl<'_> as std::clone::Clone>::clone(move _5)
    // _9 = const true
    // _3 = move _4
    // _8 = &mut _3
    // _7 = std::ffi::VaListImpl::<'_>::as_va_list(move _8)
    // _6 = foo::g::h(move _7)
    // _9 = const false
    // _5 = &mut _1
    //
    // f
    // _1 = const 0_i32
    // _3 = const 0_i32
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _2 = foo::g(move _3, move _4)
    analyze_fn(
        "
        unsafe extern \"C\" fn g(mut x: libc::c_int, mut args: ...) {
            unsafe fn h(mut y: ::std::ffi::VaList) -> *mut libc::c_int {
                let mut z: *mut libc::c_int = y.arg::<*mut libc::c_int>();
                return z;
            }
            let mut y: ::std::ffi::VaListImpl;
            y = args.clone();
            let mut z: *mut libc::c_int = h(y.as_va_list());
        }
        let mut x: libc::c_int = 0 as libc::c_int;
        g(0 as libc::c_int, &mut x as *mut libc::c_int);
        ",
        |fx, ft, res, tcx| {
            let (f, _) = find_item("foo", tcx);
            let (gx, gt) = get_xts(
                CallStr::Single(f, BasicBlock::from_usize(0)),
                "g",
                &res,
                tcx,
            );
            let (g, _) = find_item("g", tcx);
            let (hx, ht) = get_xts(
                CallStr::Single(g, BasicBlock::from_usize(2)),
                "h",
                &res,
                tcx,
            );

            assert_eq!(ht[3].var_ty, hx[1]);
            assert_eq!(ht[4].var_ty, hx[1]);
            assert_eq!(ht[5].var_ty, hx[1]);

            assert_eq!(gt[8].var_ty, gx[3]);

            assert_eq!(gt[5].var_ty, gx[2]);

            assert_eq!(ft[4].var_ty, fx[1]);
            assert_eq!(ft[5].var_ty, fx[1]);
            assert_eq!(gt[2].var_ty, fx[1]);
            assert_eq!(gt[3].var_ty, fx[1]);
            assert_eq!(gt[4].var_ty, fx[1]);
            assert_eq!(gt[6].var_ty, fx[1]);
            assert_eq!(gt[7].var_ty, fx[1]);
            assert_eq!(ht[0].var_ty, fx[1]);
            assert_eq!(ht[1].var_ty, fx[1]);
            assert_eq!(ht[2].var_ty, fx[1]);
        },
    );
}

#[test]
fn test_memcpy() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _4 = const 0_usize as *mut i32 (PointerFromExposedAddress)
    // _8 = &mut _4
    // _7 = &raw mut (*_8)
    // _6 = move _7 as *mut libc::c_void (PtrToPtr)
    // _11 = &mut _2
    // _10 = &raw mut (*_11)
    // _9 = move _10 as *const libc::c_void (PtrToPtr)
    // _14 = std::mem::size_of::<*mut i32>()
    // _13 = move _14 as u64 (IntToInt)
    // _12 = move _13 as usize (IntToInt)
    // _5 = libc::memcpy(move _6, move _9, move _12)
    analyze_fn(
        "
        let mut x: libc::c_int = 0 as libc::c_int;
        let mut y1: *mut libc::c_int = &mut x;
        let mut y2: *mut libc::c_int = 0 as *mut libc::c_int;
        libc::memcpy(
            &mut y2 as *mut *mut libc::c_int as *mut libc::c_void,
            &mut y1 as *mut *mut libc::c_int as *const libc::c_void,
            ::std::mem::size_of::<*mut libc::c_int>() as libc::c_ulong as libc::size_t,
        );
        ",
        |x, t, _, _| {
            assert_eq!(t[5].var_ty, x[4]);
            assert_eq!(t[6].var_ty, x[4]);
            assert_eq!(t[7].var_ty, x[4]);
            assert_eq!(t[8].var_ty, x[4]);

            assert_eq!(t[9].var_ty, x[2]);
            assert_eq!(t[10].var_ty, x[2]);
            assert_eq!(t[11].var_ty, x[2]);

            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(t[4].var_ty, x[1]);
        },
    );
}

#[test]
fn test_fn_sensitivity() {
    // _1 = const 0_i32
    // _2 = const 0_i32
    // _5 = &mut _1
    // _4 = &raw mut (*_5)
    // _3 = foo::g(move _4)
    // _8 = &mut _2
    // _7 = &raw mut (*_8)
    // _6 = foo::g(move _7)
    analyze_fn(
        "
        fn g(mut x: *mut libc::c_int) {}
        let mut x: libc::c_int = 0;
        let mut y: libc::c_int = 0;
        g(&mut x);
        g(&mut y);
        ",
        |x, t, res, tcx| {
            let (f, _) = find_item("foo", tcx);
            let (_, gt0) = get_xts(
                CallStr::Single(f, BasicBlock::from_usize(0)),
                "g",
                &res,
                tcx,
            );
            let (_, gt1) = get_xts(
                CallStr::Single(f, BasicBlock::from_usize(1)),
                "g",
                &res,
                tcx,
            );
            assert_eq!(t[4].var_ty, x[1]);
            assert_eq!(t[5].var_ty, x[1]);
            assert_eq!(gt0[1].var_ty, x[1]);
            assert_eq!(t[7].var_ty, x[2]);
            assert_eq!(t[8].var_ty, x[2]);
            assert_eq!(gt1[1].var_ty, x[2]);
            assert_ne!(x[1], x[2]);
        },
    );
}
