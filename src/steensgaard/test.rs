use super::*;

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    let input = compile_util::str_to_input(code);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, f);
}

fn analyze_fn<F>(code: &str, f: F)
where F: FnOnce(Vec<VarId>, Vec<Type>, AnalysisResults, TyCtxt<'_>) + Send {
    let name = "foo";
    let code = format!(
        "
        extern crate libc;
        extern \"C\" {{
            fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
        }}
        unsafe fn {}() {{
            {}
        }}
    ",
        name, code
    );
    run_compiler(&code, |tcx| {
        let res = analyze(tcx);
        let (def_id, n) = find_item(name, tcx);
        let x: Vec<_> = (0..n).map(|i| res.local(def_id, i)).collect();
        let t: Vec<_> = x.iter().map(|x| res.var_ty(*x)).collect();
        f(x, t, res, tcx);
    });
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
fn test_eq_alloc() {
    // _1 = const 0_i32
    // _3 = &mut _1
    // _2 = &raw mut (*_3)
    // _6 = std::mem::size_of::<i32>() -> [return: bb1, unwind continue]
    // _5 = move _6 as u64 (IntToInt)
    // _4 = malloc(move _5) -> [return: bb2, unwind continue]
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
    // _4 = std::mem::size_of::<i32>() -> [return: bb1, unwind continue]
    // _3 = move _4 as u64 (IntToInt)
    // _2 = malloc(move _3) -> [return: bb2, unwind continue]
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
fn test_eq_add() {
    // _3 = const 0_i32
    // _2 = move _3 as i8 (IntToInt)
    // _5 = const 0_i32
    // _4 = move _5 as i8 (IntToInt)
    // _1 = [move _2, move _4]
    // _8 = &mut _1
    // _7 = move _8 as &mut [i8] (PointerCoercion(Unsize))
    // _6 = core::slice::<impl [i8]>::as_mut_ptr(move _7) -> [return: bb1, unwind continue]
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
            let x = VarId::Global(def_id);
            assert_eq!(t[1].var_ty, x);
            assert_eq!(t[2].var_ty, x);
            assert_eq!(t[3].var_ty, x);
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
            let (def_id, _) = find_item("x", tcx);
            let x_id = VarId::Global(def_id);
            let x_ty = res.var_ty(x_id);
            assert_eq!(t[4].var_ty, x_id);
            assert_eq!(t[2].var_ty, x[1]);
            assert_eq!(t[3].var_ty, x[1]);
            assert_eq!(x_ty.var_ty, x[1]);
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
            let (def_id, _) = find_item("x", tcx);
            let x_id = VarId::Global(def_id);
            let (def_id, _) = find_item("y", tcx);
            let y_id = VarId::Global(def_id);
            let y_ty = res.var_ty(y_id);
            assert_eq!(y_ty.var_ty, x_id);
        },
    );
}