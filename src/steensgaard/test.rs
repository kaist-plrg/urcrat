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
    // return
    run_compiler(
        "
        extern crate libc;
        unsafe fn f() {
            let mut y: libc::c_int = 0 as libc::c_int;
            let mut x: *mut libc::c_int = &mut y;
        }
        ",
        |tcx| {
            let res = analyze(tcx);
            let f = find_fn("f", tcx);

            let x1 = res.vars[&VarId::Local(f, 1)];

            let x2 = res.vars[&VarId::Local(f, 2)];
            let VarType::Ref(t2) = res.var_tys[&x2] else { panic!() };
            assert_eq!(t2.var_ty, x1);

            let x3 = res.vars[&VarId::Local(f, 3)];
            let VarType::Ref(t3) = res.var_tys[&x3] else { panic!() };
            assert_eq!(t3.var_ty, x1);

            assert_ne!(x2, x3);
        },
    );
}
