use rustc_middle::ty::TyCtxt;

use super::*;
use crate::*;

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    let input = compile_util::str_to_input(code);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, f).unwrap();
}

fn analyze_fn_with_params<F>(params: &str, code: &str, f: F)
where F: FnOnce(AnalysisResults, TyCtxt<'_>) + Send {
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
        f(res, tcx);
    });
}

fn analyze_fn<F>(code: &str, f: F)
where F: FnOnce(AnalysisResults, TyCtxt<'_>) + Send {
    analyze_fn_with_params("", code, f);
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
        |_, _| {},
    );
}
