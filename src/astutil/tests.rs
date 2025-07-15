use rustc_ast::{mut_visit::MutVisitor, *};
use rustc_ast_pretty::pprust::{crate_to_string_for_macros, pat_to_string};
use rustc_middle::ty::TyCtxt;
use rustc_span::{BytePos, Span, SyntaxContext};

use crate::{
    astutil::{self, parse::*, AstSuggestion, TransformVisitor},
    compile_util,
};

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    let input = compile_util::str_to_input(code);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, f).unwrap_or_else(|e| e.raise());
}

fn print_span_info(span: &Span) {
    let data = span.data();
    if !data.ctxt.is_root() {
        println!("Span is not root: {:?}", data.ctxt);
    }
    println!(
        "Span::new({:?}, {:?}, SyntaxContext::root(), {:?})",
        data.lo, data.hi, data.parent
    );
}

#[inline]
fn assert_eq_crate(krate: &Crate, exp: &str) {
    let right_crate = parse_crate(exp.to_string());
    assert_eq!(
        crate_to_string_for_macros(krate),
        crate_to_string_for_macros(&right_crate)
    );
}

#[test]
fn test_append_after_item() {
    let orig_code = "fn main() {}";
    let item_code = "fn new_item() {}";
    let expected_code = format!("{}\n{}", orig_code, item_code);

    let target_span = Span::new(BytePos(0), BytePos(12), SyntaxContext::root(), None);

    run_compiler(orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        println!("Original crate: {}", crate_to_string_for_macros(&krate));
        // let first_item = krate.items.first().unwrap();
        // println!("Original crate: {:#?}", krate);
        // print_span_info(&first_item.span);
        let suggestion = AstSuggestion {
            span: target_span,
            action: astutil::AstEdit::AppendAfterItem(item!("{}", item_code)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx, vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_replace_item() {
    let orig_code = "fn main() {}";
    let item_code = "fn new_item() {}";
    let expected_code = item_code;

    let target_span = Span::new(BytePos(0), BytePos(12), SyntaxContext::root(), None);

    run_compiler(orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        println!("Original crate: {}", crate_to_string_for_macros(&krate));
        // let first_item = krate.items.first().unwrap();
        // println!("Original crate: {:#?}", krate);
        // print_span_info(&first_item.span);
        let suggestion = AstSuggestion {
            span: target_span,
            action: astutil::AstEdit::ReplaceItem(item!("{}", item_code)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx, vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_remove_field_def() {
    let orig_code = "struct Human { brain: i32, heart: i32 }";
    let expected_code = "struct Human { heart: i32 }";

    // Struct item's span
    let target_span = Span::new(BytePos(0), BytePos(39), SyntaxContext::root(), None);
    // Field definition's span
    let field_span = Span::new(BytePos(15), BytePos(25), SyntaxContext::root(), None);

    run_compiler(orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        // let ItemKind::Struct(VariantData::Struct { fields, .. }, _) =
        //     &krate.items.first().unwrap().kind
        // else {
        //     panic!("Expected a struct item");
        // };
        // print_span_info(&krate.items.first().unwrap().span);
        // print_span_info(&fields.first().unwrap().span);
        let suggestion = AstSuggestion {
            span: target_span,
            action: astutil::AstEdit::RemoveFieldDef(field_span),
        };
        let mut mut_visitor = TransformVisitor::new(tcx, vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_prepend_to_block() {
    let orig_stmt = "let x = 5;";
    let prep_stmt = "let y = 10;";
    let orig_code = format!("fn main() {{ {} }}", orig_stmt);
    let expected_code = format!("fn main() {{ {} {} }}", prep_stmt, orig_stmt);

    let target_span = Span::new(BytePos(10), BytePos(24), SyntaxContext::root(), None);

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        // let ItemKind::Fn(box Fn { body: Some(b), .. }) = &krate.items.first().unwrap().kind else {
        //     panic!("Expected a function item");
        // };
        // print_span_info(&b.span);
        let suggestion = AstSuggestion {
            span: target_span,
            action: astutil::AstEdit::PrependToBlock(stmt!("{}", prep_stmt)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx, vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_replace_stmt() {
    let orig_stmt = "let x = 5;";
    let repl_stmt = "let y = 10;";
    let orig_code = format!("fn main() {{ {} }}", orig_stmt);
    let expected_code = format!("fn main() {{ {} }}", repl_stmt);

    let target_span = Span::new(BytePos(12), BytePos(22), SyntaxContext::root(), None);

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        // let ItemKind::Fn(box rustc_ast::Fn { body: Some(b), .. }) =
        //     &krate.items.first().unwrap().kind
        // else {
        //     panic!("Expected a function item");
        // };
        // println!(
        //     "Span of the first statement: {:?}",
        //     b.stmts.first().unwrap().span.data()
        // );
        // print_span_info(&b.stmts.first().unwrap().span);
        let suggestion = AstSuggestion {
            span: target_span,
            action: astutil::AstEdit::ReplaceStmt(stmt!("{}", repl_stmt)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx, vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_remove_stmt() {
    let orig_code = format!("fn main() {{ let x = 5; }}");
    let expected_code = format!("fn main() {{ }}");

    let target_span = Span::new(BytePos(12), BytePos(22), SyntaxContext::root(), None);

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        let suggestion = AstSuggestion {
            span: target_span,
            action: astutil::AstEdit::RemoveStmt,
        };
        let mut mut_visitor = TransformVisitor::new(tcx, vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_replace_pat() {
    let repl_pat = "Chim(chak)";
    let orig_code = format!("fn main() {{ let x = 5; }}");
    let expected_code = format!("fn main() {{ let Chim(chak) = 5; }}");

    let target_span = Span::new(BytePos(16), BytePos(17), SyntaxContext::root(), None);

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        // let ItemKind::Fn(box Fn { body: Some(b), .. }) = &krate.items.first().unwrap().kind else {
        //     panic!("Expected a function item");
        // };
        // let StmtKind::Let(local) = &b.stmts.first().unwrap().kind else {
        //     panic!("Expected a let statement");
        // };
        // println!("Span of the pat: {:?}", print_span_info(&local.pat.span));
        let suggestion = AstSuggestion {
            span: target_span,
            action: astutil::AstEdit::ReplacePat(pat!("{}", repl_pat)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx, vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_replace_expr() {
    let repl_expr = "10";
    let orig_code = format!("fn main() {{ let x = 5; }}");
    let expected_code = format!("fn main() {{ let x = 10; }}");

    let target_span = Span::new(BytePos(20), BytePos(21), SyntaxContext::root(), None);

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        // let ItemKind::Fn(box Fn { body: Some(b), .. }) = &krate.items.first().unwrap().kind else {
        //     panic!("Expected a function item");
        // };
        // let StmtKind::Let(local) = &b.stmts.first().unwrap().kind else {
        //     panic!("Expected a let statement");
        // };
        // println!(
        //     "Span of the expression: {:?}",
        //     print_span_info(&local.kind.init().unwrap().span)
        // );
        let suggestion = AstSuggestion {
            span: target_span,
            action: astutil::AstEdit::ReplaceExpr(expr!("{}", repl_expr)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx, vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_remove_expr_field() {
    let orig_code = format!("fn main() {{ let x = Human {{ brain: 1, heart: 1 }}; }}");
    let expected_code = format!("fn main() {{ let x = Human {{ heart: 1 }}; }}");

    let target_span = Span::new(BytePos(20), BytePos(48), SyntaxContext::root(), None);
    let field_span = Span::new(BytePos(28), BytePos(36), SyntaxContext::root(), None);

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        // let ItemKind::Fn(box Fn { body: Some(b), .. }) = &krate.items.first().unwrap().kind else {
        //     panic!("Expected a function item");
        // };
        // let StmtKind::Let(local) = &b.stmts.first().unwrap().kind else {
        //     panic!("Expected a let statement");
        // };
        // let ExprKind::Struct(struct_expr) = &local.kind.init().unwrap().kind else {
        //     panic!("Expected a struct expression");
        // };
        // print_span_info(&local.kind.init().unwrap().span); // Expression span
        // print_span_info(&struct_expr.fields.first().unwrap().span); // Field span
        let suggestion = AstSuggestion {
            span: target_span,
            action: astutil::AstEdit::RemoveExprField(field_span),
        };
        let mut mut_visitor = TransformVisitor::new(tcx, vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_remove_field_attr() {
    let orig_code = "struct Human {\n#[rotten]\nbrain: i32,\nheart: i32 }";
    let expected_code = "struct Human {\nbrain: i32,\nheart: i32 }";

    // Struct item's span
    let target_span = Span::new(BytePos(25), BytePos(35), SyntaxContext::root(), None);
    // Field definition's span
    let attr_span = Span::new(BytePos(15), BytePos(24), SyntaxContext::root(), None);

    run_compiler(orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        // let ItemKind::Struct(VariantData::Struct { fields, .. }, _) =
        //     &krate.items.first().unwrap().kind
        // else {
        //     panic!("Expected a struct item");
        // };
        // print_span_info(&fields.first().unwrap().span);
        // print_span_info(&fields.first().unwrap().attrs.first().unwrap().span);
        let suggestion = AstSuggestion {
            span: target_span,
            action: astutil::AstEdit::RemoveFieldAttr(attr_span),
        };
        let mut mut_visitor = TransformVisitor::new(tcx, vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}
