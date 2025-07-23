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

    run_compiler(orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        let item_span = krate.items.first().unwrap().span;
        let suggestion = AstSuggestion {
            span: item_span,
            action: astutil::AstEdit::AppendAfterItem(item!("{}", item_code)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx.sess.source_map(), vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_replace_item() {
    let orig_code = "fn main() {}";
    let item_code = "fn new_item() {}";
    let expected_code = item_code;

    run_compiler(orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        let item_span = krate.items.first().unwrap().span;
        let suggestion = AstSuggestion {
            span: item_span,
            action: astutil::AstEdit::ReplaceItem(item!("{}", item_code)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx.sess.source_map(), vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_remove_field_def() {
    let orig_code = "struct Human { brain: i32, heart: i32 }";
    let expected_code = "struct Human { heart: i32 }";

    run_compiler(orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        let ItemKind::Struct(VariantData::Struct { fields, .. }, _) =
            &krate.items.first().unwrap().kind
        else {
            panic!("Expected a struct item");
        };
        let item_span = krate.items.first().unwrap().span;
        let field_span = fields.first().unwrap().span;
        // print_span_info(&krate.items.first().unwrap().span);
        // print_span_info(&fields.first().unwrap().span);
        let suggestion = AstSuggestion {
            span: item_span,
            action: astutil::AstEdit::RemoveFieldDef(field_span),
        };
        let mut mut_visitor = TransformVisitor::new(tcx.sess.source_map(), vec![suggestion]);
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

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        let ItemKind::Fn(box Fn { body: Some(b), .. }) = &krate.items.first().unwrap().kind else {
            panic!("Expected a function item");
        };
        let block_span = b.span;
        let suggestion = AstSuggestion {
            span: block_span,
            action: astutil::AstEdit::PrependToBlock(stmt!("{}", prep_stmt)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx.sess.source_map(), vec![suggestion]);
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

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        let ItemKind::Fn(box rustc_ast::Fn { body: Some(b), .. }) =
            &krate.items.first().unwrap().kind
        else {
            panic!("Expected a function item");
        };
        let stmt_span = b.stmts.first().unwrap().span;
        let suggestion = AstSuggestion {
            span: stmt_span,
            action: astutil::AstEdit::ReplaceStmt(stmt!("{}", repl_stmt)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx.sess.source_map(), vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_remove_stmt() {
    let orig_code = format!("fn main() {{ let x = 5; }}");
    let expected_code = format!("fn main() {{ }}");

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        let ItemKind::Fn(box rustc_ast::Fn { body: Some(b), .. }) =
            &krate.items.first().unwrap().kind
        else {
            panic!("Expected a function item");
        };
        let stmt_span = b.stmts.first().unwrap().span;
        let suggestion = AstSuggestion {
            span: stmt_span,
            action: astutil::AstEdit::RemoveStmt,
        };
        let mut mut_visitor = TransformVisitor::new(tcx.sess.source_map(), vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_replace_pat() {
    let repl_pat = "Chim(chak)";
    let orig_code = format!("fn main() {{ let x = 5; }}");
    let expected_code = format!("fn main() {{ let Chim(chak) = 5; }}");

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        let ItemKind::Fn(box Fn { body: Some(b), .. }) = &krate.items.first().unwrap().kind else {
            panic!("Expected a function item");
        };
        let StmtKind::Let(local) = &b.stmts.first().unwrap().kind else {
            panic!("Expected a let statement");
        };
        let pat_span = local.pat.span;
        let suggestion = AstSuggestion {
            span: pat_span,
            action: astutil::AstEdit::ReplacePat(pat!("{}", repl_pat)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx.sess.source_map(), vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_replace_expr() {
    let repl_expr = "10";
    let orig_code = format!("fn main() {{ let x = 5; }}");
    let expected_code = format!("fn main() {{ let x = 10; }}");

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        let ItemKind::Fn(box Fn { body: Some(b), .. }) = &krate.items.first().unwrap().kind else {
            panic!("Expected a function item");
        };
        let StmtKind::Let(local) = &b.stmts.first().unwrap().kind else {
            panic!("Expected a let statement");
        };
        let expr_span = local.kind.init().unwrap().span;
        let suggestion = AstSuggestion {
            span: expr_span,
            action: astutil::AstEdit::ReplaceExpr(expr!("{}", repl_expr)),
        };
        let mut mut_visitor = TransformVisitor::new(tcx.sess.source_map(), vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_remove_expr_field() {
    let orig_code = format!("fn main() {{ let x = Human {{ brain: 1, heart: 1 }}; }}");
    let expected_code = format!("fn main() {{ let x = Human {{ heart: 1 }}; }}");

    run_compiler(&orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        let ItemKind::Fn(box Fn { body: Some(b), .. }) = &krate.items.first().unwrap().kind else {
            panic!("Expected a function item");
        };
        let StmtKind::Let(local) = &b.stmts.first().unwrap().kind else {
            panic!("Expected a let statement");
        };
        let ExprKind::Struct(struct_expr) = &local.kind.init().unwrap().kind else {
            panic!("Expected a struct expression");
        };
        let expr_span = local.kind.init().unwrap().span;
        let field_span = struct_expr.fields.first().unwrap().span;
        let suggestion = AstSuggestion {
            span: expr_span,
            action: astutil::AstEdit::RemoveExprField(field_span),
        };
        let mut mut_visitor = TransformVisitor::new(tcx.sess.source_map(), vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}

#[test]
fn test_remove_field_attr() {
    let orig_code = "struct Human {\n#[rotten]\n#[fresh]\nbrain: i32,\nheart: i32 }";
    let expected_code = "struct Human {\n#[fresh]\nbrain: i32,\nheart: i32 }";

    run_compiler(orig_code, |tcx| {
        let mut krate = parse_crate(orig_code.to_string());
        let ItemKind::Struct(VariantData::Struct { fields, .. }, _) =
            &krate.items.first().unwrap().kind
        else {
            panic!("Expected a struct item");
        };
        let field_def_span = fields.first().unwrap().span;
        let attr_span = fields.first().unwrap().attrs.first().unwrap().span;
        let suggestion = AstSuggestion {
            span: field_def_span,
            action: astutil::AstEdit::RemoveFieldAttr(attr_span),
        };
        let mut mut_visitor = TransformVisitor::new(tcx.sess.source_map(), vec![suggestion]);
        mut_visitor.visit_crate(&mut krate);
        assert_eq_crate(&krate, &expected_code);
    });
}
