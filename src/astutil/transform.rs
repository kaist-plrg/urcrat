use rustc_ast::{
    ast::*,
    mut_visit::{self, MutVisitor},
    ptr::P,
    token::TokenKind,
    tokenstream::{
        AttrTokenStream, AttrTokenTree, AttrsTarget, LazyAttrTokenStream, TokenStream, TokenTree,
    },
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{source_map::SourceMap, Span};
use smallvec::smallvec;

use super::{AstEdit, AstEditKind, AstSuggestion, AstSuggestions};

#[derive(Debug)]
pub struct TransformVisitor<'tcx> {
    suggestions: AstSuggestions<'tcx>,
    updated: bool,
}

impl<'tcx> TransformVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, suggestion_vec: Vec<AstSuggestion>) -> Self {
        let mut suggestions = AstSuggestions::new(tcx.sess.source_map());
        for suggestion in suggestion_vec {
            suggestions.add(suggestion.span, suggestion.action);
        }
        Self {
            suggestions,
            updated: false,
        }
    }
    // fn try_replace<T: Spanned>(
    //     &mut self,
    //     replacement_kind: AstEditKind,
    //     target: &mut P<T>,
    //     extract: impl FnOnce(AstEdit) -> Option<T>,
    //     // fallback: impl FnOnce(&mut Self, &mut P<T>),
    // ) {
    //     let span = target.span();
    //     let Some(AstSuggestion {
    //         action: replacement,
    //         ..
    //     }) = self.suggestions.pop_by_kind(span, replacement_kind)
    //     else {
    //         // fallback(self, target);
    //         return;
    //     };

    //     let Some(new_node) = extract(replacement) else {
    //         // fallback(self, target);
    //         return;
    //     };

    //     self.updated = true;
    //     **target = new_node;
    //     target.set_span(span);
    // }
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_crate(&mut self, krate: &mut Crate) {
        mut_visit::walk_crate(self, krate);
        let mut append_vec = vec![];
        for (idx, item) in &mut krate.items.iter_mut().enumerate() {
            let edit_vec = self
                .suggestions
                .pop_by_kind(item.span, vec![AstEditKind::AppendAfterItem]);
            for edit in edit_vec {
                match edit.action {
                    AstEdit::AppendAfterItem(new_item) => {
                        self.updated = true;
                        // Insert the new item after the current item.
                        append_vec.push((idx, new_item));
                        // Update the span of the current item to the new item's span.
                        item.span = edit.span;
                    }
                    _ => {
                        unreachable!();
                    }
                }
            }
        }
        append_vec.reverse(); // for not messing up the indices
        for (idx, new_item) in append_vec {
            // Insert the new item after the current item.
            krate.items.insert(idx + 1, P(new_item));
        }
    }

    fn visit_item(&mut self, item: &mut P<Item>) {
        mut_visit::walk_item(self, item);
        let edit_vec = self.suggestions.pop_by_kind(
            item.span,
            vec![AstEditKind::ReplaceItem, AstEditKind::RemoveFieldDef],
        );
        for edit in edit_vec {
            match edit.action {
                AstEdit::ReplaceItem(new_item) => {
                    self.updated = true;
                    **item = new_item;
                    item.span = edit.span;
                }
                AstEdit::RemoveFieldDef(span) => {
                    let ItemKind::Struct(VariantData::Struct { ref mut fields, .. }, _) = item.kind
                    else {
                        unreachable!(
                            "RemoveFieldDef should only be applied to a struct item definition"
                        );
                    };
                    // Remove the field with the given span from the struct definition.
                    fields.retain(|field| {
                        // Retain fields that do not match the span of the field to be removed.
                        field.span != span
                    });
                    self.updated = true;
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }

    fn visit_block(&mut self, block: &mut P<Block>) {
        mut_visit::walk_block(self, block);
        let edit_vec = self
            .suggestions
            .pop_by_kind(block.span, vec![AstEditKind::PrependToBlock]);
        for edit in edit_vec {
            match edit.action {
                AstEdit::PrependToBlock(new_stmt) => {
                    self.updated = true;
                    // Prepend the statement to the block.
                    block.stmts.insert(0, new_stmt);
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }

    fn flat_map_stmt(&mut self, s: Stmt) -> smallvec::SmallVec<[Stmt; 1]> {
        let edit_vec = self.suggestions.pop_by_kind(
            s.span,
            vec![AstEditKind::ReplaceStmt, AstEditKind::RemoveStmt],
        );
        if edit_vec.is_empty() {
            mut_visit::walk_flat_map_stmt(self, s)
        } else {
            assert_eq!(edit_vec.len(), 1);
            let edit = edit_vec.into_iter().next().unwrap();
            match edit.action {
                AstEdit::ReplaceStmt(new_stmt) => {
                    self.updated = true;
                    // Replace the statement with the new statement.
                    return smallvec![new_stmt];
                }
                AstEdit::RemoveStmt => {
                    self.updated = true;
                    // Remove the statement by returning an empty vector.
                    return smallvec![];
                }
                _ => {
                    unreachable!()
                }
            }
        }
    }

    fn visit_pat(&mut self, pat: &mut P<Pat>) {
        mut_visit::walk_pat(self, pat);
        let edit_vec = self
            .suggestions
            .pop_by_kind(pat.span, vec![AstEditKind::ReplacePat]);
        for edit in edit_vec {
            match edit.action {
                AstEdit::ReplacePat(new_pat) => {
                    self.updated = true;
                    **pat = new_pat;
                    pat.span = edit.span;
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut P<Expr>) {
        mut_visit::walk_expr(self, expr);
        let edit_vec = self.suggestions.pop_by_kind(
            expr.span,
            vec![AstEditKind::ReplaceExpr, AstEditKind::RemoveExprField],
        );
        for edit in edit_vec {
            match edit.action {
                AstEdit::ReplaceExpr(new_expr) => {
                    self.updated = true;
                    **expr = new_expr;
                    expr.span = edit.span;
                }
                AstEdit::RemoveExprField(span) => {
                    let ExprKind::Struct(struct_expr) = &mut expr.kind else {
                        unreachable!(
                            "RemoveExprField should only be applied to a struct expression"
                        );
                    };
                    // Remove the field with the given span from the struct expression.
                    struct_expr.fields.retain(|field| {
                        // Retain fields that do not match the span of the field to be removed.
                        field.span != span
                    });
                    self.updated = true;
                }
                _ => {}
            }
        }
    }

    fn visit_field_def(&mut self, field_def: &mut FieldDef) {
        mut_visit::walk_field_def(self, field_def);
        let edit_vec = self
            .suggestions
            .pop_by_kind(field_def.span, vec![AstEditKind::RemoveFieldAttr]);
        for edit in edit_vec {
            match edit.action {
                AstEdit::RemoveFieldAttr(span) => {
                    // Remove the attribute with the given span from the field definition.
                    field_def.attrs.retain(|attr| attr.span != span);
                    self.updated = true;
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }
}
