use std::{collections::HashMap, fmt, path::PathBuf};

use rustc_ast::{ast::*, ptr::P};
use rustc_span::{source_map::SourceMap, Span};

use crate::compile_util;

#[derive(Clone)]
pub struct AstSuggestions<'tcx> {
    pub suggestions: HashMap<Option<PathBuf>, Vec<AstSuggestion>>,
    source_map: &'tcx SourceMap,
}

impl fmt::Debug for AstSuggestions<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.suggestions.iter()).finish()
    }
}

impl<'tcx> AstSuggestions<'tcx> {
    pub fn new(source_map: &'tcx SourceMap) -> Self {
        Self {
            suggestions: HashMap::new(),
            source_map,
        }
    }

    pub fn add(&mut self, span: Span, replacement: AstEdit) {
        let path_opt = compile_util::span_to_path(span, self.source_map);
        self.suggestions
            .entry(path_opt)
            .or_default()
            .push(AstSuggestion {
                span,
                action: replacement,
            });
    }

    pub(super) fn pop_by_kind(
        &mut self,
        span: Span,
        kinds: Vec<AstEditKind>,
    ) -> Vec<AstSuggestion> {
        // Suppose the suggestions are distinct by span and path.
        let path_opt = compile_util::span_to_path(span, self.source_map);
        let vec = match self.suggestions.get_mut(&path_opt) {
            Some(vec) => vec,
            None => return Vec::new(),
        };
        vec.extract_if(.., |s| s.span == span && kinds.contains(&s.action.kind()))
            .collect()
    }
}

macro_rules! define_ast_edit {
    (
        $( $variant:ident $( ( $ty:ty ) )? ),* $(,)?
    ) => {
        #[derive(Debug, Clone)]
        pub enum AstEdit {
            $(
                $variant $( ( $ty ) )?,
            )*
        }

        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum AstEditKind {
            $(
                $variant,
            )*
        }

        impl AstEdit {
            pub fn kind(&self) -> AstEditKind {
                match self {
                    $(
                        Self::$variant { .. } => AstEditKind::$variant,
                    )*
                }
            }
        }
    };
}

define_ast_edit!(
    // Handled by visit_crate
    AppendAfterItem(Item),
    // Handled by visit_item
    ReplaceItem(Item),
    RemoveFieldDef(Span), /* Given the parent Item(kind: struct)'s span, remove a field definition of this span. */
    // handled by visit_block
    PrependToBlock(Stmt), /* For a block expression matching the span, prepend the statement to the block. */
    // Handled by visit_stmt
    ReplaceStmt(Stmt),
    RemoveStmt,
    // Handled by visit_pat
    ReplacePat(Pat),
    // Handled by visit_expr
    ReplaceExpr(Expr),
    RemoveExprField(Span), /* Given the parent Expr's span, remove a field definition of this span. */
    // Handled by TODO: visit_field_def?
    RemoveFieldAttr(Span), /* Given the parent FieldDef's span, remove a field attribute of this span. */
);

#[derive(Debug, Clone)]
pub struct AstSuggestion {
    pub span: Span,
    pub action: AstEdit,
}
