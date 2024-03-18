use std::{
    collections::{HashMap, HashSet},
    path::Path,
};

use etrace::some_or;
use rustc_hir::{def_id::LocalDefId, ItemKind, Node};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        interpret::{ConstValue, GlobalAlloc, Scalar},
        AggregateKind, ConstantKind, Local, LocalDecl, Location, Operand, Place, PlaceElem, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{IntTy, Ty, TyCtxt, TyKind, TypeAndMut, UintTy},
};
use rustc_session::config::Input;
use rustc_span::def_id::DefId;

use crate::compile_util;

pub type AnalysisResults = HashMap<Loc, HashSet<Loc>>;

pub fn analyze_path(path: &Path) -> AnalysisResults {
    analyze_input(compile_util::path_to_input(path))
}

pub fn analyze_str(code: &str) -> AnalysisResults {
    analyze_input(compile_util::str_to_input(code))
}

fn analyze_input(input: Input) -> AnalysisResults {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, analyze).unwrap()
}

pub fn analyze(tcx: TyCtxt<'_>) -> AnalysisResults {
    let hir = tcx.hir();

    let mut vertices = HashSet::new();
    let mut tokens = HashSet::new();
    let mut alloc_vertices = HashSet::new();
    let mut alloc_tokens = HashSet::new();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        if item.ident.name.as_str() == "main" {
            continue;
        }
        let local_def_id = item.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        let (body, is_static) = match item.kind {
            ItemKind::Fn(_, _, _) => {
                let root = LocRoot::Global(local_def_id);
                let loc = Loc::new_root(root);
                tokens.insert(loc);

                (tcx.optimized_mir(def_id), false)
            }
            ItemKind::Static(_, _, _) => (tcx.mir_for_ctfe(def_id), true),
            _ => continue,
        };
        for (local, local_decl) in body.local_decls.iter_enumerated() {
            let (vs, ts) = vertices_and_tokens(local_decl.ty, tcx, Proj::empty());
            for v in vs {
                if is_static && local.as_usize() == 0 {
                    let root = LocRoot::Global(local_def_id);
                    let loc = Loc::new(root, v);
                    vertices.insert(loc);
                }
                let root = LocRoot::Local(local_def_id, local);
                let loc = Loc::new(root, v);
                vertices.insert(loc);
            }
            for t in ts {
                if is_static && local.as_usize() == 0 {
                    let root = LocRoot::Global(local_def_id);
                    let loc = Loc::new(root, t);
                    tokens.insert(loc);
                }
                let root = LocRoot::Local(local_def_id, local);
                let loc = Loc::new(root, t);
                tokens.insert(loc);
            }

            if let TyKind::RawPtr(TypeAndMut { ty, .. }) | TyKind::Ref(_, ty, _) =
                local_decl.ty.kind()
            {
                let (vs, ts) = vertices_and_tokens(*ty, tcx, Proj::empty());
                alloc_vertices.extend(vs);
                alloc_tokens.extend(ts);
            }
        }
    }

    let mut analyzer = Analyzer {
        tcx,
        vertices,
        tokens,
        alloc_vertices,
        alloc_tokens,
        state: State::default(),
    };
    for item_id in hir.items() {
        let item = hir.item(item_id);
        if item.ident.name.as_str() == "main" {
            continue;
        }
        let local_def_id = item.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        let body = match item.kind {
            ItemKind::Fn(_, _, _) => tcx.optimized_mir(def_id),
            ItemKind::Static(_, _, _) => {
                let body = tcx.mir_for_ctfe(def_id);

                let l0 = Local::from_usize(0);
                let ty = body.local_decls[l0].ty;
                let l_root = LocRoot::Global(local_def_id);
                let l = DLoc::new_loc(Loc::new_root(l_root));
                let r_root = LocRoot::Local(local_def_id, l0);
                let r = DLoc::new_loc(Loc::new_root(r_root));
                analyzer.transfer_assign(l, r, ty);

                body
            }
            _ => continue,
        };
        // println!("{}", compile_util::body_to_str(body));
        for (block, bbd) in body.basic_blocks.iter_enumerated() {
            for (statement_index, stmt) in bbd.statements.iter().enumerate() {
                let location = Location {
                    block,
                    statement_index,
                };
                let ctx = Context::new(&body.local_decls, local_def_id, location);
                analyzer.transfer_stmt(stmt, ctx);
            }
            let terminator = bbd.terminator();
            let location = Location {
                block,
                statement_index: bbd.statements.len(),
            };
            let ctx = Context::new(&body.local_decls, local_def_id, location);
            analyzer.transfer_term(terminator, ctx);
        }
    }
    analyzer.state.solutions
}

fn vertices_and_tokens<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    proj: Proj,
) -> (Vec<Proj>, Vec<Proj>) {
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Slice(_)
        | TyKind::Never
        | TyKind::Int(IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I128)
        | TyKind::Uint(UintTy::U8 | UintTy::U16 | UintTy::U32 | UintTy::U128) => {
            (vec![], vec![proj])
        }
        TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Foreign(_)
        | TyKind::RawPtr(_)
        | TyKind::Ref(_, _, _)
        | TyKind::FnDef(_, _)
        | TyKind::FnPtr(_) => (vec![proj], vec![proj]),
        TyKind::Adt(adt_def, generic_args) => {
            let mut vertices = vec![];
            let mut tokens = vec![];
            for v in adt_def.variants() {
                for (i, f) in v.fields.iter_enumerated() {
                    let i = i.as_usize();
                    let ty = f.ty(tcx, generic_args);
                    let (vs, ts) = vertices_and_tokens(ty, tcx, proj.push(i));
                    vertices.extend(vs);
                    tokens.extend(ts);
                }
            }
            tokens.push(proj);
            (vertices, tokens)
        }
        TyKind::Array(ty, _) => {
            let (vertices, mut tokens) = vertices_and_tokens(*ty, tcx, proj.push(0));
            tokens.push(proj);
            (vertices, tokens)
        }
        TyKind::Tuple(tys) => {
            let mut vertices = vec![];
            let mut tokens = vec![];
            for (i, ty) in tys.iter().enumerate() {
                let (vs, ts) = vertices_and_tokens(ty, tcx, proj.push(i));
                vertices.extend(vs);
                tokens.extend(ts);
            }
            tokens.push(proj);
            (vertices, tokens)
        }
        _ => unreachable!("{:?}", ty),
    }
}

#[derive(Clone, Copy)]
struct Context<'a, 'tcx> {
    locals: &'a IndexVec<Local, LocalDecl<'tcx>>,
    owner: LocalDefId,
    location: Location,
}

impl<'a, 'tcx> Context<'a, 'tcx> {
    fn new(
        locals: &'a IndexVec<Local, LocalDecl<'tcx>>,
        owner: LocalDefId,
        location: Location,
    ) -> Self {
        Self {
            locals,
            owner,
            location,
        }
    }
}

struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    vertices: HashSet<Loc>,
    tokens: HashSet<Loc>,
    alloc_vertices: HashSet<Proj>,
    alloc_tokens: HashSet<Proj>,
    state: State<'tcx>,
}

impl<'tcx> Analyzer<'tcx> {
    fn transfer_stmt(&mut self, stmt: &Statement<'tcx>, ctx: Context<'_, 'tcx>) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        let ty = l.ty(ctx.locals, self.tcx).ty;
        let l = DLoc::from_place(*l, ctx.owner);
        match r {
            Rvalue::Use(r) => {
                if let Some(r) = self.transfer_op(r, ctx) {
                    self.transfer_assign(l, r, ty);
                }
            }
            Rvalue::Repeat(r, _) => {
                if let Some(r) = self.transfer_op(r, ctx) {
                    let TyKind::Array(ty, _) = ty.kind() else { unreachable!() };
                    self.transfer_assign(l.push(0), r, *ty);
                }
            }
            Rvalue::Ref(_, _, r) => {
                let r = DLoc::from_place(*r, ctx.owner).with_ref(true);
                self.transfer_assign(l, r, ty);
            }
            Rvalue::ThreadLocalRef(r) => {
                let loc = Loc::new_root(LocRoot::Global(r.as_local().unwrap()));
                let r = DLoc::new_ref(loc);
                self.transfer_assign(l, r, ty);
            }
            Rvalue::AddressOf(_, r) => {
                assert!(r.is_indirect_first_projection());
                let r = DLoc::from_place(*r, ctx.owner).with_deref(false);
                self.transfer_assign(l, r, ty);
            }
            Rvalue::Len(_) => {}
            Rvalue::Cast(_, r, _) => {
                if let Some(r) = self.transfer_op(r, ctx) {
                    self.transfer_assign(l, r, ty);
                }
            }
            Rvalue::BinaryOp(_, _) => {}
            Rvalue::CheckedBinaryOp(_, _) => {}
            Rvalue::NullaryOp(_, _) => unreachable!(),
            Rvalue::UnaryOp(_, _) => {}
            Rvalue::Discriminant(_) => {}
            Rvalue::Aggregate(box kind, fs) => match kind {
                AggregateKind::Array(ty) => {
                    for f in fs.iter() {
                        if let Some(r) = self.transfer_op(f, ctx) {
                            self.transfer_assign(l.push(0), r, *ty);
                        }
                    }
                }
                AggregateKind::Adt(_, v_idx, _, _, idx) => {
                    let TyKind::Adt(adt_def, generic_args) = ty.kind() else { unreachable!() };
                    let variant = adt_def.variant(*v_idx);
                    for ((i, d), f) in variant.fields.iter_enumerated().zip(fs) {
                        if let Some(r) = self.transfer_op(f, ctx) {
                            let ty = d.ty(self.tcx, generic_args);
                            let i = if let Some(idx) = idx { *idx } else { i };
                            self.transfer_assign(l.push(i.as_usize()), r, ty);
                        }
                    }
                }
                _ => unreachable!(),
            },
            Rvalue::ShallowInitBox(_, _) => unreachable!(),
            Rvalue::CopyForDeref(r) => {
                let r = DLoc::from_place(*r, ctx.owner);
                self.transfer_assign(l, r, ty);
            }
        }
    }

    fn transfer_assign(&mut self, l: DLoc, r: DLoc, ty: Ty<'tcx>) {
        match ty.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::Never
            | TyKind::Int(IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I128)
            | TyKind::Uint(UintTy::U8 | UintTy::U16 | UintTy::U32 | UintTy::U128) => {}
            TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Foreign(_)
            | TyKind::RawPtr(_)
            | TyKind::Ref(_, _, _)
            | TyKind::FnDef(_, _)
            | TyKind::FnPtr(_) => {
                self.transfer_assign_single(l, r);
            }
            TyKind::Adt(adt_def, generic_args) => {
                for v in adt_def.variants() {
                    for (i, f) in v.fields.iter_enumerated() {
                        let i = i.as_usize();
                        let ty = f.ty(self.tcx, generic_args);
                        self.transfer_assign(l.push(i), r.push(i), ty);
                    }
                }
            }
            TyKind::Array(ty, _) => {
                self.transfer_assign(l.push(0), r.push(0), *ty);
            }
            TyKind::Tuple(tys) => {
                for (i, ty) in tys.iter().enumerate() {
                    self.transfer_assign(l.push(i), r.push(i), ty);
                }
            }
            _ => unreachable!("{:?}", ty),
        }
    }

    fn transfer_assign_single(&mut self, l: DLoc, r: DLoc) {
        assert!(!l.r#ref);
        match (l.deref, r.r#ref, r.deref) {
            (true, true, _) => unreachable!(),
            (true, false, true) => unreachable!(),
            (true, false, false) => {
                let l_root = l.loc.only_root();
                if let Some(ts) = self.state.solutions.get(&l_root) {
                    for t in ts.clone() {
                        self.add_edge(r.loc, t.extend(l.loc.projection));
                    }
                }
                self.add_to(l_root, r.loc, l.loc.projection);
                self.propagate();
            }
            (false, true, true) => {
                if r.loc.projection.is_empty() {
                    self.add_edge(r.loc, l.loc);
                    self.propagate();
                } else {
                    let r_root = r.loc.only_root();
                    if let Some(ts) = self.state.solutions.get(&r_root) {
                        for t in ts.clone() {
                            self.add_token(t.extend(r.loc.projection), l.loc);
                        }
                    }
                    self.add_token_to(r_root, l.loc, r.loc.projection);
                    self.propagate();
                }
            }
            (false, true, false) => {
                self.add_token(r.loc, l.loc);
                self.propagate();
            }
            (false, false, true) => {
                let r_root = r.loc.only_root();
                if let Some(ts) = self.state.solutions.get(&r_root) {
                    for t in ts.clone() {
                        self.add_edge(t.extend(r.loc.projection), l.loc);
                    }
                }
                self.add_from(r_root, l.loc, r.loc.projection);
                self.propagate();
            }
            (false, false, false) => {
                self.add_edge(r.loc, l.loc);
                self.propagate();
            }
        }
    }

    fn transfer_op(&mut self, op: &Operand<'tcx>, ctx: Context<'_, 'tcx>) -> Option<DLoc> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                Some(DLoc::from_place(*place, ctx.owner))
            }
            Operand::Constant(box constant) => match constant.literal {
                ConstantKind::Ty(_) => unreachable!(),
                ConstantKind::Unevaluated(_, _) => None,
                ConstantKind::Val(value, ty) => match value {
                    ConstValue::Scalar(scalar) => match scalar {
                        Scalar::Int(_) => None,
                        Scalar::Ptr(ptr, _) => match self.tcx.global_alloc(ptr.provenance) {
                            GlobalAlloc::Static(def_id) => {
                                let loc = Loc::new_root(LocRoot::Global(def_id.as_local()?));
                                Some(DLoc::new_ref(loc))
                            }
                            GlobalAlloc::Memory(_) => {
                                let loc = Loc::new_root(LocRoot::Alloc(ctx.owner, ctx.location));
                                Some(DLoc::new_ref(loc))
                            }
                            _ => unreachable!(),
                        },
                    },
                    ConstValue::ZeroSized => {
                        let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                        let loc = Loc::new_root(LocRoot::Global(def_id.as_local()?));
                        Some(DLoc::new_ref(loc))
                    }
                    ConstValue::Slice { .. } => {
                        let loc = Loc::new_root(LocRoot::Alloc(ctx.owner, ctx.location));
                        Some(DLoc::new_ref(loc))
                    }
                    _ => unreachable!(),
                },
            },
        }
    }

    fn transfer_term(&mut self, term: &Terminator<'tcx>, ctx: Context<'_, 'tcx>) {
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        else {
            return;
        };
        assert!(destination.projection.is_empty());

        let args: Vec<_> = args.iter().map(|arg| self.transfer_op(arg, ctx)).collect();
        let output = destination.ty(ctx.locals, self.tcx).ty;
        let dst = DLoc::from_place(*destination, ctx.owner);

        match func {
            Operand::Copy(func) | Operand::Move(func) => {
                assert!(func.projection.is_empty());
                let func = DLoc::from_place(*func, ctx.owner);
                if let Some(callees) = self.state.solutions.get(&func.loc) {
                    for callee in callees.clone() {
                        if callee.projection.is_empty() {
                            if let LocRoot::Global(local_def_id) = callee.root {
                                self.transfer_intra_call(args.clone(), dst, output, local_def_id);
                            }
                        }
                    }
                }
                let call = CallInfo::new(args, dst, output);
                self.add_call(func.loc, call);
            }
            Operand::Constant(box constant) => {
                let ConstantKind::Val(value, ty) = constant.literal else { unreachable!() };
                assert!(matches!(value, ConstValue::ZeroSized));
                let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                let name = self.def_id_to_string(*def_id);
                let mut segs: Vec<_> = name.split("::").collect();
                let seg0 = segs.pop().unwrap_or_default();
                let seg1 = segs.pop().unwrap_or_default();
                let seg2 = segs.pop().unwrap_or_default();
                let seg3 = segs.pop().unwrap_or_default();
                if let Some(local_def_id) = def_id.as_local() {
                    if let Some(impl_def_id) = self.tcx.impl_of_method(*def_id) {
                        let span = self.tcx.span_of_impl(impl_def_id).unwrap();
                        let code = self.tcx.sess.source_map().span_to_snippet(span).unwrap();
                        assert_eq!(code, "BitfieldStruct");
                    } else if seg1.contains("{extern#") {
                        self.transfer_c_call(dst, output, ctx);
                    } else {
                        self.transfer_intra_call(args, dst, output, local_def_id);
                    }
                } else {
                    let inputs = self.get_input_tys(*def_id).unwrap();
                    let callee = (seg3, seg2, seg1, seg0);
                    self.transfer_rust_call(args, dst, output, inputs, callee, ctx);
                }
            }
        }
    }

    fn transfer_intra_call(
        &mut self,
        args: Vec<Option<DLoc>>,
        dst: DLoc,
        output: Ty<'tcx>,
        callee: LocalDefId,
    ) {
        let inputs = some_or!(self.get_input_tys(callee.to_def_id()), return);

        for (i, (ty, arg)) in inputs.iter().zip(args).enumerate() {
            let arg = some_or!(arg, continue);
            let root = LocRoot::Local(callee, Local::from_usize(i + 1));
            let loc = Loc::new_root(root);
            let param = DLoc::new_loc(loc);
            self.transfer_assign(param, arg, *ty);
        }

        let root = LocRoot::Local(callee, Local::from_usize(0));
        let loc = Loc::new_root(root);
        let ret = DLoc::new_loc(loc);
        self.transfer_assign(dst, ret, output);
    }

    fn transfer_c_call(&mut self, dst: DLoc, output: Ty<'tcx>, ctx: Context<'_, 'tcx>) {
        if output.is_unsafe_ptr() {
            let loc = Loc::new_root(LocRoot::Alloc(ctx.owner, ctx.location));
            self.transfer_assign(dst, DLoc::new_ref(loc), output);
        }
    }

    fn transfer_rust_call(
        &mut self,
        args: Vec<Option<DLoc>>,
        dst: DLoc,
        output: Ty<'tcx>,
        inputs: &[Ty<'tcx>],
        callee: (&str, &str, &str, &str),
        ctx: Context<'_, 'tcx>,
    ) {
        if (output.is_unit() || output.is_never() || output.is_primitive())
            && inputs.iter().filter(|t| !t.is_primitive()).count() < 2
        {
            return;
        }
        match callee {
            ("", "option" | "result", _, "unwrap") => {
                if let Some(arg) = &args[0] {
                    self.transfer_assign(dst, arg.push(0), output);
                }
            }
            (_, "slice", _, "as_ptr" | "as_mut_ptr") => {
                if let Some(arg) = &args[0] {
                    let arg = arg.with_ref(true).with_deref(true).push(0);
                    self.transfer_assign(dst, arg, output);
                }
            }
            ("ptr", _, _, "offset") => {
                if let Some(arg) = &args[0] {
                    self.transfer_assign(dst, *arg, output);
                }
            }
            ("", "vec", _, "leak" | "as_mut_ptr") => {
                let loc = Loc::new_root(LocRoot::Alloc(ctx.owner, ctx.location));
                self.transfer_assign(dst, DLoc::new_ref(loc), output);
            }
            ("", "num", _, name) if name.starts_with("overflowing_") => {}
            ("", "unix", _, "memcpy")
            | ("", "", "vec", "from_elem")
            | ("ptr", _, _, "offset_from")
            | ("", "", "ptr", "write_volatile")
            | ("", "", "ptr", "read_volatile")
            | ("ops", "deref", _, "deref" | "deref_mut")
            | ("", "clone", "Clone", "clone")
            | ("", "ffi", _, "as_va_list")
            | ("", "ffi", _, "arg")
            | (_, _, "AsmCastTrait", _)
            | ("", "cast", "ToPrimitive", _)
            | ("", "cmp", "PartialEq", _)
            | ("", "cmp", "PartialOrd", _)
            | ("", "convert", _, _)
            | ("ops", "arith", _, _)
            | ("", "f128_t", _, _) => {}
            _ => panic!("{:?}", callee),
        }
    }

    fn add_token(&mut self, t: Loc, v: Loc) {
        if t.is_alloc() {
            if !self.alloc_tokens.contains(&t.projection) {
                return;
            }
        } else if !self.tokens.contains(&t) {
            return;
        }
        if v.is_alloc() {
            if !self.alloc_vertices.contains(&v.projection) {
                return;
            }
        } else if !self.vertices.contains(&v) {
            return;
        }
        if self.state.solutions.entry(v).or_default().insert(t) {
            self.state.worklist.push((t, v));
        }
    }

    fn add_edge(&mut self, x: Loc, y: Loc) {
        if x != y && self.state.successors.entry(x).or_default().insert(y) {
            for t in some_or!(self.state.solutions.get(&x), return).clone() {
                self.add_token(t, y);
            }
        }
    }

    fn add_from(&mut self, x: Loc, y: Loc, proj: Proj) {
        self.state.froms.entry(x).or_default().insert((y, proj));
    }

    fn add_to(&mut self, x: Loc, y: Loc, proj: Proj) {
        self.state.tos.entry(x).or_default().insert((y, proj));
    }

    fn add_token_to(&mut self, x: Loc, y: Loc, proj: Proj) {
        self.state.token_tos.entry(x).or_default().insert((y, proj));
    }

    fn add_call(&mut self, x: Loc, call: CallInfo<'tcx>) {
        self.state.calls.entry(x).or_default().push(call);
    }

    fn propagate(&mut self) {
        while let Some(tx) = self.state.worklist.pop() {
            let (t, x) = tx;
            if t.projection.is_empty() {
                if let LocRoot::Global(callee) = t.root {
                    if let Some(cs) = self.state.calls.get(&x) {
                        for c in cs.clone() {
                            self.transfer_intra_call(c.args, c.dst, c.output, callee)
                        }
                    }
                }
            }
            if let Some(ys) = self.state.froms.get(&x) {
                for (y, proj) in ys.clone() {
                    self.add_edge(t.extend(proj), y);
                }
            }
            if let Some(ys) = self.state.tos.get(&x) {
                for (y, proj) in ys.clone() {
                    self.add_edge(y, t.extend(proj));
                }
            }
            if let Some(ys) = self.state.token_tos.get(&x) {
                for (y, proj) in ys.clone() {
                    self.add_token(t.extend(proj), y);
                }
            }
            if let Some(ys) = self.state.successors.get(&x) {
                for y in ys.clone() {
                    self.add_token(t, y);
                }
            }
        }
    }

    fn def_id_to_string(&self, def_id: DefId) -> String {
        self.tcx.def_path(def_id).to_string_no_crate_verbose()
    }

    fn get_input_tys(&self, func: DefId) -> Option<&'tcx [Ty<'tcx>]> {
        if let Some(node) = self.tcx.hir().get_if_local(func) {
            let Node::Item(item) = node else { return None };
            if !matches!(item.kind, ItemKind::Fn(_, _, _)) {
                return None;
            }
        }
        Some(self.tcx.fn_sig(func).skip_binder().inputs().skip_binder())
    }
}

#[derive(Default)]
struct State<'tcx> {
    solutions: HashMap<Loc, HashSet<Loc>>,
    successors: HashMap<Loc, HashSet<Loc>>,
    froms: HashMap<Loc, HashSet<(Loc, Proj)>>,
    tos: HashMap<Loc, HashSet<(Loc, Proj)>>,
    token_tos: HashMap<Loc, HashSet<(Loc, Proj)>>,
    calls: HashMap<Loc, Vec<CallInfo<'tcx>>>,
    worklist: Vec<(Loc, Loc)>,
}

#[derive(Clone)]
struct CallInfo<'tcx> {
    args: Vec<Option<DLoc>>,
    dst: DLoc,
    output: Ty<'tcx>,
}

impl<'tcx> CallInfo<'tcx> {
    fn new(args: Vec<Option<DLoc>>, dst: DLoc, output: Ty<'tcx>) -> Self {
        Self { args, dst, output }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum LocRoot {
    Global(LocalDefId),
    Local(LocalDefId, Local),
    Alloc(LocalDefId, Location),
}

impl std::fmt::Debug for LocRoot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LocRoot::Global(def_id) => write!(f, "{:?}", def_id),
            LocRoot::Local(def_id, local) => write!(f, "{:?}:{:?}", def_id, local),
            LocRoot::Alloc(def_id, location) => write!(f, "{:?}:{:?}", def_id, location),
        }
    }
}

impl LocRoot {
    #[inline]
    fn is_alloc(&self) -> bool {
        matches!(self, LocRoot::Alloc(_, _))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Proj {
    v: u64,
    len: u8,
}

impl std::fmt::Debug for Proj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in self.v.to_be_bytes() {
            if i != 0 {
                write!(f, ".{}", i - 1)?;
            }
        }
        Ok(())
    }
}

impl FromIterator<usize> for Proj {
    fn from_iter<I: IntoIterator<Item = usize>>(iter: I) -> Self {
        let mut proj = Self::empty();
        for i in iter {
            proj = proj.push(i);
        }
        proj
    }
}

impl Proj {
    #[inline]
    fn empty() -> Self {
        Self { v: 0, len: 0 }
    }

    #[inline]
    fn is_empty(self) -> bool {
        self.v == 0
    }

    #[inline]
    fn push(self, i: usize) -> Self {
        assert!(i < 255);
        assert!(self.len < 8);
        Self {
            v: self.v << 8 | (i + 1) as u64,
            len: self.len + 1,
        }
    }

    #[inline]
    fn extend(self, i: Self) -> Self {
        assert!(self.len + i.len <= 8);
        Self {
            v: self.v << (i.len * 8) | i.v,
            len: self.len + i.len,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Loc {
    root: LocRoot,
    projection: Proj,
}

impl std::fmt::Debug for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.root)?;
        write!(f, "{:?}", self.projection)
    }
}

impl Loc {
    #[inline]
    pub fn new(root: LocRoot, projection: Proj) -> Self {
        Self { root, projection }
    }

    #[inline]
    pub fn new_root(root: LocRoot) -> Self {
        Self::new(root, Proj::empty())
    }

    #[inline]
    pub fn push(mut self, proj: usize) -> Self {
        self.projection = self.projection.push(proj);
        self
    }

    #[inline]
    fn extend(mut self, proj: Proj) -> Self {
        self.projection = self.projection.extend(proj);
        self
    }

    #[inline]
    fn only_root(&self) -> Self {
        Self::new_root(self.root)
    }

    #[inline]
    fn is_alloc(&self) -> bool {
        self.root.is_alloc()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct DLoc {
    r#ref: bool,
    deref: bool,
    loc: Loc,
}

impl std::fmt::Debug for DLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.r#ref {
            write!(f, "&")?;
        }
        if self.deref {
            write!(f, "*")?;
        }
        write!(f, "{:?}", self.loc)
    }
}

impl DLoc {
    #[inline]
    fn new(rf: bool, deref: bool, loc: Loc) -> Self {
        Self {
            r#ref: rf,
            deref,
            loc,
        }
    }

    #[inline]
    fn new_loc(loc: Loc) -> Self {
        Self::new(false, false, loc)
    }

    #[inline]
    fn new_ref(loc: Loc) -> Self {
        Self::new(true, false, loc)
    }

    #[inline]
    fn push(mut self, proj: usize) -> Self {
        self.loc = self.loc.push(proj);
        self
    }

    #[inline]
    fn with_deref(mut self, deref: bool) -> Self {
        self.deref = deref;
        self
    }

    #[inline]
    fn with_ref(mut self, r#ref: bool) -> Self {
        self.r#ref = r#ref;
        self
    }

    fn from_place(place: Place<'_>, owner: LocalDefId) -> Self {
        let root = LocRoot::Local(owner, place.local);
        let mut projection = Proj::empty();
        for proj in place.projection {
            match proj {
                PlaceElem::Deref => {}
                PlaceElem::Field(f, _) => projection = projection.push(f.as_usize()),
                PlaceElem::Index(_) => projection = projection.push(0),
                _ => unreachable!(),
            }
        }
        let loc = Loc::new(root, projection);
        let deref = place.is_indirect_first_projection();
        Self::new(false, deref, loc)
    }
}
