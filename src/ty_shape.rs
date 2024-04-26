use std::collections::HashMap;

use rustc_ast::UintTy;
use rustc_hir::{def::Res, ItemKind, PrimTy, QPath, TyKind as HirTyKind};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_span::def_id::{DefId, LocalDefId};
use typed_arena::Arena;

use crate::*;

pub struct TyShapes<'a, 'tcx> {
    pub bitfields: HashMap<LocalDefId, HashMap<String, usize>>,
    pub tys: HashMap<Ty<'tcx>, &'a TyShape<'a>>,
    prim: &'a TyShape<'a>,
    arena: &'a Arena<TyShape<'a>>,
}

impl std::fmt::Debug for TyShapes<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TyShapes")
            .field("bitfields", &self.bitfields)
            .field("tys", &self.tys)
            .finish()
    }
}

pub fn get_ty_shapes<'a, 'tcx>(
    arena: &'a Arena<TyShape<'a>>,
    tcx: TyCtxt<'tcx>,
) -> TyShapes<'a, 'tcx> {
    let prim = arena.alloc(TyShape::Primitive);
    let mut tss = TyShapes {
        bitfields: HashMap::new(),
        tys: HashMap::new(),
        prim,
        arena,
    };
    compute_bitfields(&mut tss, tcx);
    compute_ty_shapes(&mut tss, tcx);
    tss
}

fn compute_bitfields<'tcx>(tss: &mut TyShapes<'_, 'tcx>, tcx: TyCtxt<'tcx>) {
    let hir = tcx.hir();

    let mut bitfield_structs = HashMap::new();
    let mut bitfield_impls = HashMap::new();
    for item_id in hir.items() {
        let item = hir.item(item_id);
        match item.kind {
            ItemKind::Struct(vd, _) => {
                for field in vd.fields() {
                    let HirTyKind::Array(ty, _) = field.ty.kind else { continue };
                    let HirTyKind::Path(QPath::Resolved(_, path)) = ty.kind else { continue };
                    if !matches!(path.res, Res::PrimTy(PrimTy::Uint(UintTy::U8))) {
                        continue;
                    }
                    let name = field.ident.name.to_ident_string();
                    if !name.starts_with("c2rust_padding") {
                        let len = vd.fields().len();
                        bitfield_structs.insert(item_id.owner_id.def_id, (name, len));
                        break;
                    }
                }
            }
            ItemKind::Impl(imp) if imp.of_trait.is_none() => {
                let HirTyKind::Path(QPath::Resolved(_, path)) = imp.self_ty.kind else {
                    unreachable!()
                };
                let Res::Def(_, def_id) = path.res else { unreachable!() };
                let local_def_id = def_id.expect_local();
                let fields: Vec<_> = imp
                    .items
                    .chunks(2)
                    .map(|items| {
                        let name0 = items[0].ident.name.to_ident_string();
                        let name0 = name0.strip_prefix("set_").unwrap();
                        let name1 = items[1].ident.name.to_ident_string();
                        assert_eq!(name0, name1);
                        name1
                    })
                    .collect();
                bitfield_impls.insert(local_def_id, fields);
            }
            _ => {}
        }
    }
    tss.bitfields = bitfield_impls
        .into_iter()
        .map(|(ty, fields)| {
            let bf1: String = fields.iter().map(|f| f.as_str()).intersperse("_").collect();
            let (ref bf2, len) = bitfield_structs[&ty];
            assert_eq!(&bf1, bf2);
            let field_indices = fields
                .into_iter()
                .enumerate()
                .map(|(i, f)| (f, len + i))
                .collect();
            (ty, field_indices)
        })
        .collect();
}

fn compute_ty_shapes<'tcx>(tss: &mut TyShapes<'_, 'tcx>, tcx: TyCtxt<'tcx>) {
    let hir = tcx.hir();

    for item_id in hir.items() {
        let item = hir.item(item_id);
        let local_def_id = item.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        let body = match item.kind {
            ItemKind::Fn(_, _, _) if item.ident.name.as_str() != "main" => {
                tcx.optimized_mir(def_id)
            }
            ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(def_id),
            _ => continue,
        };
        for local_decl in body.local_decls.iter() {
            compute_ty_shape(local_decl.ty, def_id, tss, tcx);
            if let Some(ty) = points_to::unwrap_ptr(local_decl.ty) {
                compute_ty_shape(ty, def_id, tss, tcx);
            }
        }
    }
}

fn compute_ty_shape<'a, 'tcx>(
    ty: Ty<'tcx>,
    owner: DefId,
    tss: &mut TyShapes<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) -> &'a TyShape<'a> {
    if let Some(ts) = tss.tys.get(&ty) {
        return ts;
    }
    let ts = match ty.kind() {
        TyKind::Adt(adt_def, generic_args) => {
            if ty.is_c_void(tcx) {
                tss.prim
            } else {
                let tys = adt_def.variants().iter().flat_map(|variant| {
                    variant
                        .fields
                        .iter()
                        .map(|field| field.ty(tcx, generic_args))
                });
                let bitfield_len = adt_def
                    .did()
                    .as_local()
                    .and_then(|local_def_id| tss.bitfields.get(&local_def_id))
                    .map(|fields| fields.len())
                    .unwrap_or_default();
                compute_ty_shape_many(tys, bitfield_len, owner, tss, tcx)
            }
        }
        TyKind::Array(ty, len) => {
            let t = compute_ty_shape(*ty, owner, tss, tcx);
            let len = len
                .eval(tcx, tcx.param_env(owner))
                .try_to_scalar_int()
                .unwrap()
                .try_to_u64()
                .unwrap() as usize;
            tss.arena.alloc(TyShape::Array(t, len))
        }
        TyKind::Tuple(tys) => compute_ty_shape_many(tys.iter(), 0, owner, tss, tcx),
        _ => tss.prim,
    };
    tss.tys.insert(ty, ts);
    assert_ne!(ts.len(), 0);
    ts
}

#[inline]
fn compute_ty_shape_many<'a, 'tcx, I: Iterator<Item = Ty<'tcx>>>(
    tys: I,
    bitfield_len: usize,
    owner: DefId,
    tss: &mut TyShapes<'a, 'tcx>,
    tcx: TyCtxt<'tcx>,
) -> &'a TyShape<'a> {
    let mut len = 0;
    let mut fields = vec![];
    for ty in tys {
        let ts = compute_ty_shape(ty, owner, tss, tcx);
        fields.push((len, ts));
        len += ts.len();
    }
    for _ in 0..bitfield_len {
        fields.push((len, tss.prim));
        len += 1;
    }
    if len == 0 {
        tss.prim
    } else {
        tss.arena.alloc(TyShape::Struct(len, fields))
    }
}

#[allow(variant_size_differences)]
pub enum TyShape<'a> {
    Primitive,
    Array(&'a TyShape<'a>, usize),
    Struct(usize, Vec<(usize, &'a TyShape<'a>)>),
}

impl std::fmt::Debug for TyShape<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Primitive => write!(f, "*"),
            Self::Array(t, len) => write!(f, "[{:?} * {}]", t, len),
            Self::Struct(len, fields) => {
                write!(f, "[{}", len)?;
                for (i, ts) in fields {
                    let sep = if *i == 0 { ";" } else { "," };
                    write!(f, "{} {}: {:?}", sep, i, ts)?;
                }
                write!(f, "]")
            }
        }
    }
}

impl TyShape<'_> {
    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        match self {
            Self::Primitive => 1,
            Self::Array(t, _) => t.len(),
            Self::Struct(len, _) => *len,
        }
    }
}
