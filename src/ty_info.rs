use std::collections::HashMap;

use rustc_ast::UintTy;
use rustc_hir::{def::Res, ItemKind, PrimTy, QPath, TyKind as HirTyKind};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_span::def_id::{DefId, LocalDefId};
use typed_arena::Arena;

use crate::*;

pub fn get_bitfields(tcx: TyCtxt<'_>) -> HashMap<LocalDefId, HashMap<String, usize>> {
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
    bitfield_impls
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
        .collect()
}

pub fn get_ty_infos<'a, 'tcx>(
    arena: &'a Arena<TyInfo<'a>>,
    bitfields: &HashMap<LocalDefId, HashMap<String, usize>>,
    tcx: TyCtxt<'tcx>,
) -> HashMap<Ty<'tcx>, &'a TyInfo<'a>> {
    let hir = tcx.hir();

    let prim = arena.alloc(TyInfo::Primitive);
    let mut ty_infos = HashMap::new();
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
            compute_ty_info(
                local_decl.ty,
                &mut ty_infos,
                bitfields,
                prim,
                def_id,
                arena,
                tcx,
            );
            if let Some(ty) = points_to::unwrap_ptr(local_decl.ty) {
                compute_ty_info(ty, &mut ty_infos, bitfields, prim, def_id, arena, tcx);
            }
        }
    }

    ty_infos
}

fn compute_ty_info<'a, 'tcx>(
    ty: Ty<'tcx>,
    tys: &mut HashMap<Ty<'tcx>, &'a TyInfo<'a>>,
    bitfields: &HashMap<LocalDefId, HashMap<String, usize>>,
    prim: &'a TyInfo<'a>,
    def_id: DefId,
    arena: &'a Arena<TyInfo<'a>>,
    tcx: TyCtxt<'tcx>,
) -> &'a TyInfo<'a> {
    if let Some(ty_info) = tys.get(&ty) {
        return ty_info;
    }
    let ty_info = match ty.kind() {
        TyKind::Adt(adt_def, generic_args) => {
            if ty.is_c_void(tcx) {
                prim
            } else {
                let ts = adt_def.variants().iter().flat_map(|variant| {
                    variant
                        .fields
                        .iter()
                        .map(|field| field.ty(tcx, generic_args))
                });
                let bitfield = adt_def
                    .did()
                    .as_local()
                    .and_then(|local_def_id| bitfields.get(&local_def_id));
                compute_ty_info_iter(ts, tys, bitfield, bitfields, prim, def_id, arena, tcx)
            }
        }
        TyKind::Array(ty, len) => {
            let t = compute_ty_info(*ty, tys, bitfields, prim, def_id, arena, tcx);
            let len = len
                .eval(tcx, tcx.param_env(def_id))
                .try_to_scalar_int()
                .unwrap()
                .try_to_u64()
                .unwrap() as usize;
            arena.alloc(TyInfo::Array(t, len))
        }
        TyKind::Tuple(ts) => {
            compute_ty_info_iter(ts.iter(), tys, None, bitfields, prim, def_id, arena, tcx)
        }
        _ => prim,
    };
    tys.insert(ty, ty_info);
    assert_ne!(ty_info.len(), 0);
    ty_info
}

#[inline]
#[allow(clippy::too_many_arguments)]
fn compute_ty_info_iter<'a, 'tcx, I: Iterator<Item = Ty<'tcx>>>(
    ts: I,
    tys: &mut HashMap<Ty<'tcx>, &'a TyInfo<'a>>,
    bitfield: Option<&HashMap<String, usize>>,
    bitfields: &HashMap<LocalDefId, HashMap<String, usize>>,
    prim: &'a TyInfo<'a>,
    def_id: DefId,
    arena: &'a Arena<TyInfo<'a>>,
    tcx: TyCtxt<'tcx>,
) -> &'a TyInfo<'a> {
    let mut len = 0;
    let mut fields = vec![];
    for ty in ts {
        let ty_info = compute_ty_info(ty, tys, bitfields, prim, def_id, arena, tcx);
        fields.push((len, ty_info));
        len += ty_info.len();
    }
    if let Some(fs) = bitfield {
        for _ in fs {
            fields.push((len, prim));
            len += 1;
        }
    }
    if len == 0 {
        prim
    } else {
        arena.alloc(TyInfo::Struct(len, fields))
    }
}

#[allow(variant_size_differences)]
pub enum TyInfo<'a> {
    Primitive,
    Array(&'a TyInfo<'a>, usize),
    Struct(usize, Vec<(usize, &'a TyInfo<'a>)>),
}

impl std::fmt::Debug for TyInfo<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Primitive => write!(f, "*"),
            Self::Array(t, len) => write!(f, "[{:?} * {}]", t, len),
            Self::Struct(len, fields) => {
                write!(f, "[{}", len)?;
                for (i, ty_info) in fields {
                    let sep = if *i == 0 { ";" } else { "," };
                    write!(f, "{} {}: {:?}", sep, i, ty_info)?;
                }
                write!(f, "]")
            }
        }
    }
}

impl TyInfo<'_> {
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
