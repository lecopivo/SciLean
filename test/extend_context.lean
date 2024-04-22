#exit

-- import SciLean.Core.Meta.ExtendContext

open Lean Meta Qq

open SciLean

set_option pp.universes true

/--
info: newly introduced instances #[SciLean.EnumType.{u, w, w} I, SciLean.SemiInnerProductSpace.{w, v} K X]
-/
#guard_msgs in
#eval show MetaM Unit from
  let u := Level.param `u
  let v := Level.param `v
  let w := Level.param `w
  withLocalDeclQ `K .default q(Type $w) fun K => do
  withLocalDeclQ `r .instImplicit q(IsROrC $K) fun _r => do
  withLocalDeclQ `I .default q(Type $u) fun I => do
  withLocalDeclQ `X .default q(Type $v) fun X => do
    let T := q(($I × $I) → ($I ⊕ $I) → $X)

    withSemiInnerProductSpace K T fun xs => do
      IO.println s!"newly introduced instances {← xs.mapM (fun x => inferType x >>= ppExpr)} "


/--
info: newly introduced instances #[SciLean.EnumType.{u, w, w} I, SciLean.SemiInnerProductSpace.{w, v} K X, SciLean.EnumType.{u, w, w} J]
-/
#guard_msgs in
#eval show MetaM Unit from
  let u := Level.param `u
  let v := Level.param `v
  let w := Level.param `w
  withLocalDeclQ `K .default q(Type $w) fun K => do
  withLocalDeclQ `r .instImplicit q(IsROrC $K) fun _r => do
  withLocalDeclQ `I .default q(Type $u) fun I => do
  withLocalDeclQ `J .default q(Type $u) fun J => do
  withLocalDeclQ `X .default q(Type $v) fun X => do
    let T := q((($I × $I) → ($I ⊕ $I) → $X) × ($J → $X))

    withSemiInnerProductSpace K T fun xs => do
      IO.println s!"newly introduced instances {← xs.mapM (fun x => inferType x >>= ppExpr)} "
