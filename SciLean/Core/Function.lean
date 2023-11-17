import SciLean.Core.FunctionTransformations
import SciLean.Core.Monads
import SciLean.Data.Function
import SciLean.Data.DataArray 
import SciLean.Core.FloatAsReal
import SciLean.Tactic.LetEnter

open SciLean

set_option linter.unusedVariables false 

variable 
  {α β ι : Type _}

--------------------------------------------------------------------------------
-- Function.foldl --------------------------------------------------------------
--------------------------------------------------------------------------------

section OnEnumType 

variable [EnumType ι] 

variable
  {K : Type} [IsROrC K]
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]
  {W : Type} [Vec K W]
  
@[fprop]
theorem Function.foldl.arg_finit.IsDifferentiable_rule 
  (f : W → (ι → X)) (op : Y → X → Y) (init : W → Y)
  (hf : ∀ i, IsDifferentiable K (f · i)) (hop : IsDifferentiable K (fun (y,x) => op y x)) (hinit : IsDifferentiable K init)
  : IsDifferentiable K (fun w => Function.foldl (f w) op (init w)) := 
by 
  unfold foldl; unfold foldlM
  fprop

@[ftrans]
theorem Function.foldl.arg_finit.fwdCDeriv_rule
  (f : W → (ι → X)) (op : Y → X → Y) (init : W → Y)
  (hf : ∀ i, IsDifferentiable K (f · i)) (hop : IsDifferentiable K (fun ((y,x) : Y×X) => op y x)) (hinit : IsDifferentiable K init)
  : fwdCDeriv K (fun w => Function.foldl (f w) op (init w)) 
    =
    fun w dw => 
      let fdf := fun i => fwdCDeriv K (f · i) w dw
      let initdinit := fwdCDeriv K init w dw
      let dop := fun (y,dy) (x,dx) => fwdCDeriv K (fun (y,x) => op y x) (y,x) (dy,dx)
      Function.foldl fdf dop initdinit := 
by 
  unfold foldl; unfold foldlM
  ftrans; rfl

end OnEnumType 

section OnIndexType

variable [Index ι]

/-- Forward pass for reverse derivative of `Function.foldl` w.r.t. `f` and `init`. It is implemented using `DataArray`.

  TODO: 
    1. needs beter implementation but that requires refining EnumType and Index
    2. add a version with DataArray
-/
def Function.foldl.arg_finit.revDeriv_fwdPass [PlainDataType β]
  (f : ι → α) (op : β → α → β) (init : β) : β × DataArrayN β ι := Id.run do
  let n := Index.size ι
  let mut bs : DataArray β := .mkEmpty n
  let mut b := init
  for i in fullRange ι do
    bs := bs.push b
    b := op b (f i)
  (b, ⟨bs, sorry_proof⟩)


/-- Reverse pass for reverse derivative of `Function.foldl` w.r.t. `f` and `init`. It is implemented using `DataArray`.

  `f'` are intermediate values of the forward pass 
-/
def Function.foldl.arg_finit.revDeriv_revPass [PlainDataType α] [PlainDataType β]
  (f : ι → α) (f' : ι → β) (dop : β → α → β → β×α) (db : β) : DataArrayN α ι×β := Id.run do
   let n := Index.size ι
   let mut das : DataArray α := .mkEmpty n
   let mut db : β := db
   for i in [0:n.toNat] do
     let j' : Idx n := ⟨n-i.toUSize-1, sorry_proof⟩
     let j : ι := fromIdx j'
     let aj := f j
     let bj := f' j
     let (db',da) := dop bj aj db
     das := das.push da
     db := db'
   das := das.reverse
   (⟨das, sorry_proof⟩, db)


/-- Reverse derivative of `Function.foldl` w.r.t. `f` and `init`. It is implemented using `Array`.

  TODO: 
    1. needs beter implementation but that requires refining EnumType and Index
    2. add a version with DataArray
-/
def Function.foldl.arg_finit.revDeriv_dataArrayImpl [Add α] [Add β] [PlainDataType α] [PlainDataType β]
  (f : ι → α) (op : β → α → β) (dop : β → α → β → β×α) (init : β) : β × (β → DataArrayN α ι×β) := Id.run do
  let n := Index.size ι
  let mut bs : DataArray β := .mkEmpty n
  let mut b := init
  for i in fullRange ι do
    bs := bs.push b
    b := op b (f i)
  (b, 
   fun db => Id.run do
     let mut das : DataArray α := .mkEmpty n
     let mut db : β := db
     for i in [0:n.toNat] do
       let j' : Idx n := ⟨n-i.toUSize-1, sorry_proof⟩
       let j : ι := fromIdx j'
       let aj := f j
       let bj := bs.get ⟨j'.1, sorry_proof⟩
       let (db',da) := dop bj aj db
       das := das.push da
       db := db'
     das := das.reverse
     (⟨das, sorry_proof⟩, db))

/-- Reverse derivative of `Function.foldl` w.r.t. `f` and `init`. It is implemented using `Array`.

  TODO: 
    1. needs beter implementation but that requires refining EnumType and Index
    2. add a version with DataArray
-/
def Function.foldl.revDeriv_dataArrayImpl_alt [Add α] [Add β] [PlainDataType α] [PlainDataType β]
  (f : ι → α) (op : β → α → β) (dop : β → α → β → β×α) (init : β) : β × (β → DataArrayN α ι×β) := Id.run do
  let n := Index.size ι
  let bbs := Function.foldl f (fun (b,bs) a => (op b a, bs.push b)) (init, DataArray.mkEmpty n)
  let b := bbs.1
  let bs := bbs.2
  (b, 
   fun db => Id.run do
     let dbdas := Function.foldl 
       (fun i : Idx n => 
         let j : Idx n := ⟨n-i.1-1, sorry_proof⟩
         (f (fromIdx j), bs.get ⟨j.1, sorry_proof⟩))
       (fun (db,das) (aj,bj) => 
         let (db', da) := dop bj aj db
         (db', das.push da))
       (db, DataArray.mkEmpty n)
     let db := dbdas.1
     let das := dbdas.2
     let das := das.reverse
     (⟨das, sorry_proof⟩, db))


variable
  {K : Type} [IsROrC K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {W : Type} [SemiInnerProductSpace K W]
  

@[fprop]
theorem Function.foldl.arg_finit.HasAdjDiff_rule 
  (f : W → (ι → X)) (op : Y → X → Y) (init : W → Y)
  (hf : ∀ i, HasAdjDiff K (f · i)) (hop : HasAdjDiff K (fun (y,x) => op y x)) (hinit : HasAdjDiff K init)
  : HasAdjDiff K (fun w => Function.foldl (f w) op (init w)) := 
by 
  unfold foldl; unfold foldlM
  fprop


@[ftrans]
theorem Function.foldl.arg_finit.revCDeriv_rule_dataArrayImpl [PlainDataType X] [PlainDataType Y] [PlainDataType W]
  (f : W → (ι → X)) (op : Y → X → Y) (init : W → Y)
  (hf : ∀ i, HasAdjDiff K (f · i)) (hop : HasAdjDiff K (fun (y,x) => op y x)) (hinit : HasAdjDiff K init)
  : revCDeriv K (fun w => Function.foldl (f w) op (init w))
    =
    fun w => 
      let fdf := revCDeriv K f w
      let initdinit := revCDeriv K init w
      let dop : Y → X → Y → Y×X := hold fun (y : Y) (x : X) => gradient K (fun (y,x) => op y x) (y,x)
      let bbs := Function.foldl.arg_finit.revDeriv_fwdPass fdf.1 op initdinit.1
      (bbs.1,
       fun dy => 
         let dfdinit := Function.foldl.arg_finit.revDeriv_revPass fdf.1 (fun (i : ι) => bbs.2[i]) dop dy
         fdf.2 (fun i => dfdinit.1[i]) + initdinit.2 dfdinit.2) := 
by 
  unfold foldl; unfold foldlM
  unfold Function.foldl.arg_finit.revDeriv_fwdPass
  unfold Function.foldl.arg_finit.revDeriv_revPass
  set_option trace.Meta.Tactic.simp.discharge true in
  set_option trace.Meta.Tactic.simp.unify true in
  -- set_option trace.Meta.Tactic.ftrans.step true in
  conv =>
    lhs
    ftrans
    ftrans
    simp (config:={zeta:=false})
  sorry_proof

end OnIndexType



-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.unify true in
#eval
  ((gradient Float fun (x : Float ^ Idx 3) => Function.foldl (fun (i : Idx 3) => x[i]) (·*·) (1.0 : Float)) ⊞[5.0,6,7]) 1.0
  rewrite_by
    unfold gradient
    ftrans
    unfold gradient
    ftrans
    ftrans
    ftrans


--------------------------------------------------------------------------------
-- Function.reduceD ------------------------------------------------------------
--------------------------------------------------------------------------------


section OnVec
variable
  [Index ι]
  {K : Type _} [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {W : Type _} [Vec K W]

@[fprop]
theorem Function.reduceD.arg_fdefault.IsDifferentiable_rule
  (f : W → ι → X) (op : X → X → X) (default : W → X)
  (hf : IsDifferentiable K f) (hop : IsDifferentiable K (fun (x,y) => op x y)) (hdefault : IsDifferentiable K default)
  : IsDifferentiable K (fun w => Function.reduceD (f w) op (default w)) := by sorry_proof

@[ftrans]
theorem Function.reduceD.arg_fdefault.fwdCDeriv_rule
  (f : W → ι → X) (op : X → X → X) (default : W → X)
  (hf : ∀ i, IsDifferentiable K (f · i)) (hop : IsDifferentiable K (fun (x,y) => op x y)) (hdefault : IsDifferentiable K default)
  : fwdCDeriv K (fun w => Function.reduceD (f w) op (default w))
    =
    fun w dw => 
      let fdf := fwdCDeriv K f w dw
      let defaultddefault := fwdCDeriv K default w dw
      let dop := fun (x,dy) (y,dy) => fwdCDeriv K (fun (x,y) => op x y) (x,y) (dx,dy)
      Function.reduceD (fun i => (fdf.1 i, fdf.2 i)) dop defaultddefault
      := by sorry_proof

end OnVec


section OnSemiInnerProductSpace

variable
  [Index ι]
  {K : Type _} [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]


/-- Reverse derivative of `Function.foldl` w.r.t. `f` and `init`. It is implemented using `Array`.

  TODO: 
    1. needs beter implementation but that requires refining EnumType and Index
    2. add a version with DataArray
-/
def Function.reduceD.revDeriv_dataArrayImpl [PlainDataType X]
  (f : ι → X) (op : X → X → X) (dop : X → X → X → X×X) (default : X) : X × (X → DataArrayN X ι) := 
  let n := Index.size ι
  if n = 0 then
    (default, fun _ => 0)
  else Id.run do
  
    -- forward pass
    let mut ys : DataArray X := .mkEmpty n
    let mut y := f (fromIdx ⟨0,sorry_proof⟩)
    for i in [1:n.toNat] do 
      let i : ι := fromIdx ⟨i.toUSize, sorry_proof⟩
      ys := ys.push y
      y := op y (f i)
    (y, 
     fun dy => Id.run do

       -- backward pass
       let mut dxs : DataArray X := .mkEmpty n
       let mut dy := dy
       for i in [0:n.toNat] do 
         let j' : Idx n := ⟨n - i.toUSize - 1, sorry_proof⟩
         let j : ι := fromIdx j'
         let xj := f j
         let yj := ys.get ⟨j'.1, sorry_proof⟩
         let (dy',dx') := dop yj xj dy
         dxs := dxs.push dx'
         dy := dy'
       dxs := dxs.reverse
       return ⟨dxs, sorry_proof⟩)


/-- 
  TODO: needs beter implementation but that requires refining EnumType and Index
  -/
def Function.reduceD.arg_f.revCDeriv [Zero α] 
  (f df : ι → α) (dop : α → α → α → (α×(α→α×α))) (default : α) : α×α :=   
  Function.reduceD (fun i => (f i, df i)) (fun (x,dx) (y,dy) => dop x y dx dy) (default, 0)

@[fprop]
theorem Function.reduceD.arg_fdefault.IsDifferentiable_rule
  (f : W → ι → X) (op : X → X → X) (default : W → X)
  (hf : IsDifferentiable K f) (hop : IsDifferentiable K (fun (x,y) => op x y)) (hdefault : IsDifferentiable K default)
  : IsDifferentiable K (fun w => Function.reduceD (f w) op (default w)) := by sorry_proof

@[ftrans]
theorem Function.reduceD.arg_fdefault.revCDeriv_rule
  (f : W → ι → X) (op : X → X → X) (default : W → X)
  (hf : IsDifferentiable K f) (hop : IsDifferentiable K (fun (x,y) => op x y)) (hdefault : IsDifferentiable K default)
  : revCDeriv K (fun w => Function.reduceD (f w) op (default w))
    =
    fun w dw => 
      let fdf := revCDeriv K f w dw
      let defaultddefault := revCDeriv K default w dw
      let dop := fun (x,dy) (y,dy) => revCDeriv K (fun (x,y) => op x y) (x,y) (dx,dy)
      Function.reduceD (fun i => (fdf.1 i, fdf.2 i)) dop defaultddefault
      := by sorry_proof


end OnSemiInnerProductSpace


