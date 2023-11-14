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
  {K : Type _} [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {W : Type _} [Vec K W]
  
@[fprop]
theorem Function.foldl.arg_finit.IsDifferentiable_rule 
  (f : W → (ι → X)) (op : Y → X → Y) (init : W → Y)
  (hf : IsDifferentiable K f) (hop : IsDifferentiable K (fun (y,x) => op y x)) (hinit : IsDifferentiable K init)
  : IsDifferentiable K (fun w => Function.foldl (f w) op (init w)) := by sorry_proof

@[ftrans]
theorem Function.foldl.arg_finit.fwdCDeriv_rule
  (f : W → (ι → X)) (op : Y → X → Y) (init : W → Y)
  (hf : IsDifferentiable K f) (hop : IsDifferentiable K (fun ((y,x) : Y×X) => op y x)) (hinit : IsDifferentiable K init)
  : fwdCDeriv K (fun w => Function.foldl (f w) op (init w)) 
    =
    fun w dw => 
      let fdf := fwdCDeriv K f w dw
      let initdinit := fwdCDeriv K init w dw
      let dop := fun (y,dy) (x,dx) => fwdCDeriv K (fun (y,x) => op y x) (y,x) (dy,dx)
      Function.foldl (fun i => (fdf.1 i, fdf.2 i)) dop initdinit
      := by sorry_proof

end OnEnumType 

section OnIndexType

variable [Index ι]

/-- Reverse derivative of `Function.foldl` w.r.t. `f` and `init`. It is implemented using `Array`.

  TODO: 
    1. needs beter implementation but that requires refining EnumType and Index
    2. add a version with DataArray
-/
def Function.foldl.revDeriv_arrayImpl [Add α] [Add β]
  (f : ι → α) (op : β → α → β) (dop : β → α → β → β×α) (init : β) : β × (β → Array α×β) := Id.run do
  let n := (Index.size ι).toNat
  let mut bs : Array β := .mkEmpty n
  let mut b := init
  for i in fullRange ι do
    bs := bs.push b
    b := op b (f i)
  (b, 
   fun db => Id.run do
     let mut das : Array α := .mkEmpty n
     let mut db : β := db
     for i in [0:n] do
       let j : ι := fromIdx ⟨n.toUSize-i.toUSize-1, sorry_proof⟩
       let aj := f j
       let bj := bs[n-i-1]'sorry_proof
       let (db',da) := dop bj aj db
       das := das.push da
       db := db'
     das := das.reverse
     (das, db))


/-- Reverse derivative of `Function.foldl` w.r.t. `f` and `init`. It is implemented using `Array`.

  TODO: 
    1. needs beter implementation but that requires refining EnumType and Index
    2. add a version with DataArray
-/
def Function.foldl.revDeriv_dataArrayImpl [Add α] [Add β] [PlainDataType α] [PlainDataType β]
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


#eval Function.foldl.revDeriv_arrayImpl (fun i : Idx 3 => (i.toFloat + 5)) (fun x y => x * y) (fun x y dxy => (y*dxy, x*dxy)) 1 |>.snd 1
#eval Function.foldl.revDeriv_dataArrayImpl (fun i : Idx 3 => (i.toFloat + 5)) (fun x y => x * y) (fun x y dxy => (y*dxy, x*dxy)) 1 |>.snd 1
#eval Function.foldl.revDeriv_dataArrayImpl_alt (fun i : Idx 3 => (i.toFloat + 5)) (fun x y => x * y) (fun x y dxy => (y*dxy, x*dxy)) 1 |>.snd 1


variable
  {K : Type _} [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  

@[fprop]
theorem Function.foldl.arg_finit.HasAdjDiff_rule 
  (f : W → (ι → X)) (op : Y → X → Y) (init : W → Y)
  (hf : HasAdjDiff K f) (hop : HasAdjDiff K (fun (y,x) => op y x)) (hinit : HasAdjDiff K init)
  : HasAdjDiff K (fun w => Function.foldl (f w) op (init w)) := by sorry_proof

@[ftrans]
theorem Function.foldl.arg_finit.revCDeriv_rule [PlainDataType X] [PlainDataType Y]
  (f : W → (ι → X)) (op : Y → X → Y) (init : W → Y)
  (hf : HasAdjDiff K f) (hop : HasAdjDiff K (fun (y,x) => op y x)) (hinit : HasAdjDiff K init)
  : revCDeriv K (fun w => Function.foldl (f w) op (init w)) 
    =
    fun w => 
      let fdf := revCDeriv K f w
      let initdinit := revCDeriv K init w
      let dop := fun y x => gradient K (fun (y,x) => op y x) (y,x)
      let ydy := Function.foldl.revDeriv_dataArrayImpl fdf.1 op dop initdinit.1
      (ydy.1,
       fun dy => 
         let dfdinit := ydy.2 dy
         let dw₁ := fdf.2 (fun i => dfdinit.1[i])
         let dw₂ := initdinit.2 dfdinit.2
         dw₁ + dw₂)
      := by sorry_proof

end OnIndexType



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
  (hf : IsDifferentiable K f) (hop : IsDifferentiable K (fun (x,y) => op x y)) (hdefault : IsDifferentiable K default)
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


/--
  -- WARNING: `dx'` and `dw` behave differently
     - `df'` computes gradient in `dx'` 
     - `df'` computes update to gradient in `dw` 
  
  The value of `df'` should be:
    df' = fun w i x dx' dw => 
      ((∇ (x':=x;dx'), f w i x'), (dw + ∇ (w':=w;dx'), f w' i x))
-/
def ForIn.arg_bf.revDeriv_dataArrayImpl [Index ι] [PlainDataType X] [PlainDataType W] [Zero X] [Zero W]
  (init : X) (f : W → ι → X → X) (df' : W → ι → X → X → W → X×W) (w : W)
  : X×(X→X×W) :=
  let n := Index.size ι
  if n = 0 then
    (init, fun _ => 0)
  else Id.run do
    -- forward pass
    let mut xs : DataArray X := .mkEmpty n
    let mut x := init
    for i in fullRange ι do
      xs := xs.push x
      x := f w i x
    (x, fun dx' => Id.run do
      -- backward pass
      -- TODO: implemente reverse ranges!
      let mut dx' := dx'
      let mut dw : W := 0
      for i in [0:n.toNat] do
        let j' : Idx n := ⟨n-i.toUSize-1,sorry_proof⟩
        let j : ι := fromIdx j'
        let xj := xs.get ⟨j'.1, sorry_proof⟩
        let (dx'',dw') := df' w j xj dx' dw
        dx' := dx''
        dw := dw'
      (dx',dw))


@[ftrans]
theorem ForIn.forIn.arg_bf.revDerivM_rule' [Index ι] [PlainDataType X] [PlainDataType W]
  (init : W → X) (f : W → ι → X → X)
  (hinit : HasAdjDiff K init) (hf : ∀ i, HasAdjDiff K (fun (w,x) => f w i x))
  : revCDeriv K (fun w => forIn (m:=Id) (fullRange ι) (init w) (fun i y => do pure PUnit.unit; pure <| ForInStep.yield (f w i y))) 
    =
    fun w => 
      let initdinit := revCDeriv K init w
      let forInBody := hold f
      let df' := hold fun w i x dx' dw =>
        let f' : W×X → X := fun (w',x') => f w' i x'
        let dwx' := gradient K f' (w,x) dx'
        (dwx'.2, dw + dwx'.1)
      let xdforIn := ForIn.arg_bf.revDeriv_dataArrayImpl initdinit.1 forInBody df' w
      (xdforIn.1, 
       fun dx' => 
         let (dx'', dw) := xdforIn.2 dx'
         initdinit.2 dx'' + dw)
  := sorry_proof

#eval 
  (⊞ i => gradient Float (fun (x : (Float^Idx 3)×Float) => x.2 * x.1[i]) (⊞[5.0,6,7], 42.0) 1.0)
    rewrite_by 
      unfold gradient
      ftrans
      simp


#check Nat


example (i : Idx 3) : HasAdjDiff Float fun (x : Float ^ Idx 3) => x[i] := by fprop
example (i : Idx 3) : HasAdjDiff Float fun (x : Float ^ Idx 3 × Float) => x.1[i] := by fprop

set_option trace.Meta.Tactic.fprop.step true in
example (i : Idx (Nat.toUSize 3)) : HasAdjDiff Float fun (x : ((typeOf (5.0 : Float)) ^ Idx (Nat.toUSize 3)) × Float) => x.1[i] := by fprop

set_option pp.funBinderTypes true in
-- set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.simp.discharge true in
#eval
  ((gradient Float (fun x : Float ^ Idx 3 => Id.run do
    let mut y := 1.0
    for i in fullRange (Idx 3) do
      y := y * x[i]
    y))
    rewrite_by
      unfold gradient
      ftrans
      simp (config:= {zeta:=false}) only [revDerivM]
      ftrans
      unfold gradient
      ftrans
      ftrans)
  ⊞[5.0,6,7] 1

-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
#eval
  ((gradient Float (fun x : Float ^ Idx 3 => Id.run do
    let mut y := 1.0
    for i in fullRange (Idx 3) do
      let a := y * y
      y := y * x[i] * a
    y))
    rewrite_by
      unfold gradient
      ftrans
      simp (config:= {zeta:=false}) only [revDerivM]
      ftrans
      unfold gradient
      ftrans
      ftrans)
  ⊞[5.0,6,7] 1

      
-- (fun x => Id.run do
--       let (y₀,dinit') := revCDeriv K init x
--       let (y,ys) ← forIn (Std.Range.mk start stop step) (y₀,#[]) (fun i (y,ys) => 
--         let y' := f x i y
--         .yield (y', ys.push y'))
--       pure (y, 
--             fun dy => do
--               let (dx,dy) ← forIn (Std.Range.mk start stop step) ((0:X),dy) (fun i (dx,dy) => do 
--                 let j := stop - ((i-start) + 1)
--                 let yᵢ : Y := ys[j]!
--                 let (dx',dy) := (revCDeriv K (fun (xy : X×Y) => f xy.1 i xy.2) (x,yᵢ)).2 dy
--                 .yield (dx + dx', dy))
--               pure (dx + dinit' dy))) :=
-- by
--   sorry_proof




/-- Reverse derivative of `Function.foldl` w.r.t. `f` and `init`. It is implemented using `Array`.

  TODO: 
    1. needs beter implementation but that requires refining EnumType and Index
    2. add a version with DataArray
-/
def Function.reduceD.revDeriv_dataArrayImpl_alt [PlainDataType X]
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
       
       
       )
  -- let bbs := Function.reduceD f (fun (b,bs) a => (op b a, bs.push b)) (default, DataArray.mkEmpty n)
  -- let b := bbs.1
  -- let bs := bbs.2
  -- (b, 
  --  fun db => Id.run do
  --    let dbdas := Function.foldl 
  --      (fun i : Idx n => 
  --        let j : Idx n := ⟨n-i.1-1, sorry_proof⟩
  --        (f (fromIdx j), bs.get ⟨j.1, sorry_proof⟩))
  --      (fun (db,das) (aj,bj) => 
  --        let (db', da) := dop bj aj db
  --        (db', das.push da))
  --      (db, DataArray.mkEmpty n)
  --    let db := dbdas.1
  --    let das := dbdas.2
  --    let das := das.reverse
  --    (⟨das, sorry_proof⟩, db))
/--
TODO: 
    1. needs beter implementation but that requires refining EnumType and Index
    2. add a version with DataArray
-/
def Function.reduceD.revDeriv_dataArrayImpl_alt [PlainDataType X]
  (f : ι → X) (op : X → X → X) (dop : X → X → X → X×X) (default : X) : X × (X → DataArrayN X ι) := Id.run do
  let n := Index.size ι
  let bbs := Function.reduceD f (fun (b,bs) a => (op b a, bs.push b)) (default, DataArray.mkEmpty n)
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

-- /--
--   TODO: needs beter implementation but that requires refining EnumType and Index
--   -/
-- def Function.reduceD (f : ι → α) (op : α → α → α) (default : α) : α := Id.run do
--   let n := Index.size ι
--   if n = 0 then
--     return default
--   let mut a := f (fromIdx ⟨0,sorry_proof⟩)
--   for i in [1:n.toNat] do
--     a := op a (f (fromIdx ⟨i.toUSize,sorry_proof⟩))
--   return a


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
