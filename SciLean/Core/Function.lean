import SciLean.Core.FunctionTransformations
import SciLean.Data.Function
import SciLean.Data.DataArray 

open SciLean

set_option linter.unusedVariables false 

variable 
  {α β ι : Type _}

section OnEnumType 

variable [EnumType ι] 

/-- Reverse derivative of `Function.foldl` w.r.t. `f` and `init`. It is implemented using `Array`.

  TODO: 
    1. needs beter implementation but that requires refining EnumType and Index
    2. add a version with DataArray
-/
def Function.foldl.fwdDeriv [Add α] [Add β]
  (f df : ι → α) (dop : β → α → β → α → β×β) (init dinit : β) : β × β := Id.run do
  let mut bdb := (init,dinit)
  for i in fullRange ι do
    bdb := dop bdb.1 (f i) bdb.2 (df i)
  bdb

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
      let dop := fun y x dy dx => fwdCDeriv K (fun (y,x) => op y x) (y,x) (dy,dx)
      Function.foldl.fwdDeriv fdf.1 fdf.2 dop initdinit.1 initdinit.2
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


