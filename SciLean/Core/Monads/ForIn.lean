import SciLean.Core.Monads.FwdDerivMonad
import SciLean.Core.Monads.Id
import SciLean.Core.Monads.MProd
import SciLean.Core.Monads.ForInStep

import SciLean.Data.DataArray

set_option linter.unusedVariables false

open SciLean

section OnVec

variable 
  {K : Type} [IsROrC K]
  {m m'} [Monad m] [Monad m'] [FwdDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {ρ : Type} {α : Type _} [ForIn m ρ α] [ForIn m' ρ α] {β : Type _}
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]

--------------------------------------------------------------------------------
-- ForIn.forIn -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- we need some kind of lawful version of `ForIn` to be able to prove this
@[fprop]
theorem ForIn.forIn.arg_bf.IsDifferentiableM_rule
  (range : ρ) (init : X → Y) (f : X → α → Y → m (ForInStep Y))
  (hinit : IsDifferentiable K init) (hf : ∀ a, IsDifferentiableM K (fun (xy : X×Y) => f xy.1 a xy.2))
  : IsDifferentiableM K (fun x => forIn range (init x) (f x)) := sorry_proof


-- we need some kind of lawful version of `ForIn` to be able to prove this
@[ftrans]
theorem ForIn.forIn.arg_bf.fwdDerivM_rule
  (range : ρ) (init : X → Y) (f : X → α → Y → m (ForInStep Y))
  (hinit : IsDifferentiable K init) (hf : ∀ a, IsDifferentiableM K (fun (xy : X×Y) => f xy.1 a xy.2))
  : fwdDerivM K (fun x => forIn range (init x) (f x)) 
    =
    (fun x dx => do
      let ydy₀ := fwdCDeriv K init x dx
      forIn range ydy₀
        fun a ydy => do 
          let ydy ← fwdDerivM K (fun (xy : X×Y) => f xy.1 a xy.2) (x,ydy.1) (dx,ydy.2)
          return ForInStep.return2 ydy) :=
by
  sorry_proof

-- Proof that the above theorem is true for the range [0:3] and function that does not break the for loop
example
  (init : X → Y) (f : X → Nat → Y → m Y)
  (hinit : IsDifferentiable K init) (hf : ∀ a, IsDifferentiableM K (fun (xy : X×Y) => f xy.1 a xy.2))
  : fwdDerivM K (fun x => forIn [0:3] (init x) (fun i y => do pure (ForInStep.yield (← f x i y)))) 
    =
    (fun x dx => do
      let ydy₀ := fwdCDeriv K init x dx
      forIn [0:3] ydy₀
        fun a ydy => do 
          let ydy ← fwdDerivM K (fun (xy : X×Y) => f xy.1 a xy.2) (x,ydy.1) (dx,ydy.2)
          return .yield ydy) :=
by
  funext
  simp [forIn,Std.Range.forIn,Std.Range.forIn.loop,Std.Range.forIn.loop.match_1]
  ftrans
  rfl
    

--------------------------------------------------------------------------------


end OnVec


--------------------------------------------------------------------------------


section OnSemiInnerProductSpace

variable 
  {K : Type} [IsROrC K]
  {m m'} [Monad m] [Monad m'] [RevDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {ρ : Type} {α : Type _} [ForIn m ρ α] [ForIn m' ρ α] {β : Type _}
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {W : Type} [SemiInnerProductSpace K W]


--------------------------------------------------------------------------------
-- ForIn.forIn -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- we need some kind of lawful version of `ForIn` to be able to prove this
@[fprop]
theorem ForIn.forIn.arg_bf.HasAdjDiffM_rule
  (range : ρ) (init : X → Y) (f : X → α → Y → m (ForInStep Y))
  (hinit : HasAdjDiff K init) (hf : ∀ a, HasAdjDiffM K (fun (xy : X×Y) => f xy.1 a xy.2))
  : HasAdjDiffM K (fun x => forIn range (init x) (f x)) := sorry_proof

@[fprop]
theorem ForIn.forIn.arg_bf.HasAdjDiff_rule [ForIn Id ρ α]
  (range : ρ) (init : X → Y) (f : X → α → Y → (ForInStep Y))
  (hinit : HasAdjDiff K init) (hf : ∀ a, HasAdjDiff K (fun (xy : X×Y) => f xy.1 a xy.2))
  : HasAdjDiff K (fun x => forIn (m:=Id) range (init x) (f x)) := sorry_proof


/-- This version of reverse derivative of a for loop builds a big lambda function
  for the reverse pass during the forward pass. This is probably ok in for loops
  where each iteration is very costly and there are not many iterations.
-/
theorem ForIn.forIn.arg_bf.revDerivM_rule_lazy
  (range : ρ) (init : X → Y) (f : X → α → Y → m (ForInStep Y))
  (hinit : HasAdjDiff K init) (hf : ∀ a, HasAdjDiffM K (fun (xy : X×Y) => f xy.1 a xy.2))
  : revDerivM K (fun x => forIn range (init x) (f x)) 
    =
    (fun x => do
      let ydinit := revCDeriv K init x
      let ydf ← forIn range (ydinit.1, fun (dy:Y) => pure (f:=m') ((0:X),dy))
        (fun a ydf => do
          let ydf' ← revDerivM K (fun (xy : X×Y) => f xy.1 a xy.2) (x,ydf.1)
          let df : Y → m' (X×Y) := 
            fun dy : Y => do
              let dxy  ← ydf'.2 (.yield dy)
              let dxy' ← ydf.2 dxy.2
              pure (dxy.1 + dxy'.1, dxy'.2)
          match ydf'.1 with
          | .yield y => pure (ForInStep.yield (y, df))
          | .done  y => pure (ForInStep.done (y, df)))
      pure (ydf.1, 
            fun dy => do
              let dxy ← ydf.2 dy
              pure (dxy.1 + ydinit.2 dxy.2))) :=
by
  sorry_proof


/-- Forward pass of a for loop implemented using `DataArray`
  -/
def ForIn.forIn.arg_bf.fwdPass_dataArrayImpl [Index ι] [PlainDataType X]
  (init : X) (f : ι → X → ForInStep X)
  : X×DataArray X := Id.run do
  let n := Index.size ι

  -- forward pass
  let mut xs : DataArray X := .mkEmpty n
  forIn (fullRange ι) (init, DataArray.mkEmpty (α:=X) n)
    fun i (x,xs) =>
      let xs := xs.push x
      match f i x with
      | .done x' => .done (x', xs)
      | .yield x' => .yield (x', xs)



/-- Reverse pass of a for loop implemented using `DataArray`

  See `Forin.arg_bf.revCDeriv_rule_dataArrayImpl` how it relates to reverse derivative of for loop.

  TODO: Index shoud support iterating in reverse order

  WARNING: `dx'` and `dw` behave differently
     - `df'` computes gradient in `dx'` 
     - `df'` computes update to gradient in `dw` 
  
  The value of `df'` should be:
    df' = fun w i x dx' dw => 
      ((∇ (x':=x;dx'), f w i x'), (dw + ∇ (w':=w;dx'), f w' i x))
  -/
def ForIn.forIn.arg_bf.revPass_dataArrayImpl [Index ι] [PlainDataType X] [PlainDataType W] [Zero X] [Zero W]
  (df' : ι → X → W → X → W×X) (xs : DataArray X) (dx' : X) : W×X := Id.run do
  let n := xs.size
  let mut dwx := (0,dx')
  for i in [0:n.toNat] do
    let i' : Idx xs.size := ⟨n-i.toUSize-1,sorry_proof⟩
    let j : ι := fromIdx ⟨n-i.toUSize-1,sorry_proof⟩
    let xj := xs.get i'
    dwx := df' j xj dwx.1 dwx.2
  dwx



/-- Reverse derivative of a for loop

  WARNING: `dx'` and `dw` behave differently
     - `df'` computes gradient in `dx'` 
     - `df'` computes update to gradient in `dw` 
  
  The value of `df'` should be:
    df' = fun w i x dw dx' => 
      ((∇ (x':=x;dx'), f w i x'), (dw + ∇ (w':=w;dx'), f w' i x))
-/
def ForIn.arg_bf.revDeriv_dataArrayImpl [Index ι] [PlainDataType X] [PlainDataType W] [Zero X] [Zero W]
  (init : X) (f : ι → X → X) (df' : ι → X → W → X → W×X)
  : X×(X→W×X) :=
  Id.run do
    let n := Index.size ι
    -- forward pass
    let mut xs : DataArray X := .mkEmpty n
    let mut x := init
    for i in fullRange ι do
      xs := xs.push x
      x := f i x
    (x, fun dx' => ForIn.forIn.arg_bf.revPass_dataArrayImpl df' xs dx')


-- /-- The do notation leaves the for loop body in a strange form `do pure PUnit.unit; pure <| ForInStep.yield (f w i y))`
--   Marking this theorem with `ftrans` is a bit of a hack. It normalizes the body to `ForInStep.yield (f w i y)`.
--   -/
-- @[ftrans]
-- theorem ForIn.forIn.arg_bf.revDerivM_rule_normalization [Index ι]
--   (init : W → X) (f : W → ι → X → X)
--   : revDerivM K (fun w => forIn (m:=Id) (fullRange ι) (init w) (fun i y => do pure PUnit.unit; pure <| ForInStep.yield (f w i y)))
--     =
--     revCDeriv K (fun w => forIn (m:=Id) (fullRange ι) (init w) (fun i y => ForInStep.yield (f w i y))) := by rfl



-- /-- The do notation leaves the for loop body in a strange form `do pure PUnit.unit; pure <| ForInStep.yield (f w i y))`
--   Marking this theorem with `ftrans` is a bit of a hack. It normalizes the body to `ForInStep.yield (f w i y)`.
--   -/
-- @[ftrans]
-- theorem ForIn.forIn.arg_bf.revCDeriv_rule_normalization [Index ι]
--   (init : W → X) (f : W → ι → X → X)
--   : revCDeriv K (fun w => forIn (m:=Id) (fullRange ι) (init w) (fun i y => do pure PUnit.unit; pure <| ForInStep.yield (f w i y)))
--     =
--     revCDeriv K (fun w => forIn (m:=Id) (fullRange ι) (init w) (fun i y => ForInStep.yield (f w i y))) := by rfl


@[ftrans]
theorem ForIn.forIn.arg_bf.revCDeriv_rule_def [Index ι] [PlainDataType X] [PlainDataType W]
  (init : W → X) (f : W → ι → X → ForInStep X)
  (hinit : HasAdjDiff K init) (hf : ∀ i, HasAdjDiff K (fun (w,x) => f w i x))
  : revCDeriv K (fun w => forIn (m:=Id) (fullRange ι) (init w) (fun i y => f w i y))
    =
    fun w => (Id.run do
      let n := Index.size ι
      let initdinit := revCDeriv K init w

      let xxs := ForIn.forIn.arg_bf.fwdPass_dataArrayImpl initdinit.1 (f w)
      -- forward pass
      let mut xs := xxs.2
      let mut x := xxs.1

      let revPassBody := hold fun i x dw dx' =>
        let dwx' := gradient K (fun (w',x') => (f w' i x').val) (w,x) dx'
        (dw + dwx'.1, dwx'.2)

      (x, 
       fun dx' =>
         -- reverse pass
         let dwx' := ForIn.forIn.arg_bf.revPass_dataArrayImpl revPassBody xs dx'
         initdinit.2 dwx'.2 + dwx'.1)) :=
by
  sorry_proof


-- @[ftrans]
-- disables for now because downstream `ForInStep.yield.arg_a0.revDerivUpdate_rule` is 
-- causing some issues with Id monad and congr lemmas in simp
theorem ForIn.forIn.arg_bf.revCDeriv_rule_def' [Index ι] [PlainDataType X] [PlainDataType W]
  (init : W → X) (f : W → ι → X → ForInStep X)
  (hinit : HasAdjDiff K init) (hf : ∀ i, HasAdjDiff K (fun (w,x) => f w i x))
  : revCDeriv K (fun w => forIn (m:=Id) (fullRange ι) (init w) (fun i y => f w i y))
    =
    fun w => (Id.run do
      let n := Index.size ι
      let initdinit := revCDeriv K init w

      let xxs := ForIn.forIn.arg_bf.fwdPass_dataArrayImpl initdinit.1 (f w)
      -- forward pass
      let mut xs := xxs.2
      let mut x := xxs.1

      let revPassBody := hold fun i x dw dx' =>
        (revDerivUpdate K (fun (w',x') => (f w' i x').val) (w,x)).2 dx' (dw,0)

      (x, 
       fun dx' =>
         -- reverse pass
         let dwx' := ForIn.forIn.arg_bf.revPass_dataArrayImpl revPassBody xs dx'
         initdinit.2 dwx'.2 + dwx'.1)) :=
by
  sorry_proof


end OnSemiInnerProductSpace




