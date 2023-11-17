import SciLean.Core.Monads.FwdDerivMonad
import SciLean.Core.Monads.Id
import SciLean.Data.DataArray

set_option linter.unusedVariables false

namespace SciLean

variable 
  {K : Type _} [IsROrC K]
  
-- This is not true but lets assume it for now
instance [Vec K X] : Vec K (ForInStep X) := sorry

-- This is not true but lets assume it for now
instance [SemiInnerProductSpace K X] : SemiInnerProductSpace K (ForInStep X) := sorry



-- TODO: transport vec structure from Prod
instance [Vec K X] [Vec K Y] : Vec K (MProd X Y) := sorry
instance [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] : SemiInnerProductSpace K (MProd X Y) := sorry


@[fprop]
theorem _root_.MProd.mk.arg_fstsnd.HasAdjDiff_rule 
  [SemiInnerProductSpace K W] [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
  (f : W → X) (g : W → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : HasAdjDiff K (fun w => MProd.mk (f w) (g w)) := by sorry_proof


@[ftrans]
theorem _root_.MProd.mk.arg_fstsnd.revCDeriv_rule
  [SemiInnerProductSpace K W] [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
  (f : W → X) (g : W → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revCDeriv K (fun w => MProd.mk (f w) (g w))
    =
    fun w => 
      let xdf' := revCDeriv K f w
      let ydg' := revCDeriv K g w
      (MProd.mk xdf'.1 ydg'.1, 
       fun dxy => 
         xdf'.2 dxy.1 + ydg'.2 dxy.2) := 
by 
  sorry_proof


@[fprop]
theorem _root_.MProd.fst.arg_self.HasAdjDiff_rule 
  [SemiInnerProductSpace K W] [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
  (f : W → MProd X Y) (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun w => (f w).1) := by sorry_proof

@[ftrans]
theorem _root_.MProd.fst.arg_self.revCDeriv_rule 
  [SemiInnerProductSpace K W] [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
  (f : W → MProd X Y) (hf : HasAdjDiff K f)
  : revCDeriv K (fun w => (f w).1)
    =
    fun w => 
      let xydxy := revCDeriv K f w
      (xydxy.1.1, fun dw => xydxy.2 (MProd.mk dw 0)) := by sorry_proof

@[fprop]
theorem _root_.MProd.snd.arg_self.HasAdjDiff_rule 
  [SemiInnerProductSpace K W] [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
  (f : W → MProd X Y) (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun w => (f w).2) := by sorry_proof

@[ftrans]
theorem _root_.MProd.snd.arg_self.revCDeriv_rule 
  [SemiInnerProductSpace K W] [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
  (f : W → MProd X Y) (hf : HasAdjDiff K f)
  : revCDeriv K (fun w => (f w).2)
    =
    fun w => 
      let xydxy := revCDeriv K f w
      (xydxy.1.2, fun dw => xydxy.2 (MProd.mk 0 dw)) := by sorry_proof


end SciLean
open SciLean

def ForInStep.val : ForInStep α → α
| .yield a => a
| .done  a => a


@[simp, ftrans_simp]
theorem ForInStep.val_yield (a : α) : ForInStep.val (.yield a) = a := by rfl

@[simp, ftrans_simp]
theorem ForInStep.val_done (a : α) : ForInStep.val (.done a) = a := by rfl


/-- Turns a pair of values each with yield/done annotation into a pair with
a single yield/done annotation based on the first element. -/
def ForInStep.return2 (x : ForInStep α × ForInStep β) : ForInStep (α × β) :=
  match x.1, x.2 with
  | .yield x₁, .yield x₂ => .yield (x₁, x₂)
  | .yield x₁,  .done x₂ => .yield (x₁, x₂)
  | .done  x₁, .yield x₂ => .done  (x₁, x₂)
  | .done  x₁,  .done x₂ => .done  (x₁, x₂)

def ForInStep.return2Inv (x : ForInStep (α × β)) : ForInStep α × ForInStep β :=
  match x with
  | .yield (x,y) => (.yield x, .yield y)
  | .done (x,y) => (.done x, .done y)


@[simp]
theorem ForInStep.return2_return2Inv_yield {α β} (x : α × β)
  : ForInStep.return2 (ForInStep.return2Inv (.yield x)) = .yield x := by rfl

@[simp]
theorem ForInStep.return2_return2Inv_done {α β} (x : α × β)
  : ForInStep.return2 (ForInStep.return2Inv (.done x)) = .done x := by rfl


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
  simp [forIn,Std.Range.forIn,Std.Range.forIn.loop,Std.Range.forIn.loop.match_1]
  ftrans

--------------------------------------------------------------------------------
-- ForInStep.yield -------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem ForInStep.yield.arg_a0.IsDifferentiable_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : IsDifferentiable K fun x => ForInStep.yield (a0 x) := by sorry_proof

-- this is a hack as with Id monad sometimes you do not need `pure` which trips `fprop` up
@[fprop]
theorem ForInStep.yield.arg_a0.IsDifferentiableM_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : IsDifferentiableM (m:=Id) K fun x => ForInStep.yield (a0 x) := by sorry_proof

@[ftrans]
theorem ForInStep.yield.arg_a0.cderiv_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : cderiv K (fun x => ForInStep.yield (a0 x))
    =
    fun x dx => ForInStep.yield (cderiv K a0 x dx) := by sorry_proof

@[ftrans]
theorem ForInStep.yield.arg_a0.fwdCDeriv_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : fwdCDeriv K (fun x => ForInStep.yield (a0 x))
    =
    fun x dx => ForInStep.return2Inv (ForInStep.yield (fwdCDeriv K a0 x dx))
  := by sorry_proof

@[fprop]
theorem ForInStep.done.arg_a0.IsDifferentiable_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : IsDifferentiable K fun x => ForInStep.done (a0 x) := by sorry_proof


--------------------------------------------------------------------------------
-- ForInStep.done -------------------------------------------------------------
--------------------------------------------------------------------------------

-- this is a hack as with Id monad sometimes you do not need `pure` which trips `fprop` up
@[fprop]
theorem ForInStep.done.arg_a0.IsDifferentiableM_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : IsDifferentiableM (m:=Id) K fun x => ForInStep.done (a0 x) := by sorry_proof

@[ftrans]
theorem ForInStep.done.arg_a0.cderiv_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : cderiv K (fun x => ForInStep.done (a0 x))
    =
    fun x dx => ForInStep.done (cderiv K a0 x dx) := by sorry_proof

@[ftrans]
theorem ForInStep.done.arg_a0.fwdCDeriv_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : fwdCDeriv K (fun x => ForInStep.done (a0 x))
    =
    fun x dx => ForInStep.return2Inv (ForInStep.done (fwdCDeriv K a0 x dx))
  := by sorry_proof


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
  (df' : W → ι → X → X → W → X×W) (w : W) (xs : DataArrayN X ι) (dx' : X) : X×W := Id.run do
  let n := Index.size ι
  let mut dx' := dx'
  let mut dw : W := 0
  for i in [0:n.toNat] do
    let j : ι := fromIdx ⟨n-i.toUSize-1,sorry_proof⟩
    let xj := xs[j]
    let dxw' := df' w j xj dx' dw
    dx' := dxw'.1
    dw := dxw'.2
  (dx',dw)


def ForIn.forIn.arg_bf.revPass_dataArrayImpl' [Index ι] [PlainDataType X] [PlainDataType W] [Zero X] [Zero W]
  (df' : ι → X → X → W → X×W) (xs : DataArray X) (dx' : X) : X×W := Id.run do
  let n := xs.size
  let mut dxw := (dx',0)
  for i in [0:n.toNat] do
    let i' : Idx xs.size := ⟨n-i.toUSize-1,sorry_proof⟩
    let j : ι := fromIdx ⟨n-i.toUSize-1,sorry_proof⟩
    let xj := xs.get i'
    dxw := df' j xj dxw.1 dxw.2
  dxw



/-- Reverse derivative of a for loop

  WARNING: `dx'` and `dw` behave differently
     - `df'` computes gradient in `dx'` 
     - `df'` computes update to gradient in `dw` 
  
  The value of `df'` should be:
    df' = fun w i x dx' dw => 
      ((∇ (x':=x;dx'), f w i x'), (dw + ∇ (w':=w;dx'), f w' i x))
-/
def ForIn.arg_bf.revDeriv_dataArrayImpl [Index ι] [PlainDataType X] [PlainDataType W] [Zero X] [Zero W]
  (init : X) (f : W → ι → X → X) (df' : ι → X → X → W → X×W) (w : W)
  : X×(X→X×W) :=
  Id.run do
    let n := Index.size ι
    -- forward pass
    let mut xs : DataArray X := .mkEmpty n
    let mut x := init
    for i in fullRange ι do
      xs := xs.push x
      x := f w i x
    (x, fun dx' => ForIn.forIn.arg_bf.revPass_dataArrayImpl' df' xs dx')


/-- The do notation leaves the for loop body in a strange form `do pure PUnit.unit; pure <| ForInStep.yield (f w i y))`
  Marking this theorem with `ftrans` is a bit of a hack. It normalizes the body to `ForInStep.yield (f w i y)`.
  -/
@[ftrans]
theorem ForIn.forIn.arg_bf.revDerivM_rule_normalization [Index ι]
  (init : W → X) (f : W → ι → X → X)
  : revDerivM K (fun w => forIn (m:=Id) (fullRange ι) (init w) (fun i y => do pure PUnit.unit; pure <| ForInStep.yield (f w i y)))
    =
    revCDeriv K (fun w => forIn (m:=Id) (fullRange ι) (init w) (fun i y => ForInStep.yield (f w i y))) := by rfl



/-- The do notation leaves the for loop body in a strange form `do pure PUnit.unit; pure <| ForInStep.yield (f w i y))`
  Marking this theorem with `ftrans` is a bit of a hack. It normalizes the body to `ForInStep.yield (f w i y)`.
  -/
@[ftrans]
theorem ForIn.forIn.arg_bf.revCDeriv_rule_normalization [Index ι]
  (init : W → X) (f : W → ι → X → X)
  : revCDeriv K (fun w => forIn (m:=Id) (fullRange ι) (init w) (fun i y => do pure PUnit.unit; pure <| ForInStep.yield (f w i y)))
    =
    revCDeriv K (fun w => forIn (m:=Id) (fullRange ι) (init w) (fun i y => ForInStep.yield (f w i y))) := by rfl


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

      let revPassBody := hold fun i x dx' dw =>
        let dwx' := gradient K (fun (w',x') => (f w' i x').val) (w,x) dx'
        (dwx'.2, dw + dwx'.1)

      (x, 
       fun dx' =>
         -- reverse pass
         let dxw' := ForIn.forIn.arg_bf.revPass_dataArrayImpl' revPassBody xs dx'
         initdinit.2 dxw'.1 + dxw'.2)) :=
by
  sorry_proof


  
--------------------------------------------------------------------------------
-- ForInStep.yield -------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem ForInStep.yield.arg_a0.HasAdjDiff_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : HasAdjDiff K fun x => ForInStep.yield (a0 x) := by sorry_proof

@[fprop]
theorem ForInStep.yield.arg_a0.HasAdjDiffM_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : HasAdjDiffM (m:=Id) K fun x => ForInStep.yield (a0 x) := by sorry_proof

@[ftrans]
theorem ForInStep.yield.arg_a0.revCDeriv_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : revCDeriv K (fun x => ForInStep.yield (a0 x))
    =
    fun x => 
      let ydf := revCDeriv K a0 x
      (.yield ydf.1, fun y => ydf.2 y.val)
  := by sorry_proof

@[ftrans]
theorem ForInStep.yield.arg_a0.revDerivM_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : revDerivM (m:=Id) K (fun x => ForInStep.yield (a0 x))
    =
    fun x => 
      let ydf := revCDeriv K a0 x
      (.yield ydf.1, fun y => ydf.2 y.val)
  := by sorry_proof


--------------------------------------------------------------------------------
-- ForInStep.done --------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem ForInStep.done.arg_a0.HasAdjDiff_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : HasAdjDiff K fun x => ForInStep.done (a0 x) := by sorry_proof

@[fprop]
theorem ForInStep.done.arg_a0.HasAdjDiffM_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : HasAdjDiffM (m:=Id) K fun x => ForInStep.done (a0 x) := by sorry_proof

@[ftrans]
theorem ForInStep.done.arg_a0.revCDeriv_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : revCDeriv K (fun x => ForInStep.done (a0 x))
    =
    fun x => 
      let ydf := revCDeriv K a0 x
      (.done ydf.1, fun y => ydf.2 y.val)
  := by sorry_proof

@[ftrans]
theorem ForInStep.done.arg_a0.revDerivM_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : revDerivM (m:=Id) K (fun x => ForInStep.done (a0 x))
    =
    fun x => 
      let ydf := revCDeriv K a0 x
      (.done ydf.1, fun y => ydf.2 y.val)
  := by sorry_proof


--------------------------------------------------------------------------------
-- ForInStep.val --------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem ForInStep.val.arg_a0.HasAdjDiff_rule
  (a0 : X → ForInStep Y) (ha0 : HasAdjDiff K a0)
  : HasAdjDiff K fun x => ForInStep.val (a0 x) := by sorry_proof

@[fprop]
theorem ForInStep.val.arg_a0.HasAdjDiffM_rule
  (a0 : X → ForInStep Y) (ha0 : HasAdjDiff K a0)
  : HasAdjDiffM (m:=Id) K fun x => ForInStep.val (a0 x) := by sorry_proof

@[ftrans]
theorem ForInStep.val.arg_a0.revCDeriv_rule
  (a0 : X → ForInStep Y) (ha0 : HasAdjDiff K a0)
  : revCDeriv K (fun x => ForInStep.val (a0 x))
    =
    fun x => 
      let ydf := revCDeriv K a0 x
      (ydf.1.val, fun y => ydf.2 (.yield y))
  := by sorry_proof

@[ftrans]
theorem ForInStep.val.arg_a0.revDerivM_rule
  (a0 : X → ForInStep Y) (ha0 : HasAdjDiff K a0)
  : revDerivM (m:=Id) K (fun x => ForInStep.val (a0 x))
    =
    fun x => 
      let ydf := revCDeriv K a0 x
      (ydf.1.val, fun y => ydf.2 (.yield y))
  := by sorry_proof


end OnSemiInnerProductSpace




