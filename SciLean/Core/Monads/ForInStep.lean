import SciLean.Core.FunctionTransformations
import SciLean.Core.Monads.FwdDerivMonad
import SciLean.Core.Monads.Id
import SciLean.Data.DataArray

set_option linter.unusedVariables false

open SciLean
variable 
  {K : Type _} [IsROrC K]
  
-- This is not true but lets assume it for now
instance [Vec K X] : Vec K (ForInStep X) := sorry

-- This is not true but lets assume it for now
instance [SemiInnerProductSpace K X] : SemiInnerProductSpace K (ForInStep X) := sorry


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
  {K : Type _} [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]


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
  {K : Type _} [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]


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
theorem ForInStep.yield.arg_a0.revDerivUpdate_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : revDerivUpdate K (fun x => ForInStep.yield (a0 x))
    =
    fun x => 
      let ydf := revDerivUpdate K a0 x
      (.yield ydf.1, fun dy dx => ydf.2 dy.val dx)
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
theorem ForInStep.done.arg_a0.revDerivUpdate_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : revDerivUpdate K (fun x => ForInStep.done (a0 x))
    =
    fun x => 
      let ydf := revDerivUpdate K a0 x
      (.done ydf.1, fun dy dx => ydf.2 dy.val dx)
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
theorem ForInStep.val.arg_a0.revDerivUpdate_rule
  (a0 : X → ForInStep Y) (ha0 : HasAdjDiff K a0)
  : revDerivUpdate K (fun x => ForInStep.val (a0 x))
    =
    fun x => 
      let ydf := revDerivUpdate K a0 x
      (ydf.1.val, fun dy dx => ydf.2 (.yield dy) dx)
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
