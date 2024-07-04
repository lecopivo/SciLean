import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Dirac
-- import Mathlib.Data.RCLike.Basic
-- import Mathlib.Analysis.LocallyConvex.Basic
-- import Mathlib.Topology.Algebra.Module.LocallyConvex

import SciLean.Mathlib.MeasureTheory.Unit

import SciLean.Core.FunctionTransformations
import SciLean.Core.Integral.BoundingBall
import SciLean.Util.SorryProof


open MeasureTheory

namespace SciLean

/-- Convenient integral - the integral I need :)
It should be Bochner integral but it should integrate function valued function point wise i.e.
```
∫ x, fun y => f x y = fun y => ∫ x, f x y
```
where rhs can be understoods as Bochenr integral and lhs defined thie `cintegral`. -/
noncomputable
opaque cintegral {α} [MeasurableSpace α] {X} [AddCommGroup X] [Module ℝ X]
  -- dragging along all of these typeclasses is really really annoying
  -- [AddCommGroup X] [TopologicalSpace X] [TopologicalAddGroup X] [Module ℝ X] [LocallyConvexSpace ℝ X]
    (f : α → X) (μ : Measure α) : X := 0

opaque CIntegrable {α} [MeasurableSpace α] {X} [AddCommGroup X] [Module ℝ X]
    (f : α → X) (μ : Measure α) : Prop

open Lean Parser  Term
syntax "∫' " funBinder (" in " term)? ", " term:60 (" ∂" term:70)? : term

macro_rules
| `(∫' $x:funBinder, $b) => `(cintegral (fun $x => $b) (by volume_tac))
| `(∫' $x:funBinder, $b ∂$μ) => `(cintegral (fun $x => $b) $μ)
| `(∫' $x:funBinder in $set, $b) => `(cintegral (fun $x => $b) (Measure.restrict (by volume_tac) $set))
| `(∫' $x:funBinder in $set, $b ∂$μ) => `(cintegral (fun $x => $b) (Measure.restrict $μ $set))


@[app_unexpander cintegral] def unexpandCIntegral : Lean.PrettyPrinter.Unexpander

  | `($(_) $f:term volume) =>
    match f with
    | `(fun $x => $b) => `(∫' $x, $b)
    | `(fun $x $xs* => $b) => `(∫' $x, fun $xs* => $b)
    | _ => throw ()

  | `($(_) $f:term $μ) =>
    match f, μ with
    -- |      `(fun $x => $b), `(Measure.restrict volume $A) => `(∫' $x in $A, $b)
    -- | `(fun $x $xs* => $b), `(Measure.restrict volume $A) => `(∫' $x in $A, (fun $xs* => $b))
    |      `(fun $x => $b), `(Measure.restrict $μ $A) => `(∫' $x in $A, $b ∂$μ)
    | `(fun $x $xs* => $b), `(Measure.restrict $μ $A) => `(∫' $x in $A, (fun $xs* => $b) ∂$μ)
    -- |      `(fun $x => $b), `(volume) => `(∫' $x, $b)
    -- | `(fun $x $xs* => $b), `(volume) => `(∫' $x, (fun $xs* => $b))
    |      `(fun $x => $b), _ => `(∫' $x, $b ∂$μ)
    | `(fun $x $xs* => $b), _ => `(∫' $x, (fun $xs* => $b) ∂$μ)
    | _, _ => throw ()


  | _ => throw ()

----------------------------------------------------------------------------------------------------
-- Algebra -----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
section Algebra

variable
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]
  {X} [AddCommGroup X] [Module ℝ X]
  {Y} [AddCommGroup Y] [Module ℝ Y]

@[simp, ftrans_simp]
theorem cintegral_zero (μ : Measure α): ∫' _, (0 : X) ∂μ = 0 := sorry_proof

@[add_pull] -- @[integral_push]
theorem cintegral_add {f g : α → X} {μ : Measure α}
    (hf : CIntegrable f μ) (hg : CIntegrable g μ) :
    ∫' x, f x + g x ∂μ = ∫' x, f x ∂μ + ∫' x, g x ∂μ := sorry_proof

@[add_push] -- @[integral_push]
theorem cintegral_add' {f g : α → X} {μ : Measure α}
    (hf : CIntegrable f μ) (hg : CIntegrable g μ) :
    ∫' x, f x ∂μ + ∫' x, g x ∂μ = ∫' x, f x + g x ∂μ  := sorry_proof

@[smul_pull]-- @[integral_push]
theorem cintegral_smul {R} [Semiring R] [Module R X] {f : α → X} (r : R) :
    ∫' x, r • f x ∂μ = r • ∫' x, f x ∂μ := sorry_proof

@[smul_push] -- @[integral_pull]
theorem cintegral_smul' {R} [Semiring R] [Module R X] {f : α → X} (r : R) :
    r • ∫' x, f x ∂μ = ∫' x, r • f x ∂μ := sorry_proof

@[add_pull] -- @[integral_push]
theorem cintegral_add_measures {f : α → X} {μ ν : Measure α}
    (hμ : CIntegrable f μ) (hν : CIntegrable f ν) :
    ∫' x, f x ∂(μ+ν) = ∫' x, f x ∂μ + ∫' x, f x ∂ν := sorry_proof

@[simp, ftrans_simp]
theorem cintegral_dirac {f : α → X} (p : α) :
    ∫' x, f x ∂(Measure.dirac p) = f p := sorry_proof

@[simp,ftrans_simp]
theorem cintegral_unit {f : Unit → X} :
    ∫' x, f x  = f () := sorry_proof

-- @[integral_push]
theorem cintegral_prod_mk {f : α → X} {g : α → Y} {μ : Measure α} :
    ∫' x, (f x, g x) ∂μ = (∫' x, f x ∂μ, ∫' x, g x ∂μ) := sorry_proof

-- @[integral_pull]
theorem cintegral_prod_mk' {f : α → X} {g : α → Y} {μ : Measure α} :
    (∫' x, f x ∂μ, ∫' x, g x ∂μ) = ∫' x, (f x, g x) ∂μ := sorry_proof

theorem cintegral_lambda {α} (f : α → β → X) (μ : Measure β) :
    (fun x => ∫' y, f x y ∂μ)
    =
    ∫' y, (fun x => f x y) ∂μ := sorry_proof

theorem cintegral.arg_f.push_lambda {α} (f : α → β → X) (μ : Measure β) :
    (fun x => ∫' y, f x y ∂μ)
    =
    ∫' y, (fun x => f x y) ∂μ := sorry_proof


@[simp, ftrans_simp]
theorem cintegral_measure_map (g : β → X) (f : α → β) (μ : Measure α) :
    (∫' y, g y ∂(μ.map f))
    =
    ∫' x, g (f x) ∂μ := sorry_proof


end Algebra


----------------------------------------------------------------------------------------------------
-- Integral simproc --------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


section Simplifier

variable {α} [MeasurableSpace α] {X} [AddCommGroup X] [Module ℝ X]

theorem integral_in_set_simp
    (f g : α → X) (A : Set α) (h : ∀ x, x ∈ A → f x = g x) (μ : Measure α) :
    ∫' x in A, f x ∂μ
    =
    ∫' x in A, g x ∂μ := sorry_proof

open Lean Meta in
simproc_decl integral_simproc (cintegral _ (Measure.restrict _ _)) := fun e => do
  let .app e  μ' := e  | return .continue
  let .app _  f  := e  | return .continue
  let .app μ' A  := μ' | return .continue
  let .app _  μ  := μ' | return .continue

  let .forallE xName xType _ _ ← inferType f | return .continue

  withLocalDeclD xName xType fun x => do
  withLocalDeclD `h (← mkAppM ``Membership.mem #[x,A]) fun h => do
    let fx := f.beta #[x]
    let r ← Simp.simp fx

    let h' ← mkLambdaFVars #[x,h] (← r.getProof)
    let g ← mkLambdaFVars #[x] r.expr

    let prf ← mkAppM ``integral_in_set_simp #[f,g,A,h',μ]
    let rhs := (← inferType prf).appArg!

    return .visit { expr := rhs, proof? := .some prf }


end Simplifier


----------------------------------------------------------------------------------------------------
-- Domain simps  -----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section DomainSimps

variable
  {R} [RealScalar R] [@DecidableRel R (· ≤ ·)]
  {X} [MeasureSpace X]
  {Y} [AddCommGroup Y] [Module ℝ Y]
  {Z} [AddCommGroup Z] [Module ℝ Z]

-- we prefer specifying sets with `0 ≤ ...`
-- TODO: Add seme regularity conditions on φ and ψ
-- @[simp,ftrans_simp]
theorem split_integral_of_ite (φ ψ : X → R) (f g : X → Y) :
    (∫' x, if ψ x ≤ φ x then f x else g x)
    =
    (∫' x in {x' | ψ x' ≤ φ x'}, f x)
    +
    (∫' x in {x' | φ x' < ψ x'}, g x) := sorry_proof


-- @[simp,ftrans_simp]
-- theorem split_integral_of_ite' (φ ψ : X → R) (f g : X → Y) (h : X → Y → Z):
--     (∫' x, h x (if ψ x ≤ φ x then f x else g x))
--     =
--     (∫' x in {x' | 0 ≤ φ x' - ψ x'}, h x (f x))
--     +
--     (∫' x in {x' | 0 ≤ ψ x' - φ x'}, h x (g x)) := sorry_proof

-- @[simp,ftrans_simp]
theorem split_integral_over_set_of_ite (φ ψ : X → R) (f g : X → Y) (A : Set X) :
    (∫' x in A, if ψ x ≤ φ x then f x else g x)
    =
    (∫' x in {x' | 0 ≤ φ x' - ψ x'} ∩ A, f x)
    +
    (∫' x in {x' | 0 ≤ ψ x' - φ x'} ∩ A, g x) := by sorry_proof

-- attribute [ftrans_simp] MeasureTheory.integral_zero sub_nonneg

end DomainSimps


----------------------------------------------------------------------------------------------------
-- Differentiation ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
section Differentiation

variable
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]
  {R} [RCLike R]
  {X} [Vec R X] [Module ℝ X]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z] [Module ℝ Z]

@[fun_prop]
theorem cintegral.arg_f.CDifferentiable_rule
    (f : X → β → Z) (μ : Measure β) (hf : ∀ x, CDifferentiable R (f · x)) :
    CDifferentiable R (fun x => ∫' y, f x y ∂μ) := by have := hf; sorry_proof

@[fun_trans]
theorem cintegral.arg_f.cderiv_rule
    (f : X → β → Z) (μ : Measure β) (hf : ∀ y, CDifferentiable R (f · y)) :
    (cderiv R  fun x => ∫' y, f x y ∂μ)
    =
    fun x dx => ∫' y, cderiv R (f · y) x dx ∂μ := by have := hf; sorry_proof

@[fun_trans]
theorem cintegral.arg_f.fwdDeriv_rule
    (f : X → β → Z) (μ : Measure β) (hf : ∀ x, CDifferentiable R (f · x)) :
    (fwdDeriv R fun x => ∫' y, f x y ∂μ)
    =
    fun x dx => ∫' y, fwdDeriv R (f · y) x dx ∂μ := by
  unfold fwdDeriv; fun_trans [cintegral_prod_mk]

@[fun_prop]
theorem cintegral.arg_f.IsLinearMap_rule
    (f : X → β → Z) (μ : Measure β) (hf : ∀ y, IsLinearMap R (f · y)) :
    IsLinearMap R (fun x => ∫' y, f x y ∂μ) := by have := hf; sorry_proof

@[fun_prop]
theorem cintegral.arg_f.IsSmoothLinearMap_rule
    (f : X → β → Z) (μ : Measure β) (hf : ∀ y, IsSmoothLinearMap R (f · y)) :
    IsSmoothLinearMap R (fun x => ∫' y, f x y ∂μ) := by constructor <;> fun_prop


end Differentiation


-- ----------------------------------------------------------------------------------------------------
-- -- Upper bounds on integration domains  ------------------------------------------------------------
-- ----------------------------------------------------------------------------------------------------
-- open Classical in
-- theorem cintegral_bound_domain_ball
--     {X} [MeasureSpace X] [MetricSpaceP X 2]
--     {U} [AddCommGroup U] [Module ℝ U]
--     (A : Set X) (f : X → U)
--     (center : X) (radius : ℝ) (hball : BoundingBall A center radius) :
--     ∫' y in A, f y
--     =
--     ∫' x in Metric.closedBallP 2 center radius, (if x ∈ A then f x else 0) := sorry_proof
