import SciLean.Core.Transformations.HasParamDerivWithJumps.HasParamFDerivWithJumps
import SciLean.Core.Transformations.HasParamDerivWithJumps.HasParamFwdFDerivWithJumps
import SciLean.Core.Transformations.HasParamDerivWithJumps.HasParamRevFDerivWithJumps
import SciLean.Core.Transformations.BoundingBall
import SciLean.Core.Transformations.RnDeriv
import SciLean.Tactic.LFunTrans

open MeasureTheory

namespace SciLean

----------------------------------------------------------------------------------------------------
-- Missing simp attributes -------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

attribute [ftrans_simp]
  RCLike.inner_apply
  Set.empty_inter Set.inter_empty Set.empty_union Set.union_empty
  Sum.elim_lam_const_lam_const Sum.elim_inl Sum.elim_inr sub_self
  Prod.smul_mk
  Pi.conj_apply
  ite_apply

attribute [ftrans_simp ↓, ftrans_simp]
  List.cons_append
  List.nil_append
  List.singleton_append
  List.append_assoc
  List.map_cons
  List.map_nil
  List.foldl_nil
  -- List.foldl_cons -- we have custom version with let binding

attribute [ftrans_simp]
  integral_zero
  integral_singleton

attribute [ftrans_simp]
  Measure.hausdorffMeasure_zero_singleton

attribute [ftrans_simp]
  -- not sure about these as they require nontrivial hypothesis
  frontier_Icc frontier_Ico frontier_Ioc frontier_Ioo


----------------------------------------------------------------------------------------------------
-- Misc ------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[ftrans_simp]
theorem finrank_real_scalar [RealScalar R] : FiniteDimensional.finrank ℝ R = 1 := sorry_proof

instance instMemPreimageDecidable (x : α) (B : Set β) (f : α → β)
    [inst : ∀ (y:β), Decidable (y ∈ B)] :
    Decidable (x ∈ f ⁻¹' B) := inst (f x)

notation "π" => RealScalar.pi (R:=defaultScalar%)


----------------------------------------------------------------------------------------------------
-- Frontier ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[ftrans_simp]
theorem frontier_setOf_le {X} [TopologicalSpace X] {R} [RealScalar R] (f g : X → R)
  (hf : Continuous f) (hg : Continuous g) :
  frontier {x | f x ≤ g x}
  =
  {x | f x = g x} := sorry_proof


section
variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]

set_default_scalar R

-- TODO: this equality holds only for `w` and `x` such that `φ w x = ψ w x`. Away from the level set
--       frontierSpeed is not well defined
@[simp,ftrans_simp]
theorem frontierSpeed_setOf_le (φ ψ : W → X → R) :
    frontierSpeed' R  (fun w => {x | φ w x ≤ ψ w x})
    =
    fun w dw x =>
      let ζ := (fun w x => φ w x - ψ w x)
      (-(fderiv R (ζ · x) w dw)/‖fgradient (ζ w ·) x‖₂) := by
  sorry_proof

@[simp,ftrans_simp]
theorem frontierSpeed_setOf_lt (φ ψ : W → X → R) :
    frontierSpeed' R  (fun w => {x | φ w x < ψ w x})
    =
    fun w dw x =>
      let ζ := (fun w x => φ w x - ψ w x)
      (-(fderiv R (ζ · x) w dw)/‖fgradient (ζ w ·) x‖₂) := by
  sorry_proof


end

----------------------------------------------------------------------------------------------------
-- Integral ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section IntegralSimps

variable
  {α} [EMetricSpace α] [MeasurableSpace α] [BorelSpace α]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

@[ftrans_simp]
theorem integral_zero_hausdof_of_singleton_inter_set (f : α → Y) (a : α) (A : Set α) [Decidable (a ∈ A)] :
  ∫ x in {a} ∩ A, f x ∂μH[0] = if a ∈ A then f a else 0 := sorry_proof


@[ftrans_simp]
theorem integral_zero_hausdof_of_setOf_bijective_inter_set [Nonempty α]
    (f : α → Y) (φ : α → β) (hφ : φ.Bijective) (b : β) (A : Set α) [∀ x, Decidable (x ∈ A)] :
    ∫ x in {x' | φ x' = b} ∩ A, f x ∂μH[0]
    =
    let x' := φ.invFun b
    if x' ∈ A then f x' else 0 := sorry_proof

@[ftrans_simp]
theorem integral_zero_hausdof_of_setOf_bijective_inter_set' [Nonempty α]
    (f : α → Y) (φ : α → β) (hφ : φ.Bijective) (b : β) (A : Set α) [∀ x, Decidable (x ∈ A)] :
    ∫ x in (no_index {x' | b = φ x'}) ∩ A, f x ∂μH[0]
    =
    let x' := φ.invFun b
    if x' ∈ A then f x' else 0 := sorry_proof


end IntegralSimps



----------------------------------------------------------------------------------------------------
-- List --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- @[ftrans_simp ↓]
-- theorem foldl_cons' (l : List α) (b : β) :
--   (a :: l).foldl f b
--   =
--   let x := f b a
--   l.foldl f x := by simp only [List.foldl_cons]


@[ftrans_simp ↓ mid+1]
theorem List.foldl_sum (a : α) (f : α → β) (l : List α) (b : β) [Add β] :
  (a :: l).foldl (fun s x => s + f x) b
  =
  let s := f a
  l.foldl (fun s x => s + f x) (b + s) := rfl



----------------------------------------------------------------------------------------------------
-- if simps ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[ftrans_simp ↓]
theorem fst_ite {c : Prop} [Decidable c] (t e : α×β) :
    (if c then t else e).1 = if c then t.1 else e.1 := by split_ifs <;> rfl

@[ftrans_simp ↓]
theorem snd_ite {c : Prop} [Decidable c] (t e : α×β) :
    (if c then t else e).2 = if c then t.2 else e.2 := by split_ifs <;> rfl


@[ftrans_simp ↓]
theorem ite_add2 {α} [Add α] (P : Prop) [Decidable P] (a b c d : α) :
    (if P then a else b) + (if P then c else d)
    =
    if P then a + c else b + d := by split_ifs <;> rfl

@[ftrans_simp ↓]
theorem ite_sub2 {α} [Sub α] (P : Prop) [Decidable P] (a b c d : α) :
    (if P then a else b) - (if P then c else d)
    =
    if P then a - c else b - d := by split_ifs <;> rfl



----------------------------------------------------------------------------------------------------
-- Tactics -----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Run `fun_prop` but only on goals that do not contain `if _ then _ else _`. -/
syntax (name := funPropNoIfsTacStx) "fun_prop_no_ifs" : tactic


open Lean Meta Elab Tactic
/-- Tactic to prove function properties -/
@[tactic funPropNoIfsTacStx]
def funPropTac : Tactic
  | `(tactic| fun_prop_no_ifs) => do

    let goal ← getMainGoal
    goal.withContext do
      let goalType ← goal.getType >>= instantiateMVars
      if goalType.containsConst (fun n => n == ``ite || n == ``dite) then
        pure ()
      else
        evalTactic (← `(tactic| fun_prop))

  | _ =>
    throwUnsupportedSyntax


open FiniteDimensional

axiom assume_almost_disjoint {X} [MeasurableSpace X]
  (A B : Set X) (μ : Measure X) : AlmostDisjoint A B μ

axiom assume_almost_disjoint_list {X} [MeasurableSpace X]
  (As : List (Set X)) (μ : Measure X) : AlmostDisjointList As μ

/--  -/
syntax (name:=assumeAlmostDiscjointStx) "assume_almost_disjoint" : tactic


@[tactic assumeAlmostDiscjointStx]
def assumeAlmostDiscjointTac : Tactic
  | `(tactic| assume_almost_disjoint) => do

    let goal ← getMainGoal

    goal.withContext do
      let goalType ← goal.getType >>= instantiateMVars
      if goalType.isAppOf ``AlmostDisjoint ||
         goalType.isAppOf ``AlmostDisjointList then

        evalTactic (← `(tactic| simp (config:={failIfUnchanged:=false}) (disch:=fun_prop) only [ftrans_simp,DiscontinuityDataList.getDiscontinuity,DiscontinuityDataList.getDiscontinuities,List.foldl_cons]))
        let goalType ← getMainGoal >>= (·.getType)
        logInfo m!"assuming {goalType}"
        evalTactic (← `(tactic| first | apply assume_almost_disjoint | apply assume_almost_disjoint_list))

  | _ =>
    throwUnsupportedSyntax
