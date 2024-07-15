import SciLean.Core.Transformations.HasParamDerivWithJumps.HasParamFDerivWithJumps
import SciLean.Core.Transformations.HasParamDerivWithJumps.HasParamFwdFDerivWithJumps
import SciLean.Core.Transformations.HasParamDerivWithJumps.HasParamRevFDerivWithJumps
import SciLean.Core.Transformations.BoundingBall
import SciLean.Core.Transformations.RnDeriv
import SciLean.Tactic.LFunTrans

import SciLean.Core.FloatAsReal

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
  Set.setOf_mem_eq



attribute [ftrans_simp] zero_le_one



----------------------------------------------------------------------------------------------------
-- Misc ------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[ftrans_simp]
theorem finrank_real_scalar [RealScalar R] : FiniteDimensional.finrank ℝ R = 1 := sorry_proof

instance instMemPreimageDecidable (x : α) (B : Set β) (f : α → β)
    [inst : ∀ (y:β), Decidable (y ∈ B)] :
    Decidable (x ∈ f ⁻¹' B) := inst (f x)

def _root_.Set.decidableMemProdComputable {α β : Type*} {s : Set α} {t : Set β}
 [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s ×ˢ t) := fun _ => And.decidable

@[ftrans_simp]
theorem decidableMemProd_mk_computable {α β : Type*} {s : Set α} {t : Set β} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
  (Set.decidableMemProd : DecidablePred (· ∈ s ×ˢ t)) = Set.decidableMemProdComputable := by rfl

-- clean up all classical decisions to decidable ones if possible
open Classical in
@[ftrans_simp]
theorem prop_classical_dec_eq_decidable {P : Prop} [inst : Decidable P] :
   Classical.propDecidable P = inst := by
  induction inst <;> induction (propDecidable P) <;> aesop


notation "π" => RealScalar.pi (R:=defaultScalar%)


----------------------------------------------------------------------------------------------------
-- Frontier ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

set_option linter.unusedVariables false in
@[ftrans_simp]
theorem frontier_setOf_le {X} [TopologicalSpace X] {R} [RealScalar R] (f g : X → R)
  (hf : Continuous f) (hg : Continuous g) :
  frontier {x | f x ≤ g x}
  =
  {x | f x = g x} := sorry_proof

set_option linter.unusedVariables false in
open Set in
@[ftrans_simp]
theorem frontier_Icc' {R} [RealScalar R] (a b : R) (h : a < b) :
  frontier (Icc a b) = ({a,b} : Finset R) := sorry_proof

set_option linter.unusedVariables false in
open Set in
@[ftrans_simp]
theorem frontier_Ico' {R} [RealScalar R] (a b : R) (h : a < b) :
  frontier (Ico a b) = ({a,b} : Finset R) := sorry_proof

set_option linter.unusedVariables false in
open Set in
@[ftrans_simp]
theorem frontier_Ioc' {R} [RealScalar R] (a b : R) (h : a < b) :
  frontier (Ioc a b) = ({a,b} : Finset R) := sorry_proof

set_option linter.unusedVariables false in
open Set in
@[ftrans_simp]
theorem frontier_Ioo' {R} [RealScalar R] (a b : R) (h : a < b) :
  frontier (Ioo a b) = ({a,b} : Finset R) := sorry_proof


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


set_option linter.unusedVariables false in
@[ftrans_simp]
theorem integral_zero_hausdof_of_setOf_bijective_inter_set [Nonempty α]
    (f : α → Y) (φ : α → β) (hφ : φ.Bijective) (b : β) (A : Set α) [∀ x, Decidable (x ∈ A)] :
    ∫ x in {x' | φ x' = b} ∩ A, f x ∂μH[0]
    =
    let x' := φ.invFun b
    if x' ∈ A then f x' else 0 := sorry_proof

set_option linter.unusedVariables false in
@[ftrans_simp]
theorem integral_zero_hausdof_of_setOf_bijective_inter_set' [Nonempty α]
    (f : α → Y) (φ : α → β) (hφ : φ.Bijective) (b : β) (A : Set α) [∀ x, Decidable (x ∈ A)] :
    ∫ x in (no_index {x' | b = φ x'}) ∩ A, f x ∂μH[0]
    =
    let x' := φ.invFun b
    if x' ∈ A then f x' else 0 := sorry_proof


set_option linter.unusedVariables false in
@[ftrans_simp]
theorem integral_zero_hausdof_of_finset
    (f : α → Y) (A : Set α) (B : Finset α) [∀ x, Decidable (x ∈ A)] :
    ∫ x in B ∩ A, f x ∂μH[0]
    =
    B.sum fun x =>  if x ∈ A then f x else 0 := sorry_proof


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
-- volume ------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section volume

variable {R} [RealScalar R]

set_default_scalar R

open Set SciLean MeasureTheory
@[ftrans_simp]
theorem volume_Icc {R} [RealScalar R] [MeasureSpace R] (a b : R) :
  volume (Icc a b) = Scalar.toENNReal (R:=R) (if a ≤ b then b - a else 0) := sorry_proof

@[ftrans_simp]
theorem volume_Ioo {R} [RealScalar R] [MeasureSpace R] (a b : R) :
  volume (Ioo a b) = Scalar.toENNReal (R:=R) (if a ≤ b then b - a else 0) := sorry_proof

@[ftrans_simp]
theorem volume_Ico {R} [RealScalar R] [MeasureSpace R] (a b : R) :
  volume (Ico a b) = Scalar.toENNReal (R:=R) (if a ≤ b then b - a else 0) := sorry_proof

@[ftrans_simp]
theorem volume_Ioc {R} [RealScalar R] [MeasureSpace R] (a b : R) :
  volume (Ioc a b) = Scalar.toENNReal (R:=R) (if a ≤ b then b - a else 0) := sorry_proof

@[ftrans_simp ↓]
theorem volume_prod {X Y} [MeasureSpace X] [MeasureSpace Y] (A : Set X) (B : Set Y) :
  volume (A ×ˢ B) = volume A * volume B := sorry_proof

def ballVolume (dim : Nat) (r : R) :=
  if r ≤ 0 then
    0
  else
    go dim
where
  go (dim : Nat) :=
  match dim with
  | 0 => 1
  | 1 => 2 * r
  | (n + 2) => 2*π/(n+2) * r^2 * ballVolume n r

open FiniteDimensional
@[ftrans_simp]
theorem volume_closedBall₂ {R} [RealScalar R] {X} [NormedAddCommGroup X] [AdjointSpace R X] [MeasureSpace X]
  (x : X) (r : R) :
  volume (closedBall₂ x r)
  =
  Scalar.toENNReal (R:=R) (ballVolume (finrank R X) r) := sorry_proof


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
