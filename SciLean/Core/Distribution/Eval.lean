import SciLean.Core.Distribution.Basic
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Core.Rand.Distributions.UniformI

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {X} [Vec R X] -- [TopologicalSpace X] [space : TCOr (Vec R X) (DiscreteTopology X)]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z]
  {U} [Vec R U]
  {V} [Vec R V] [Module ℝ V]
  {W} [Vec R W]

set_default_scalar R

open Classical

@[distrib_eval]
theorem action_extAction (T : 𝒟' X) (φ : 𝒟 X) :
    T φ = T.extAction' φ := sorry_proof

@[simp,ftrans_simp]
theorem extAction_vecDirac (x : X) (φ : X → Y)  (L : R ⊸ Y ⊸ Z) :
    (dirac x).extAction φ L
    =
    L 1 (φ x) := sorry_proof

@[simp,ftrans_simp]
theorem extAction_restrict_vecDirac (x : X) (A : Set X) (φ : X → Y) (L : R ⊸ Y ⊸ Z) :
    ((dirac x).restrict A).extAction φ L
    =
    if x ∈ A then L 1 (φ x) else 0 := sorry_proof

    -- x.postComp (fun u => (y u).extAction φ) := by sorry_proof

@[action_push]
theorem postExtAction_postComp (x : 𝒟'(X,U)) (y : U ⊸ 𝒟'(Y,Z)) (φ : Y → R) :
    (x.postComp y).postComp (⟨fun T => T.extAction' φ, by unfold Distribution.extAction'; fun_prop⟩)
    =
    x.postComp (⟨fun u => (y u).extAction' φ, by unfold Distribution.extAction'; fun_prop⟩) := by sorry_proof

variable [MeasureSpace X]

open Rand in
@[distrib_eval]
theorem function_toDistribution_eval (f : X → Y) (A : Set X) (φ : X → U) (L : Y ⊸ U ⊸ V) [UniformRand A] :
  (f.toDistribution.restrict A).extAction φ L
  =
  (uniform A).𝔼 fun x =>
    let V : R := Scalar.ofENNReal (volume A)
    V • L (f x) (φ x) := sorry_proof


open Rand in
@[distrib_eval]
theorem function_toDistribution_eval_restrict (f : X → Y) (B A : Set X) (φ : X → U) (L : Y ⊸ U ⊸ V) [UniformRand A] :
  ((f.toDistribution.restrict B).restrict A).extAction φ L
  =
  (uniform A).𝔼 fun x =>
    let V : R := Scalar.ofENNReal (volume A)
    if x.1 ∈ B then
      V • L (f x) (φ x)
    else
      0 := sorry_proof


@[simp, ftrans_simp, action_push]
theorem function_toDistribution_extAction_unit {X} [Vec R X] [Module ℝ X] (f : Unit → X) (φ : Unit → Y) (L : X ⊸ Y ⊸ Z) :
    f.toDistribution.extAction φ L
    =
    L (f ()) (φ ()) := sorry_proof
