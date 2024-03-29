import SciLean.Core.Distribution.Basic
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Core.Rand.Distributions.UniformI

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {X} [TopologicalSpace X] [space : TCOr (Vec R X) (DiscreteTopology X)]
  {Y} [Vec R Y]
  {Z} [Vec R Z]

set_default_scalar R

open Classical

@[action_push]
theorem action_extAction (T : 𝒟' X) (φ : 𝒟 X) :
    T.action φ = T.extAction φ := sorry_proof

@[action_push]
theorem extAction_vecDirac (x : X) (y : Y) (φ : X → R) :
    (vecDirac x y).extAction φ
    =
    φ x • y := sorry_proof

@[action_push]
theorem extAction_restrict_vecDirac (x : X) (y : Y) (A : Set X) (φ : X → R) :
    ((vecDirac x y).restrict A).extAction φ
    =
    if x ∈ A then φ x • y else 0 := sorry_proof

@[action_push]
theorem postExtAction_vecDirac (x : X) (y : 𝒟'(Y,Z)) (φ : Y → R) :
    (vecDirac x y).postExtAction φ
    =
    vecDirac x (y.extAction φ) := sorry_proof

variable [MeasureSpace X]

open Rand in
@[action_push]
theorem function_toDistribution_eval (f : X → R) (A : Set X) (φ : X → R) [UniformRand A] :
  (f.toDistribution.restrict A).extAction φ
  =
  (uniform A).E fun x =>
    let V : R := Scalar.ofENNReal (volume A)
    V • f x * φ x := sorry_proof


open Rand in
@[action_push]
theorem function_toDistribution_eval_restrict (f : X → R) (B A : Set X) (φ : X → R) [UniformRand A] :
  ((f.toDistribution.restrict B).restrict A).extAction φ
  =
  (uniform A).E fun x =>
    let V : R := Scalar.ofENNReal (volume A)
    if x.1 ∈ B then
      V • f x * φ x
    else
      0 := sorry_proof
