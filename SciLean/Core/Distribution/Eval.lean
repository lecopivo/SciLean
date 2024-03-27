import SciLean.Core.Distribution.Basic
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Core.Rand.Distributions.UniformI

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {X} [TopologicalSpace X] [space : TCOr (Vec R X) (DiscreteTopology X)]

set_default_scalar R

open Classical

@[action_push]
theorem action_extAction (T : 𝒟' X) (φ : 𝒟 X) :
    T.action φ = T.extAction φ := sorry_proof

@[action_push]
theorem dirac_eval (x : X) (φ : X → R) :
    (dirac x).extAction φ
    =
    φ x := sorry_proof

@[action_push]
theorem dirac_restric_eval (x : X) (A : Set X) (φ : X → R) :
    ((dirac x).restrict A).extAction φ
    =
    if x ∈ A then φ x else 0 := sorry_proof

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
