import SciLean.Probability.Rand

namespace SciLean

set_option deprecated.oldSectionVars true
variable {X} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X] [TopologicalSpace X]
variable {Y} [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] [TopologicalSpace Y]
variable {Z} [AddCommGroup Z] [Module ℝ Z] [MeasurableSpace Z] [TopologicalSpace Z]

open MeasureTheory
@[fun_prop]
def IsAffineRandMap (f : X → Rand Y) : Prop :=
  -- maybe this should be stated in terms of weak integral
  -- also maybe we should require that: `∀ x, LawfulRand (f x)`
  ∀ (φ : Y → ℝ), (∀ x, Integrable φ (f x).ℙ) → IsAffineMap ℝ (fun x => ∫ x, φ x ∂(f x).ℙ)

@[fun_prop]
theorem IsAffineRandMap.const_rule (y : Rand Y) :
    IsAffineRandMap (fun _ : X => y) := by sorry_proof

set_option linter.unusedVariables false
@[fun_prop]
theorem _root_.Pure.pure.arg_a0.IsAffineRandMap (f : X → Y) (hf : IsAffineMap ℝ f) :
    IsAffineRandMap (fun x => pure (f x)) := by sorry_proof

@[fun_prop]
theorem _root_.Bind.bind.arg_a0at.IsAffineRandMap
    (a0 : X → Rand Y) (a1 : X → Y → Rand Z)
    (ha0 : IsAffineRandMap a0) (ha1 : IsAffineRandMap (fun (x,y) => a1 x y)) :
    IsAffineRandMap (fun x => Bind.bind (a0 x) (fun y => a1 x y)) := by sorry_proof
