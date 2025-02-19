import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Analysis.SpecialFunctions.StarRingEnd
import SciLean.Lean.ToSSA

namespace SciLean

open VectorType ComplexConjugate

-- max function is differentiable at points that have unique maximum value
def_fun_prop VectorType.max in x [Lawful X]
    (x₀ : X) (hx₀ : ¬(∃ i j, i ≠ j ∧ toVec x₀ i = max x₀ ∧ toVec x₀ j = max x₀)) :
    (DifferentiableAt R · x₀) by sorry_proof

-- TODO: This is not completely true!!! We should have only `DifferentiableAt
def_fun_prop VectorType.max in x [Lawful X] : Differentiable R by sorry_proof


-- reverse AD
abbrev_data_synth VectorType.max in x [Lawful X] [Dense X] [DecidableEq n] : HasRevFDeriv R by
  conv => enter[3]; assign (fun x : X =>
    let i := imaxRe x sorry_proof
    let xmax := toVec x i
    (xmax, fun dxi : R => fromVec (X:=X) (fun j => if j=i then dxi else 0)))
  sorry_proof

abbrev_data_synth VectorType.max in x [Lawful X] [Dense X] [DecidableEq n] : HasRevFDerivUpdate R by
  conv => enter[3]; assign (fun x : X =>
    let i := imaxRe x sorry_proof
    let xmax := toVec x i
    (xmax, fun (dxi : R) (dx : X) =>
      let dxi' := toVec dx i
      VectorType.set dx i (dxi' + dxi)))
  sorry_proof
