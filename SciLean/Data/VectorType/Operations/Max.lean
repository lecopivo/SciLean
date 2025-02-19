import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Analysis.SpecialFunctions.StarRingEnd
import SciLean.Lean.ToSSA

namespace SciLean

open VectorType ComplexConjugate

set_option linter.unusedVariables false

-- -- max function is differentiable at points that have unique maximum value
def_fun_prop VectorType.max in x [InjectiveGetElem X n]
    (x₀ : X) (hx₀ : ¬(∃ (i j : n), i ≠ j ∧ x₀[i]'True.intro = max x₀ ∧ x₀[j]'True.intro = max x₀)) :
    (DifferentiableAt R · x₀) by sorry_proof

-- TODO: This is not completely true!!! We should have only `DifferentiableAt
def_fun_prop VectorType.max in x [InjectiveGetElem X n] : Differentiable R by sorry_proof


-- reverse AD
abbrev_data_synth VectorType.max in x [InjectiveGetElem X n] [Dense X] [DecidableEq n] : HasRevFDeriv R by
  conv => enter[3]; assign (fun x : X =>
    let i := imaxRe x sorry_proof
    let xmax := x[i]
    (xmax, fun dxi : R => fromVec (X:=X) (fun j => if j=i then dxi else 0)))
  sorry_proof

abbrev_data_synth VectorType.max in x [InjectiveGetElem X n] [Dense X] [DecidableEq n] : HasRevFDerivUpdate R by
  conv => enter[3]; assign (fun x : X =>
    let i := imaxRe x sorry_proof
    let xmax := x[i]
    (xmax, fun (dxi : R) (dx : X) =>
      let dxi' := dx[i]
      setElem dx i (dxi' + dxi) (by dsimp)))
  sorry_proof
