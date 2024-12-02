import SciLean.Data.DataArray.Operations.Diag
import SciLean.Data.DataArray.Operations.Matmul
import SciLean.Data.DataArray.Operations.Transpose

namespace SciLean

variable
  {I : Type} [IndexType I] [DecidableEq I]
  {J : Type} [IndexType J] [DecidableEq J]
  {R : Type} [RealScalar R] [PlainDataType R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {U : Type*} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]

namespace DataArrayN

set_option linter.unusedVariables false

@[fun_prop]
theorem inv.arg_A.Differentiable_rule (A : X → R^[I,I])
     (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible) :
     Differentiable R (fun x => (A x).inv) := sorry_proof


@[fun_prop]
theorem _root_.Inv.inv.arg_a0.Differentiable_rule_matrix (A : X → R^[I,I])
     (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible) :
     Differentiable R (fun x => (A x)⁻¹) := inv.arg_A.Differentiable_rule A hA hA'


@[fun_trans]
theorem inv.arg_A.fderiv_rule (A : X → R^[I,I])
     (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible) :
     fderiv R (fun x => (A x).inv)
     =
     fun x => fun dx =>L[R]
       let dA := fderiv R A x dx
       let A := A x
       (- A.inv * dA * A.inv) := sorry


@[fun_trans]
theorem _root_.Inv.inv.arg_a0.fderiv_rule_matrix (A : X → R^[I,I])
     (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible) :
     fderiv R (fun x => (A x)⁻¹)
     =
     fun x => fun dx =>L[R]
       let dA := fderiv R A x dx
       let A := A x
       (- A⁻¹ * dA * A⁻¹) := inv.arg_A.fderiv_rule A hA hA'


@[fun_trans]
theorem inv.arg_A.fwdFDeriv_rule (A : X → R^[I,I])
     (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible) :
     fwdFDeriv R (fun x => (A x).inv)
     =
     fun x dx =>
       let AdA := fwdFDeriv R A x dx
       let A := AdA.1; let dA := AdA.2
       let A' := A.inv
       (A', - A' * dA * A') := sorry


@[fun_trans]
theorem _root_.Inv.inv.arg_a0.fwdFDeriv_rule_matrix (A : X → R^[I,I])
     (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible) :
     fwdFDeriv R (fun x => (A x)⁻¹)
     =
     fun x dx =>
       let AdA := fwdFDeriv R A x dx
       let A := AdA.1; let dA := AdA.2
       let A' := A⁻¹
       (A', - A' * dA * A') := inv.arg_A.fwdFDeriv_rule A hA hA'


@[fun_trans]
theorem inv.arg_A.revFDeriv_rule (A : U → R^[I,I])
     (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible) :
     revFDeriv R (fun x => (A x).inv)
     =
     fun x =>
       let AdA := revFDeriv R A x
       let A := AdA.1; let dA := AdA.2
       let A' := A.inv
       (A',
        fun B =>
          let C := - A'ᵀ * (B * A'ᵀ)
          dA C) := by
  unfold revFDeriv
  funext x
  fun_trans (disch:=assumption)
  funext B
  apply congr_arg
  simp[neg_pull]


@[fun_trans]
theorem _root_.Inv.inv.arg_a0.revFDeriv_rule_matrix (A : U → R^[I,I])
     (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible) :
     revFDeriv R (fun x => (A x)⁻¹)
     =
     fun x =>
       let AdA := revFDeriv R A x
       let A := AdA.1; let dA := AdA.2
       let A' := A⁻¹
       (A',
        fun B =>
          let C := - A'ᵀ * (B * A'ᵀ)
          dA C) := by
  unfold revFDeriv
  funext x
  fun_trans (disch:=assumption)
  funext B
  apply congr_arg
  simp[neg_pull]
