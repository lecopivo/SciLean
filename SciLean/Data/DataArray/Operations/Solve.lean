import SciLean.Data.DataArray.Operations.Inv
import SciLean.Data.DataArray.Operations.Vecmul

namespace SciLean

variable
  {I : Type*} [IndexType I] [DecidableEq I]
  {J : Type*} [IndexType J] [DecidableEq J]
  {R : Type*} [RealScalar R] [PlainDataType R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {U : Type*} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]

namespace DataArrayN

set_option linter.unusedVariables false

variable
  (A : X → R^[I,I]) (b : X → R^[I])
  (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible)
  (hb : Differentiable R b)


@[fun_prop]
theorem solve.arg_Ab.IsContinuousLinearMap_rule (A : R^[I,I]) (hb : IsContinuousLinearMap R b)  :
     IsContinuousLinearMap R (fun x => A.solve (b x)) := by unfold solve; fun_prop

include hA hA' hb in
@[fun_prop]
theorem solve.arg_Ab.Differentiable_rule :
     Differentiable R (fun x => (A x).solve (b x)) := by unfold solve; fun_prop (disch:=apply hA')


include hA hA' hb in
@[fun_trans]
theorem solve.arg_A.fderiv_rule  :
     fderiv R (fun x => (A x).solve (b x))
     =
     fun x => fun dx =>L[R]
       let dA := fderiv R A x dx
       let db := fderiv R b x dx
       let b := b x
       let A := A x
       (- A.solve (dA * A.solve b) + A.solve db) := by
  unfold solve
  conv =>
    lhs
    fun_trans (disch:=apply hA') only -- no idea why it does not work properly
  sorry_proof



set_option trace.Meta.Tactic.fun_trans.rewrite true in
include hA hA' hb in
@[fun_trans]
theorem solve.arg_A.fwdFDeriv_rule :
     fwdFDeriv R (fun x => (A x).solve (b x))
     =
     fun x dx =>
       let AdA := fwdFDeriv R A x dx
       let bdb := fwdFDeriv R b x dx
       let A := AdA.1; let dA := AdA.2
       let b := bdb.1; let db := bdb.2
       let A' := A.inv
       (A.solve b, - A.solve (dA * A.solve b) + A.solve db) := by
  unfold solve; funext x dx
  fun_trans (disch:=apply hA')
  cases fwdFDeriv R A x dx; cases fwdFDeriv R b x dx;
  dsimp
  sorry_proof -- done up tomodulo associativity


@[fun_trans]
theorem solve.arg_Ab.revFDeriv_rule_matrix (A : U → R^[I,I]) (b : U → R^[I])
     (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible)
     (hb : Differentiable R b) :
     revFDeriv R (fun x => (A x).solve (b x))
     =
     fun x =>
       let AdA := revFDeriv R A x
       let bdb := revFDeriv R b x
       let A := AdA.1; let dA := AdA.2
       let b := bdb.1; let db := bdb.2
       let A' := Aᵀ
       (A.solve b, fun y : R^[I] =>
         let b' := A.solve b
         let y' := A'.solve y
         let du₁ := - dA (y'.outerprod b')
         let du₂ := db y'
         du₁ + du₂) := by

  funext x
  conv =>
    lhs; unfold revFDeriv; dsimp; enter[2]
    fun_trans (disch:=apply hA')
    unfold solve
    fun_trans

  simp only [revFDeriv.revFDeriv_fst, Prod.mk.injEq, true_and]
  funext y
  have h : ∀ (A : R^[I,I]), A⁻¹ᵀ = Aᵀ⁻¹ := sorry_proof
  simp[revFDeriv,solve,h]
