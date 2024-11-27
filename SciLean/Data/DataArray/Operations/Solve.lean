import SciLean.Data.DataArray.Operations.Inv
import SciLean.Data.DataArray.Operations.Vecmul

namespace SciLean

variable
  {I : Type*} [IndexType I] [DecidableEq I]
  {J : Type*} [IndexType J] --[DecidableEq J]
  {R : Type*} [RealScalar R] [PlainDataType R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {U : Type*} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]

namespace DataArrayN

set_option linter.unusedVariables false

variable
  (A : X → R^[I,I]) (b : X → R^[I]) (B : X → R^[I,J])
  (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible)
  (hb : Differentiable R b) (hB : Differentiable R B)

@[fun_prop]
theorem solve.arg_Ab.IsContinuousLinearMap_rule (A : R^[I,I]) (hb : IsContinuousLinearMap R b)  :
     IsContinuousLinearMap R (fun x => A.solve (b x)) := by unfold solve; fun_prop

@[fun_prop]
theorem solve'.arg_AB.IsContinuousLinearMap_rule (A : R^[I,I]) (hB : IsContinuousLinearMap R B)  :
     IsContinuousLinearMap R (fun x => A.solve' (B x)) := by unfold solve'; fun_prop

include hA hA' hb in
@[fun_prop]
theorem solve.arg_Ab.Differentiable_rule :
     Differentiable R (fun x => (A x).solve (b x)) := by unfold solve; fun_prop (disch:=apply hA')

include hA hA' hB in
@[fun_prop]
theorem solve'.arg_AB.Differentiable_rule :
     Differentiable R (fun x => (A x).solve' (B x)) := by unfold solve'; fun_prop (disch:=apply hA')


include hA hA' hb in
@[fun_trans]
theorem solve.arg_Ab.fderiv_rule  :
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


include hA hA' hB in
@[fun_trans]
theorem solve'.arg_AB.fderiv_rule  :
     fderiv R (fun x => (A x).solve' (B x))
     =
     fun x => fun dx =>L[R]
       let dA := fderiv R A x dx
       let dB := fderiv R B x dx
       let B := B x
       let A := A x
       (- A.solve' (dA * A.solve' B) + A.solve' dB) := by
  unfold solve'
  conv =>
    lhs
    fun_trans (disch:=apply hA') only -- no idea why it does not work properly
  sorry_proof


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
       (A.solve b, - A.solve (dA * A.solve b) + A.solve db) := by
  unfold solve; funext x dx
  fun_trans (disch:=apply hA')
  cases fwdFDeriv R A x dx; cases fwdFDeriv R b x dx;
  dsimp
  simp[matmul_assoc,vecmul_assoc,neg_push]


include hA hA' hB in
@[fun_trans]
theorem solve'.arg_AB.fwdFDeriv_rule :
     fwdFDeriv R (fun x => (A x).solve' (B x))
     =
     fun x dx =>
       let AdA := fwdFDeriv R A x dx
       let BdB := fwdFDeriv R B x dx
       let A := AdA.1; let dA := AdA.2
       let B := BdB.1; let dB := BdB.2
       (A.solve' B, - A.solve' (dA * A.solve' B) + A.solve' dB) := by
  unfold solve'; funext x dx
  fun_trans (disch:=apply hA') only
  cases fwdFDeriv R A x dx; cases fwdFDeriv R B x dx;
  dsimp
  simp[matmul_assoc,neg_push]


@[fun_trans]
theorem solve.arg_b.adjoint_rule (A : R^[I,I]) :
   adjoint R (fun b : R^[I] => A.solve b)
   =
   fun b => Aᵀ.solve b := by unfold solve; fun_trans


@[fun_trans]
theorem solve'.arg_B.adjoint_rule (A : R^[I,I]) :
   adjoint R (fun B : R^[I,J] => A.solve' B)
   =
   fun B => Aᵀ.solve' B := by unfold solve'; fun_trans


@[fun_trans]
theorem solve.arg_Ab.revFDeriv_rule (A : U → R^[I,I]) (b : U → R^[I])
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
  simp[revFDeriv,solve]


@[fun_trans]
theorem solve'.arg_AB.revFDeriv_rule (A : U → R^[I,I]) (B : U → R^[I,J])
     (hA : Differentiable R A) (hA' : ∀ x, (A x).Invertible)
     (hB : Differentiable R B) :
     revFDeriv R (fun x => (A x).solve' (B x))
     =
     fun x =>
       let AdA := revFDeriv R A x
       let BdB := revFDeriv R B x
       let A := AdA.1; let dA := AdA.2
       let B := BdB.1; let dB := BdB.2
       let A' := Aᵀ
       (A.solve' B, fun Y =>
         let B' := A.solve' B
         let Y' := A'.solve' Y
         let du₁ := - dA (Y' * B'ᵀ)
         let du₂ := dB Y'
         du₁ + du₂) := by

  funext x
  conv =>
    lhs; unfold revFDeriv; dsimp; enter[2]
    fun_trans (disch:=apply hA')
    unfold solve
    fun_trans

  simp only [revFDeriv.revFDeriv_fst, Prod.mk.injEq, true_and]
  funext y
  simp[revFDeriv,solve]
