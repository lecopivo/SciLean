import SciLean.Data.DataArray.Operations.Simps
import SciLean.Data.ArrayType.Properties
import SciLean.Meta.GenerateFunTrans

set_option linter.unusedVariables false

namespace SciLean


section Missing

variable
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [AdjointSpace R X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace R Y]
  {Z} [NormedAddCommGroup Z] [AdjointSpace R Z]


theorem revFDerivProj_wrt_prod
    {f : X → Y → Z} (hf : Differentiable R ↿f := by fun_prop) :
    revFDerivProj R Unit (fun xy : X×Y => f xy.1 xy.2)
    =
    fun (xy : X×Y) =>
      let x := xy.1; let y := xy.2
      let zdz₁ := revFDerivProj R Unit (f · y) x
      let zdz₂ := revFDerivProj R Unit (f x ·) y
      let z := zdz₁.1; let dz₁ := zdz₁.2; let dz₂ := zdz₂.2
      (z, fun i dz => (dz₁ i dz, dz₂ i dz)) := by

  unfold revFDerivProj
  funext (x,y)
  rw[fderiv_wrt_prod hf]
  fun_trans
  let f' := fun dx dy => (fderiv R (fun x => f x y) x) dx + (fderiv R (fun x_1 => f x x_1) y) dy
  have h := adjoint_wrt_prod (K:=R) (f:=f') (by fun_prop)
  simp[h,f']

theorem revFDerivProjUpdate_wrt_prod
    {f : X → Y → Z} (hf : Differentiable R ↿f := by fun_prop) :
    revFDerivProjUpdate R Unit (fun xy : X×Y => f xy.1 xy.2)
    =
    fun (xy : X×Y) =>
      let x := xy.1; let y := xy.2
      let zdz₁ := revFDerivProjUpdate R Unit (f · y) x
      let zdz₂ := revFDerivProjUpdate R Unit (f x ·) y
      let z := zdz₁.1; let dz₁ := zdz₁.2; let dz₂ := zdz₂.2
      (z, fun i dz dxy =>
        let dx := dxy.1; let dy := dxy.2;
        (dz₁ i dz dx, dz₂ i dz dy)) := by

  unfold revFDerivProjUpdate
  rw[revFDerivProj_wrt_prod]
  funext x
  simp; funext i de (dx,dy); simp


theorem _root_.SciLean.DataArrayN.norm2_def {R : Type*} [RCLike R] {I} [IndexType I] {X} [PlainDataType X] [Inner R X]
    (x : X^[I]) : ‖x‖₂²[R] = ∑ i, ‖x[i]‖₂²[R] := rfl

theorem _root_.SciLean.DataArrayN.inner_def {R : Type*} [RealScalar R] {I} [IndexType I] {X} [PlainDataType X] [Inner R X]
    (x y : X^[I]) : Inner.inner x y = ∑ i, Inner.inner (𝕜:=R) x[i] y[i] := rfl

@[simp, simp_core]
theorem oneHot_unit {X} [Zero X] (i : Unit) (x : X) : oneHot i x = x := rfl

end Missing

variable {I : Type*} [IndexType I]
variable {R : Type*} [RealScalar R] [PlainDataType R]


open DataArrayN

def_fun_prop multiply in x
  with_transitive : IsContinuousLinearMap R by unfold DataArrayN.multiply; sorry_proof

def_fun_prop multiply in y
  with_transitive : IsContinuousLinearMap R by unfold DataArrayN.multiply; sorry_proof

#generate_linear_map_simps DataArrayN.multiply.arg_x.IsLinearMap_rule
#generate_linear_map_simps DataArrayN.multiply.arg_y.IsLinearMap_rule

def_fun_prop multiply in x y
  with_transitive : Differentiable R by unfold DataArrayN.multiply; sorry_proof

abbrev_fun_trans multiply in x y : fderiv R by
  rw[fderiv_wrt_prod (by fun_prop)]
  fun_trans

abbrev_fun_trans multiply in x y : fwdFDeriv R by
  rw[fwdFDeriv_wrt_prod (by fun_prop)]
  autodiff

abbrev_fun_trans multiply in x : adjoint R  by
  equals (fun x' => y.multiply x') =>
    funext x
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def,DataArrayN.multiply,mul_assoc]

abbrev_fun_trans multiply in y : adjoint R by
  equals (fun y' => x.multiply y') =>
    funext y
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def,DataArrayN.multiply]
    ac_rfl


abbrev_fun_trans multiply in x y : revFDeriv R by
  rw[revFDeriv_wrt_prod (by fun_prop)]
  unfold revFDeriv
  autodiff
