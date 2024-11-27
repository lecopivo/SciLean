import SciLean.Data.DataArray.Operations.Simps
import SciLean.Data.ArrayType.Properties
import SciLean.Meta.GenerateFunTrans


namespace SciLean


--todo: redistribute to appropriate places
section Missing

variable
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z]



theorem fderiv_wrt_prod
  {f : X → Y → Z} (hf : Differentiable R ↿f := by fun_prop) :
  fderiv R (fun xy : X×Y => f xy.1 xy.2)
  =
  fun xy => fun dxy =>L[R]
    let x := xy.1; let y := xy.2
    let dx := dxy.1; let dy := dxy.2
    let dzdx := fderiv R (f · y) x dx
    let dzdy := fderiv R (f x ·) y dy
    dzdx + dzdy := sorry

theorem fwdFDeriv_wrt_prod
    {f : X → Y → Z} (hf : Differentiable R ↿f := by fun_prop) :
    fwdFDeriv R (fun xy : X×Y => f xy.1 xy.2)
    =
    fun (xy dxy : X×Y) =>
      let x := xy.1; let y := xy.2
      let dx := dxy.1; let dy := dxy.2
      let zdz₁ := fwdFDeriv R (f · y) x dx
      let zdz₂ := fwdFDeriv R (f x ·) y dy
      let z := zdz₁.1; let dz₁ := zdz₁.2; let dz₂ := zdz₂.2
      (z, dz₁ + dz₂) := by

  unfold fwdFDeriv
  rw[fderiv_wrt_prod hf]
  fun_trans

end Missing


section Missing

variable
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [AdjointSpace R X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace R Y]
  {Z} [NormedAddCommGroup Z] [AdjointSpace R Z]

theorem adjoint_wrt_prod
    {f : X → Y → Z} (hf : IsContinuousLinearMap R ↿f := by fun_prop) :
    adjoint R (fun xy : X×Y => f xy.1 xy.2)
    =
    fun (z : Z) =>
      let x := adjoint R (f · 0) z
      let y := adjoint R (f 0 ·) z
      (x,y) := sorry


theorem revFDeriv_wrt_prod
    {f : X → Y → Z} (hf : Differentiable R ↿f := by fun_prop) :
    revFDeriv R (fun xy : X×Y => f xy.1 xy.2)
    =
    fun (xy : X×Y) =>
      let x := xy.1; let y := xy.2
      let zdz₁ := revFDeriv R (f · y) x
      let zdz₂ := revFDeriv R (f x ·) y
      let z := zdz₁.1; let dz₁ := zdz₁.2; let dz₂ := zdz₂.2
      (z, fun dz => (dz₁ dz, dz₂ dz)) := by

  unfold revFDeriv
  funext (x,y)
  rw[fderiv_wrt_prod hf]
  fun_trans
  let f' := fun dx dy => (fderiv R (fun x => f x y) x) dx + (fderiv R (fun x_1 => f x x_1) y) dy
  have h := adjoint_wrt_prod (R:=R) (f:=f') (by fun_prop)
  simp[h,f']


theorem _root_.SciLean.DataArrayN.norm2_def {R : Type*} [RCLike R] {I} [IndexType I] {X} [PlainDataType X] [Inner R X]
    (x : X^[I]) : ‖x‖₂²[R] = ∑ i, ‖x[i]‖₂²[R] := rfl

theorem _root_.SciLean.DataArrayN.inner_def {R : Type*} [RealScalar R] {I} [IndexType I] {X} [PlainDataType X] [Inner R X]
    (x y : X^[I]) : Inner.inner x y = ∑ i, Inner.inner (𝕜:=R) x[i] y[i] := rfl

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
