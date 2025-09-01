import SciLean

namespace SciLean.ML

variable
  {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar R

@[simp_core ↑]
theorem Function.uncurry.arg_f.revFDerivProj_rule_1
  {I₁} [IndexType I₁]
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] :
  revFDerivProj R Unit (fun (f : I₁ → X) => ↿f)
  =
  fun f =>
    (↿f, fun _ df i₁ => df i₁) := sorry_proof

@[simp_core ↑]
theorem Function.uncurry.arg_f.revFDerivProj_rule_2
  {I₁} [IndexType I₁]
  {I₂} [IndexType I₂]
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] :
  revFDerivProj R Unit (fun (f : I₁ → I₂ → X) => ↿f)
  =
  fun f =>
    (↿f, fun _ df i₁ i₂ => df (i₁,i₂)) := sorry_proof

@[simp_core ↑]
theorem Function.uncurry.arg_f.revFDerivProj_rule_3
  {I₁} [IndexType I₁]
  {I₂} [IndexType I₂]
  {I₃} [IndexType I₃]
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] :
  revFDerivProj R Unit (fun (f : I₁ → I₂ → I₃ → X) => ↿f)
  =
  fun f =>
    (↿f, fun _ df i₁ i₂ i₃ => df (i₁,i₂,i₃)) := sorry_proof


open SciLean
variable {n₁ n₂ : Nat} {I : Type} [IndexType I] [DecidableEq I]
def avgPool2d {R : Type} [RealScalar R] [PlainDataType R]
    (x : R^[I,n₁,n₂]) {m₁ m₂ : Nat}
    (h₁ : m₁ = n₁/2 := by infer_var)
    (h₂ : m₂ = n₂/2 := by infer_var) : R^[I,m₁,m₂] :=
  ⊞ (ι : I) (i : Fin m₁) (j : Fin m₂) =>
    let i₁ : Fin n₁ := ⟨2*i.1, by omega⟩
    let i₂ : Fin n₁ := ⟨2*i.1+1, by omega⟩
    let j₁ : Fin n₂ := ⟨2*j.1, by omega⟩
    let j₂ : Fin n₂ := ⟨2*j.1+1, by omega⟩
    (x[ι,i₁,j₁] + x[ι,i₁,j₂] + x[ι,i₂,j₁] + x[ι,i₂,j₂])


def_fun_prop avgPool2d in x
  : Differentiable R

def_fun_trans avgPool2d in x
  add_suffix _unit
  [DecidableEq I] : revFDerivProj R Unit by unfold avgPool2d; autodiff

def_fun_trans avgPool2d in x
  add_suffix _unit
  [DecidableEq I] : revFDerivProjUpdate R Unit by unfold avgPool2d; autodiff

def_fun_trans avgPool2d in x
  [DecidableEq I] : revFDerivProj R ((I×Fin m₁×Fin m₂)×Unit) by unfold avgPool2d; autodiff

def_fun_trans avgPool2d in x
  [DecidableEq I] : revFDerivProjUpdate R ((I×Fin m₁×Fin m₂)×Unit) by unfold avgPool2d; autodiff


def_fun_trans avgPool2d in x
  [DecidableEq I] : revFDeriv R by rw[revFDeriv_eq_revFDerivProj]; autodiff
