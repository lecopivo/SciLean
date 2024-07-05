import SciLean.Core.FunctionTransformations

open FiniteDimensional

namespace SciLean

set_option linter.unusedVariables false

section DetDefinition

variable {R : Type*} [CommRing R]
  {X} [AddCommGroup X] [Module R X]
  {Y} [AddCommGroup Y] [Module R Y]
  {Z} [AddCommGroup Z] [Module R Z]

variable (R)
open Classical in
@[fun_trans]
noncomputable
def det (f : X → X) : R :=
  if h : IsLinearMap R f then
    LinearMap.det (IsLinearMap.mk' f h)
  else
    1


@[fun_trans]
theorem det.id_rule :
    det R (fun x : X => x) = 1 := sorry_proof

-- do I need finite dimensional condition?
@[fun_trans]
theorem det.comp_rule
    (f : X → X) (g : X → X) (hf : IsLinearMap R f) (hg : IsLinearMap R g) :
    det R (fun x => f (g x)) = det R f * det R g := sorry_proof


@[fun_trans, ftrans_simp]
theorem det.scalar_rule
    (f : R → R) (hf : IsLinearMap R f) :
    det R f = f 1 := sorry_proof


open FiniteDimensional in
@[fun_trans]
theorem HSMul.hSMul.arg_x.det_rule
    (r : R) (f : X → X) (hf : IsLinearMap R f)  :
    det R (fun x => r • f x) = r^(finrank R X) * det R f := sorry_proof


open FiniteDimensional in
@[fun_trans]
theorem HSMul.hSMul.arg_r.det_rule
    (r : X → R) (v : X) (hr : IsLinearMap R r)  :
    det R (fun x => r x • v) = if (finrank R X) = 1 then r v else 0 := sorry_proof


end DetDefinition


variable
  {R} [RealScalar R]
  {U} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]
  {V} [NormedAddCommGroup V] [AdjointSpace R V] [CompleteSpace V]
  {W} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]


variable (R)
@[fun_trans]
noncomputable
def jacobian (g : U → V) (x : U) : R :=
  let dg := fderiv R g x
  let dg' :=  adjoint R dg
  Scalar.sqrt (det R (dg' ∘ dg))

variable {R}


@[fun_trans]
theorem jacobian.id_rule :
    jacobian R (fun x : U => x)
    =
    fun _ => 1 := sorry_proof


@[fun_trans]
theorem jacobian.const_rule (y : V) :
    jacobian R (fun (_ : U) => y)
    =
    fun _ => if finrank R U = 0 then 1 else 0 := sorry_proof


@[fun_trans]
theorem jacobian.comp_rule (f : U → V) (g : U → U)
    (hf : Differentiable R f) (hg : Differentiable R g) :
    jacobian R (fun x => f (g x))
    =
    fun x => jacobian R f x * jacobian R g x := by sorry_proof


open FiniteDimensional in
@[fun_trans]
theorem HSMul.hSMul.arg_x.jacobian_rule
    (r : R) (f : U → V) (hf : Differentiable R f)  :
    jacobian R (fun x => r • f x)
    =
    fun x =>
      (Scalar.abs r)^(finrank R U) • jacobian R f x := sorry_proof


open FiniteDimensional in
@[fun_trans]
theorem Prod.mk.arg_xy.jacobian_rule
    (f : U → V) (g : U → W) (hf : Differentiable R f) (hg : Differentiable R g) :
    jacobian R (fun x => (f x, g x))
    =
    fun x =>
      let Jf := fun dx => fderiv R f x dx
      let Jg := fun dx => fderiv R g x dx
      let Gf := fun dx => adjoint R Jf (Jf dx)
      let Gg := fun dx => adjoint R Jg (Jg dx)
      Scalar.sqrt (Scalar.abs (det R (fun dx => Gf dx + Gg dx))) := sorry_proof
