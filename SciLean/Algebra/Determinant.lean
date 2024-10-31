import SciLean.Analysis.AdjointSpace.Adjoint

open Module

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


@[fun_trans, simp_core]
theorem det.scalar_rule
    (f : R → R) (hf : IsLinearMap R f) :
    det R f = f 1 := sorry_proof


@[fun_trans]
theorem HSMul.hSMul.arg_x.det_rule
    (r : R) (f : X → X) (hf : IsLinearMap R f)  :
    det R (fun x => r • f x) = r^(finrank R X) * det R f := sorry_proof


@[fun_trans]
theorem HSMul.hSMul.arg_r.det_rule
    (r : X → R) (v : X) (hr : IsLinearMap R r)  :
    det R (fun x => r x • v) = if (finrank R X) = 1 then r v else 0 := sorry_proof


end DetDefinition
