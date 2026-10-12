module

public import SciLean.Analysis.AdjointSpace.Adjoint

@[expose] public section


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
    det R (fun x : X => x) = 1 := by
  have h : IsLinearMap R (fun x : X => x) := IsLinearMap.id_rule
  simp only [det, h, ↓reduceDIte]
  exact LinearMap.det_id

-- do I need finite dimensional condition?
@[fun_trans]
theorem det.comp_rule
    (f : X → X) (g : X → X) (hf : IsLinearMap R f) (hg : IsLinearMap R g) :
    det R (fun x => f (g x)) = det R f * det R g := by
  have h : IsLinearMap R (fun x => f (g x)) := IsLinearMap.comp_rule hf hg
  simp only [det, h, hf, hg, ↓reduceDIte]
  rw [← LinearMap.det_comp]
  rfl


@[fun_trans, simp_core]
theorem det.scalar_rule
    (f : R → R) (hf : IsLinearMap R f) :
    det R f = f 1 := by
  classical
  simp only [det, hf, ↓reduceDIte]
  rw [← LinearMap.det_toMatrix (Basis.singleton Unit R), Matrix.det_unique]
  simp [LinearMap.toMatrix_apply, Basis.singleton_apply]


/-- Note: this rule requires `X` to be a free module, otherwise `LinearMap.det` is defined to be
one and the statement fails e.g. for `R := ℤ` and `X := ℤ × ZMod 2`. -/
@[fun_trans]
theorem HSMul.hSMul.arg_x.det_rule [Module.Free R X]
    (r : R) (f : X → X) (hf : IsLinearMap R f)  :
    det R (fun x => r • f x) = r^(finrank R X) * det R f := by
  have h : IsLinearMap R (fun x => r • f x) := by
    constructor
    · intro x y; rw [hf.map_add, smul_add]
    · intro c x; rw [hf.map_smul, smul_comm]
  simp only [det, h, hf, ↓reduceDIte]
  rw [show IsLinearMap.mk' (fun x => r • f x) h = r • IsLinearMap.mk' f hf from rfl]
  exact LinearMap.det_smul r _


/-- Note: compared to the original statement this rule assumes that `R` is nontrivial and that `X`
is a finite free module of positive rank. For the zero module - and for a module that is not
finite free - `LinearMap.det` is `1` by definition while the right hand side is `0`, so the
statement fails there. -/
@[fun_trans]
theorem HSMul.hSMul.arg_r.det_rule [Nontrivial R] [Module.Free R X] [Module.Finite R X]
    (hX : 0 < finrank R X) (r : X → R) (v : X) (hr : IsLinearMap R r)  :
    det R (fun x => r x • v) = if (finrank R X) = 1 then r v else 0 := by
  classical
  have hlin : IsLinearMap R (fun x => r x • v) := by
    constructor
    · intro x y; rw [hr.map_add, add_smul]
    · intro c x; rw [hr.map_smul, smul_assoc]
  set b := Module.Free.chooseBasis R X with hb
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R X) = finrank R X :=
    (Module.finrank_eq_card_chooseBasisIndex R X).symm
  have hM : LinearMap.toMatrix b b (IsLinearMap.mk' _ hlin)
      = Matrix.of (fun i j => b.repr v i * r (b j)) := by
    ext i j
    simp [LinearMap.toMatrix_apply, mul_comm]
  simp only [det, hlin, ↓reduceDIte]
  rw [← LinearMap.det_toMatrix b, hM]
  by_cases h1 : finrank R X = 1
  · have hc1 : Fintype.card (Module.Free.ChooseBasisIndex R X) = 1 := by rw [hcard, h1]
    have : Unique (Module.Free.ChooseBasisIndex R X) := (Fintype.equivFinOfCardEq hc1).unique
    rw [Matrix.det_unique]
    simp only [h1, ↓reduceIte, Matrix.of_apply]
    have hv : v = b.repr v default • b default := by
      conv_lhs => rw [← b.sum_repr v]
      rw [Finset.sum_eq_single default
        (by intro c _ hc; exact absurd (Subsingleton.elim c default) hc) (by simp)]
    conv_rhs => rw [hv]
    rw [hr.map_smul]
    simp [smul_eq_mul]
  · have h2 : 1 < Fintype.card (Module.Free.ChooseBasisIndex R X) := by
      rw [hcard]; omega
    obtain ⟨i₀, i₁, hne⟩ := Fintype.exists_pair_of_one_lt_card h2
    have hsplit : (Matrix.of (fun i j => b.repr v i * r (b j)))
        = (Matrix.of (fun (i : Module.Free.ChooseBasisIndex R X)
            (_ : Module.Free.ChooseBasisIndex R X) => b.repr v i))
          * Matrix.diagonal (fun j => r (b j)) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.diagonal]
    rw [hsplit, Matrix.det_mul, Matrix.det_zero_of_column_eq hne (fun k => rfl), zero_mul]
    simp [h1]


end DetDefinition
