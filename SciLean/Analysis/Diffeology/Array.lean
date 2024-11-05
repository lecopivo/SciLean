import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.NormedSpace
import SciLean.Data.ArrayN
import SciLean.Meta.GenerateLinearMapSimp

namespace SciLean

-- Note that the size is well definew only if `α` is nonempty
namespace Diffeology.Array.Util
open Classical in
def StableSize (f : α → Array β) : Prop := ∃ n, ∀ a, n = (f a).size

open Classical in
@[simp]
theorem stableSize_const (x : Array β) : StableSize (fun _ : α => x) :=
   ⟨x.size, by simp⟩

set_option pp.proofs.withType true in
open Classical in
theorem StableSize.sizeAt {f : α → Array β} (hf : StableSize f) (a : α) : choose hf = (f a).size := by
  have h := choose_spec hf
  exact h a

open Classical in
@[simp]
theorem StableSize.comp [Nonempty α] {f : β → Array γ} (hf : StableSize f) (g : α → β) :
    StableSize (f ∘ g) := by
  apply Exists.intro (choose hf)
  have h : Nonempty α := inferInstance
  simp[h]; intro a; rw[hf.sizeAt (g a)]


open Classical in
noncomputable
def outSize (f : α → Array β) : ℕ :=
  if h : StableSize f then
    choose h
  else
    0

open Classical in
theorem StableSize.fix_outSize_at {f : α → Array β} (hf : StableSize f) (a : α) :
    outSize f = (f a).size := by

  unfold outSize; simp[hf,hf.sizeAt a]

open Classical in
@[simp]
theorem StableSize.outSize_comp [Nonempty α] {f : β → Array γ} (hf : StableSize f) (g : α → β) :
    outSize (f∘g) = outSize f := by

  have a : α := choice inferInstance
  have hfg := hf.comp g
  unfold outSize; simp[hfg,hf,hf.sizeAt (g a), hfg.sizeAt a]

open Classical in
@[simp]
theorem StableSize.arrayN_data [Nonempty α] {f : α → ArrayN β n} : StableSize (fun x => (f x).1) := by
  apply Exists.intro n
  have a : α := choice inferInstance
  simp[(f a).data_size]

open Classical in
@[simp]
theorem outSize_array [Nonempty α] (f : α → ArrayN β n) : outSize (fun x => (f x).data) = n := by
  have a : α := choice inferInstance
  have h : StableSize (fun x => (f x).data) := ⟨n, by intro a; rw[← (f a).2]⟩
  unfold outSize; simp[h,choose_spec h a]

open Classical in
@[simp]
theorem outSize_const [Nonempty α] (x : Array β) : outSize (fun _ : α => x) = x.size := by

  unfold outSize
  have a : α := choice inferInstance
  have hn := stableSize_const (α:=α) x
  simp[hn, choose_spec hn a]

open Classical in
noncomputable
def fixSize (f : α → Array β) : α → ArrayN β (outSize f) :=
  if h : StableSize f then
    fun a => ArrayN.mk (f a) (by unfold outSize; simp[h,choose_spec h a])
  else
    fun _ => ⟨#[], by unfold outSize; simp[h]⟩

 theorem cast_arrayN_mk {n m} (x : Array α) (hn : n = x.size) (hm : m = x.size) :
  cast (by rw[hn,hm]) (ArrayN.mk x hm) = ArrayN.mk x hn := by subst hn; subst hm; simp

@[simp]
theorem fixSize_comp [Nonempty α] (f : β → Array γ) (g : α → β) (hf : StableSize f) :
    fixSize (f∘g) = fun x => cast (by rw[hf.outSize_comp g]) ((fixSize f) (g x)) := by
  unfold fixSize
  simp_all; funext a;
  rw[cast_arrayN_mk]

@[simp]
theorem fixSize_const {α β : Type*} [Nonempty α]  (y : Array β) :
    fixSize (fun _ : α => y) = fun _ => cast (by rw[outSize_const]) (ArrayN.mk y rfl) := by
  simp[fixSize]
  funext a
  rw[cast_arrayN_mk]

@[simp]
theorem fixSize_arrayN_data [Nonempty α] (f : α → ArrayN β n) :
    fixSize (fun x => (f x).data) = fun x => cast (by simp) (f x) := by
  simp[fixSize]
  funext a
  sorry


@[fun_prop]
theorem cast_clm
    {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n m} (h : n = m) :
    IsContinuousLinearMap ℝ (fun x => cast (show ArrayN X n = ArrayN X m from by rw[h]) x) := by
  subst h; simp; fun_prop

@[fun_prop]
theorem cast_contDiff
    {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n m} (h : n = m) :
    ContDiff ℝ ⊤ (fun x => cast (show ArrayN X n = ArrayN X m from by rw[h]) x) := by
  subst h; simp; fun_prop

@[fun_prop]
theorem cast_linear
    {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n m} (h : n = m) :
    IsLinearMap ℝ (fun x => cast (show ArrayN X n = ArrayN X m from by rw[h]) x) := by
  fun_prop (disch:=apply h)

#generate_linear_map_simps cast_linear

theorem clm_is_linear
    {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X →L[ℝ] Y) : IsLinearMap ℝ (fun x => f x) := by fun_prop

#generate_linear_map_simps clm_is_linear


end Diffeology.Array.Util
open Diffeology.Array.Util

variable
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

instance : Diffeology (Array X) where
  plots n f := StableSize f ∧ ContDiff ℝ ⊤ (fixSize f)
  plot_comp := by
    intros n m p f hp hf
    cases' hp with hpn hp
    have := hpn.comp f
    constructor
    · assumption
    · simp[hpn]; fun_prop (disch:=simp_all)
  const_plot := by
    intros n x
    constructor
    · apply stableSize_const
    · simp; fun_prop


-- set_option pp.proofs.withType true in
-- set_option pp.proofs true in
open Classical in
noncomputable
instance : TangentSpace (Array X) (fun x => ArrayN X x.size) where
  tangentMap c _ u du :=
    if h : StableSize c then
      cast (by rw[h.fix_outSize_at u]) (fderiv ℝ (fixSize c) u du)
    else
      0

  tangentMap_comp := by
    intros n m p f hp hf u du
    cases' hp with hpn hp
    have hpfn := hpn.comp f
    have : outSize p = outSize (p ∘ f) := (hpn.outSize_comp f).symm
    fun_trans (disch:=assumption) [fixSize_comp,hpn,hpfn]

  tangentMap_const := by
    intros n x t dt
    simp

  exp x dx t := (ArrayN.mk x rfl + t 0 • dx).1
  exp_at_zero := by simp
  exp_is_plot := by
    intro x dx
    constructor
    · apply Exists.intro x.size; simp
    · simp; fun_prop
  tangentMap_exp_at_zero := by
    intros x dx dt; simp
    fun_trans
  tangentMap_linear := by
    intro n p hp u; simp[hp.1]
    have : outSize p = (p u).size := hp.1.fix_outSize_at u
    constructor
    · intro x y; simp (disch:=assumption) only [add_push]
    · intro s x; simp (disch:=assumption) only [smul_push]


#exit

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem Array.get.arg_a.MDifferentiable_rule (i : ℕ) (x₀ : X) :
    TSSmooth (fun x : Array X => x.getD i x₀) where
  plot_preserving := by
    intro n p hp
    simp[Function.comp_def]
    let m : ℕ := (p 0).size
    let p' := fixSize p (p 0).size hp.1
    if hi : i < m then
      let i' : Fin m := ⟨i, hi⟩
      have h : (fun x => (p x)[i]?.getD x₀) = (fun x => (p' x)[i']) := sorry
      rw[h]
      have : Differentiable ℝ (fun x => p' x) := fun x => hp.2 x
      intro x; fun_prop
    else
      have h : (fun x => (p x)[i]?.getD x₀) = (fun x => x₀) := by sorry
      rw[h]
      intro x; fun_prop

  plot_independence := sorry


theorem Array.get.arg_a.mderiv_rule (i : ℕ) (x₀ : X) :
    mderiv (fun x : Array X => x.getD i x₀)
    =
    fun x dx =>
      if hi : i < x.size then
        ArrayType.get dx ⟨i,hi⟩
      else
        0 := sorry
