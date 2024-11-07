import SciLean.Analysis.Diffeology.Basic
-- import SciLean.Analysis.Diffeology.NormedSpace
import SciLean.Analysis.Diffeology.VecDiffeology
import SciLean.Data.ArrayN
import SciLean.Data.ArrayType
import SciLean.Meta.GenerateLinearMapSimp

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ

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
  rw[← cast_arrayN_mk]

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
  tangentMap c u du :=
    if h : StableSize c then
      cast (by rw[h.fix_outSize_at u]) (fderiv ℝ (fixSize c) u du)
    else
      0

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



theorem array_getD_inbounds_eq_fixSize_get
    (f : α → Array β) (hf : StableSize f)
    (i : ℕ) (hi : i < outSize f)
    (v₀ : β) (x : α) :
    (f x).getD i v₀
    =
    ArrayType.get (fixSize f x) ⟨i,hi⟩ := by

  have hi' : i < (f x).size := by simp_all[hf.sizeAt x,outSize]
  simp [Array.getD_get?,hi',ArrayType.get,fixSize,hf]

theorem array_getD_outbounds_eq_default
    (f : α → Array β) (hf : StableSize f) (i : ℕ) (hi : ¬(i < outSize f))
    (v₀ : β) (x : α) :
    (f x).getD i v₀
    =
    v₀ := by

  have hi' : i ≥ (f x).size := by simp_all[hf.sizeAt x,outSize]
  simp [Array.getD_get?,hi']

section TangentMapCongr

variable
  {X : Type*} [Diffeology X] {TX : X → Type*}
  [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]

-- not sure if I can prove this ...
theorem TangentSpace.tangentMap_congr {n} {p q : ℝ^n → X} {u : ℝ^n} :
    (h : ∀ x, p x = q x) → tangentMap p u = cast (by rw[h u]) (tangentMap q u) := by sorry

class Bundle (X : Type) (TX : outParam (X → Type))  where
  map : (f : ℝ → X) → (x : ℝ) → TX (f x)

-- open Bundle
-- theorem bundle_map_cast {X} {TX} [Bundle X TX]


end TangentMapCongr

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Diffeology X] [StandardDiffeology X]


@[fun_prop]
theorem Array.getD.arg_av₀.TSSmooth_rule (i : ℕ) :
    TSSmooth (fun x : (Array X)×X => x.1.getD i x.2) where
  plot_preserving := by
    intro n p hp
    cases' hp.1 with hpn hp1
    have hp2 := StandardDiffeology.plots_smooth.1 hp.2
    apply StandardDiffeology.plots_smooth.2

    let m := outSize (Prod.fst ∘ p)

    if hi : i < m then
      simp (disch:=aesop) only
        [Function.comp_def,array_getD_inbounds_eq_fixSize_get (f:=(fun x => (p x).1))]
      fun_prop
    else
      simp (disch:=aesop) only
        [Function.comp_def,array_getD_outbounds_eq_default (f:=(fun x => (p x).1))]
      assumption

  plot_independence := by
    intro n p q u hp hq hx hdx; funext du
    simp only [Function.comp_def]
    cases' hp.1 with hpn hp1
    have hp2 := StandardDiffeology.plots_smooth.1 hp.2
    cases' hq.1 with hqn hq1
    have hq2 := StandardDiffeology.plots_smooth.1 hq.2

    let mp := outSize (Prod.fst ∘ p)
    let mq := outSize (Prod.fst ∘ q)

    have mpq : mp = mq := sorry

    have hdx₁ : fderiv ℝ (fun x => fixSize (fun x => (p x).1) x) u du
                =
                cast (by sorry) (fderiv ℝ (fun x => fixSize (fun x => (q x).1) x) u du) := sorry

    have hdx₂ : fderiv ℝ (fun x => (p x).2) u
                =
                fderiv ℝ (fun x => (q x).2) u := sorry

    if hip : i < mp then
      have hiq : i < mq := sorry
      have hhp := fun x => array_getD_inbounds_eq_fixSize_get (f:=(fun x => (p x).1)) hpn i hip (p x).2 x
      have hhq := fun x => array_getD_inbounds_eq_fixSize_get (f:=(fun x => (q x).1)) hqn i hiq (q x).2 x
      rw[TangentSpace.tangentMap_congr hhp]
      rw[TangentSpace.tangentMap_congr hhq]
      simp[TangentSpace.tangentMap]
      fun_trans
      rw[hdx₁]
      sorry -- wtf I'm supposed to do here?
    else
      have hiq : ¬(i < mq) := sorry
      have hhp := fun x => array_getD_outbounds_eq_default (f:=(fun x => (p x).1)) hpn i hip (p x).2 x
      have hhq := fun x => array_getD_outbounds_eq_default (f:=(fun x => (q x).1)) hqn i hiq (q x).2 x
      rw[TangentSpace.tangentMap_congr hhp]
      rw[TangentSpace.tangentMap_congr hhq]
      simp[hdx₂,TangentSpace.tangentMap]


@[fun_prop]
theorem Array.get?.arg_a.TSSmooth_rule (i : ℕ) :
    TSSmooth (fun x : Array X => x[i]? i) where
  plot_preserving := by
    intro n p hp
    cases' hp.1 with hpn hp1
    have hp2 := StandardDiffeology.plots_smooth.1 hp.2
    apply StandardDiffeology.plots_smooth.2

    let m := outSize (Prod.fst ∘ p)

    if hi : i < m then
      simp (disch:=aesop) only
        [Function.comp_def,array_getD_inbounds_eq_fixSize_get (f:=(fun x => (p x).1))]
      fun_prop
    else
      simp (disch:=aesop) only
        [Function.comp_def,array_getD_outbounds_eq_default (f:=(fun x => (p x).1))]
      assumption

  plot_independence := by
    intro n p q u hp hq hx hdx; funext du
    simp only [Function.comp_def]
    cases' hp.1 with hpn hp1
    have hp2 := StandardDiffeology.plots_smooth.1 hp.2
    cases' hq.1 with hqn hq1
    have hq2 := StandardDiffeology.plots_smooth.1 hq.2

    let mp := outSize (Prod.fst ∘ p)
    let mq := outSize (Prod.fst ∘ q)

    have mpq : mp = mq := sorry

    have hdx₁ : fderiv ℝ (fun x => fixSize (fun x => (p x).1) x) u du
                =
                cast (by sorry) (fderiv ℝ (fun x => fixSize (fun x => (q x).1) x) u du) := sorry

    have hdx₂ : fderiv ℝ (fun x => (p x).2) u
                =
                fderiv ℝ (fun x => (q x).2) u := sorry

    if hip : i < mp then
      have hiq : i < mq := sorry
      have hhp := fun x => array_getD_inbounds_eq_fixSize_get (f:=(fun x => (p x).1)) hpn i hip (p x).2 x
      have hhq := fun x => array_getD_inbounds_eq_fixSize_get (f:=(fun x => (q x).1)) hqn i hiq (q x).2 x
      rw[TangentSpace.tangentMap_congr hhp]
      rw[TangentSpace.tangentMap_congr hhq]
      simp[TangentSpace.tangentMap]
      fun_trans
      rw[hdx₁]
      sorry -- wtf I'm supposed to do here?
    else
      have hiq : ¬(i < mq) := sorry
      have hhp := fun x => array_getD_outbounds_eq_default (f:=(fun x => (p x).1)) hpn i hip (p x).2 x
      have hhq := fun x => array_getD_outbounds_eq_default (f:=(fun x => (q x).1)) hqn i hiq (q x).2 x
      rw[TangentSpace.tangentMap_congr hhp]
      rw[TangentSpace.tangentMap_congr hhq]
      simp[hdx₂,TangentSpace.tangentMap]



theorem hoho {X} [Add X] (x y : ArrayN X n) (i : ℕ) :
  (x + y).data[i]'sorry = x.data[i]'sorry + y.data[i]'sorry := sorry

theorem hihi {X} [SMul R X] (r : R) (x : ArrayN X n) (i : ℕ) :
  (r • x).data[i]'sorry = r • x.data[i]'sorry := sorry

@[fun_trans]
theorem Array.get.arg_a.tsderiv_rule (i : ℕ) :
    tsderiv (fun x : (Array X)×X => x.1.getD i x.2)
    =
    fun x dx =>
      if hi : i < x.1.size then
        ArrayType.get dx.1 ⟨i,hi⟩
      else
        dx.2 := by

  funext x dx
  unfold tsderiv
  split_ifs with h hi
  · simp only [TangentSpace.tangentMap,TangentSpace.exp,Function.comp_def]
    simp[Array.getD_get?,hi,hoho,hihi];
    fun_trans
    rfl
  · simp only [TangentSpace.tangentMap,TangentSpace.exp,Function.comp_def]
    simp[Array.getD_get?,hi]
    fun_trans
  · by_contra; apply h; fun_prop
  · by_contra; apply h; fun_prop


#check Array.get?
set_option trace.Meta.Tactic.fun_trans true in
set_option trace.Meta.Tactic.fun_trans.discharge true in
set_option trace.Meta.Tactic.fun_trans.unify true in
#check tsderiv (fun x : (Array ℝ)×ℝ => x.1.getD 0 0) rewrite_by fun_trans only


set_option trace.Meta.Tactic.fun_trans true in
set_option trace.Meta.Tactic.fun_trans.discharge true in
set_option trace.Meta.Tactic.fun_trans.unify true in
#check tsderiv (fun x : Array ℝ => x.getD 0 (x.getD 1 0)) rewrite_by fun_trans only
