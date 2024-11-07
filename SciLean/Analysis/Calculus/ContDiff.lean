import Mathlib.Analysis.Calculus.ContDiff.Basic
import SciLean.Analysis.Normed.IsContinuousLinearMap

namespace SciLean


attribute [fun_prop] ContDiff

attribute [fun_prop]
  contDiff_id
  contDiff_const
  ContDiff.comp
  contDiff_apply
  -- contDiff_pi

  ContDiff.prod
  ContDiff.fst
  ContDiff.snd



attribute [fun_prop]
  contDiff_add
  ContDiff.add
  contDiff_neg
  ContDiff.neg
  -- contDiff_sub -- missing
  ContDiff.sub
  -- contDiff_sum -- missing
  ContDiff.sum
  contDiff_mul
  ContDiff.mul
  contDiff_prod
  ContDiff.prod
  -- contDiff_pow -- missing
  ContDiff.pow
  contDiff_smul
  ContDiff.smul
  ContDiff.prod_map
  ContDiff.inv
  ContDiff.div

  ContDiff.fderiv
  ContDiff.continuous_deriv


attribute [fun_prop]
  ContDiff.differentiable
  ContDiff.continuous
  ContDiff.restrict_scalars


variable
  {R : Type*} [NontriviallyNormedField R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace R Y]
  {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace R (E i)]

@[fun_prop]
theorem contDiff_pi' {φ : X → (i : ι) → E i} (hφ : ∀ i, ContDiff R n (φ · i)) :
  ContDiff R n φ := by apply contDiff_pi.2 hφ

@[fun_prop]
theorem ContDiff.continuous_top {f : X → Y} (h : ContDiff R ⊤ f) : Continuous f :=
  contDiff_zero.1 (h.of_le bot_le)

@[fun_prop]
theorem ContDiff.differentiable_top {f : X → Y} (h : ContDiff R ⊤ f) : Differentiable R f := by
  fun_prop (disch:=simp)

@[fun_prop]
theorem contDiff_isContinuousLinearMap
    (f : X → Y) (hf : IsContinuousLinearMap R f) :
    ContDiff R ⊤ f := by

  let hf : IsBoundedLinearMap R f := by
    have h : f = (fun x =>L[R] f x) := by rfl
    rw[h]
    apply ContinuousLinearMap.isBoundedLinearMap
  apply IsBoundedLinearMap.contDiff hf

-- @[fun_prop]
-- theorem ContDiff.contDiff_top {f : X → Y} {n} (h : ContDiff R ⊤ f) : ContDiff R n f := by
--   fun_prop (disch:=aesop)

@[fun_prop]
theorem dite.arg_te.ContDiff_rule
    {R : Type*} [NontriviallyNormedField R]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace R Y]
    (c : Prop) [Decidable c]
    (f : c → X → Y)  (hf : ∀ h, ContDiff R n (f h))
    (g : ¬c → X → Y) (hg : ∀ h, ContDiff R n (g h)) :
    ContDiff R n (fun x => if h : c then f h x else g h x) := by
  split_ifs <;> aesop
