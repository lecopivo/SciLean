import SciLean.Analysis.Calculus.HasFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Logic.Function.Constant

import SciLean.Data.ArrayOperations.Basic
import SciLean.Data.ArrayType.Notation
import SciLean.Data.Vector

set_option linter.unusedVariables false

namespace SciLean

variable
  {K : Type*} [RCLike K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace K Z]

variable (K) in
@[data_synth out f' in f]
structure HasVecFwdFDeriv (n : ℕ) (f : X → Y) (f' : X → Vector X n → Y×Vector Y n) where
  val : ∀ x dx, (f' x dx).1 = f x
  deriv : ∃ df : X → X →L[K] Y,
      (∀ x, HasFDerivAt f (df x) x)
      ∧
      (∀ x (dx : Vector X n) (i : Fin n), df x dx[i] = (f' x dx).2[i])

open Classical in
variable (K) in
noncomputable
def vecFwdFDeriv (n : ℕ) (f : X → Y) (x : X) (dx : Vector X n) : Y × Vector Y n :=
  if h : ∃ f', HasVecFwdFDeriv K n f f' then
    choose h x dx
  else
    (0,0)


set_option linter.unusedVariables false in
theorem vecFwdFDeriv_from_hasVecFwdFDeriv
    {f : X → Y} {f'} (hf : HasVecFwdFDeriv K n f f') :
    vecFwdFDeriv K n f = f' := by
  sorry_proof

simproc_decl vecFwdFDeriv_simproc (vecFwdFDeriv _ _ _) :=
  mkDataSynthSimproc `revFDeriv_simproc ``vecFwdFDeriv_from_hasVecFwdFDeriv


----------------------------------------------------------------------------------------------------
-- API for constructing and deconstructing HasFwdFDeriv -----------------------------------
----------------------------------------------------------------------------------------------------

-- theorem hasFwdFDeriv_from_hasFDerivAt {f : X → Y}
--     {df : X → X →L[K] Y} (deriv : ∀ x, HasFDerivAt (𝕜:=K) f (df x) x)
--     {f' : X → X → Y×Y} (simp : ∀ x dx, f' x dx = (f x, df x dx)) :
--     HasFwdFDeriv K f f' := by
--   constructor
--   case val =>
--     simp[simp]
--   case deriv =>
--     apply Exists.intro df
--     simp_all


-- set_option linter.unusedVariables false in
-- -- @[to_data_synth_simproc] -- this attribute should automatically generate the following simproc
-- theorem fwdFDeriv_from_hasFwdFDeriv
--   {f : X → Y} {f'} (hf : HasFwdFDeriv K f f') :
--   fwdFDeriv K f = f' := sorry_proof

-- simproc_decl fwdFDeriv_simproc (fwdFDeriv _ _) :=
--   mkDataSynthSimproc `fwdFDeriv_simproc ``fwdFDeriv_from_hasFwdFDeriv

----------------------------------------------------------------------------------------------------
-- Lambda Theorems ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasVecFwdFDeriv

@[data_synth]
theorem id_rule : HasVecFwdFDeriv K n (fun x : X => x) (λ x dx => (x, dx)) := by
  sorry_proof

theorem const_rule (c : Y) : HasVecFwdFDeriv K n (fun _ : X => c) (λ _ _ => (c, ⊞ (i : Fin n) => (0:Y))) := by
  sorry_proof

theorem comp_rule {g : X → Y} {f : Y → Z} {g' f'}
    (hf : HasVecFwdFDeriv K n f f') (hg : HasVecFwdFDeriv K n g g') :
    HasVecFwdFDeriv K n
      (fun x => f (g x))
      (fun x dx =>
        let' (y, dy) := g' x dx;
        let' (z, dz) := f' y dy;
        (z, dz)) := by
  sorry_proof

theorem let_rule {g : X → Y} {f : Y → X → Z} {f' g'}
    (hg : HasVecFwdFDeriv K n g g') (hf : HasVecFwdFDeriv K n (fun yx : Y×X => f yx.1 yx.2) f') :
    HasVecFwdFDeriv K n
      (fun x =>
        let y := g x
        f y x)
      (fun x dx =>
        let' (y, dy) := g' x dx
        let' (z, dz) := f' (y,x) (⊞ i => (dy[i], dx[i]))
        (z, dz)) := by
  sorry_proof

@[data_synth]
theorem apply_rule {I} [IndexType I] [DecidableEq I] (i : I) :
    HasVecFwdFDeriv K n (fun x : I → X => x i)
      (fun x dx =>
        (x i, dx.map (fun dx' => dx' i))) := sorry_proof

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I} [IndexType I] [DecidableEq I] (i : I) :
    HasVecFwdFDeriv K n (fun x : (I → X)×Y => x.1 i)
      (fun x dx =>
        (x.1 i, dx.map (fun dx' => dx'.1 i))) := sorry_proof

set_option linter.unusedVariables false in
-- theorem pi_rule {I : Type*} [IndexType I]
--     {f : X → I → Y} {f' : I → _} (hf : ∀ i, HasVecFwdFDeriv K n (f · i) (f' i)) :
--     HasVecFwdFDeriv K n f
--       (fun x dx =>
--         let a := fun i => f' i x dx
--         ) := by

--   sorry_proof

set_option linter.unusedVariables false in
theorem proj_rule
    {X₁ : Type*} [NormedAddCommGroup X₁] [NormedSpace K X₁]
    {X₂ : Type*} [NormedAddCommGroup X₂] [NormedSpace K X₂]
    (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
    (hg : HasVecFwdFDeriv K n g g') (hf : f = fun x => g (p₁ x) := by rfl)
    (hp₁ : IsContinuousLinearMap K p₁ := by fun_prop) /- (hdec : Decomposition p₁ p₂ q) -/ :
    HasVecFwdFDeriv K n f
      (fun x dx =>
        let x₁ := p₁ x
        let dx₁ := dx.map p₁
        let ydy := g' x₁ dx₁
        ydy) := by
  sorry_proof

set_option linter.unusedVariables false in
theorem let_skip_rule
    {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    {g : X → α} {f : α → X → Z} {f' : α → _}
    (hf : ∀ a, HasVecFwdFDeriv K n (f a) (f' a))
    (hg : g.IsConstant) :
    HasVecFwdFDeriv K n
      (fun x =>
        let y := g x
        f y x)
      (fun x dx =>
        let a := g x
        let' (z, dz) := f' a x dx
        (z, dz)) := by
  sorry_proof


open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv,``pi_rule⟩, .pi
   --    (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv,``proj_rule⟩, .proj
      (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
      (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
      (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv,``let_skip_rule⟩, .letSkip
      (← getConstArgId ``let_skip_rule `g) (← getConstArgId ``let_skip_rule `f)
      (← getConstArgId ``let_skip_rule `hf)⟩

end HasVecFwdFDeriv
end SciLean
open SciLean


variable
  {K : Type*} [RCLike K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace K Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]



@[data_synth]
theorem Prod.mk.arg_a0a1.HasVecFwdFDeriv_comp_rule
    {f : X → Y} {g : X → Z} {f' g'}
    (hf : HasVecFwdFDeriv K n f f') (hg : HasVecFwdFDeriv K n g g') :
    HasVecFwdFDeriv K n
      (fun x => (f x, g x))
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        ((y, z), ⊞ i => (dy[i], dz[i]))) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf
  -- have ⟨_,_,_,_⟩ := hg
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all


@[data_synth]
theorem Prod.fst.arg_self.HasVecFwdFDeriv_proj_rule :
    HasVecFwdFDeriv K n
      (fun xy : X×Y => xy.1)
      (fun x dx => (x.1, dx.map Prod.fst)) := by
  sorry_proof
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem Prod.snd.arg_self.HasVecFwdFDeriv_proj_rule :
    HasVecFwdFDeriv K n
      (fun xy : X×Y => xy.2)
      (fun x dx => (x.2,dx.map Prod.snd)) := by
  sorry_proof
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasVecFwdFDeriv_comp_rule
    {f : X → Y} {g : X → Y} {f' g'}
    (hf : HasVecFwdFDeriv K n f f') (hg : HasVecFwdFDeriv K n g g') :
    HasVecFwdFDeriv K n
      (fun x => f x + g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y + z, ⊞ i => dy[i] + dz[i])) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf
  -- have ⟨_,_,_,_⟩ := hg
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem HSub.hSub.arg_a0a1.HasVecFwdFDeriv_comp_rule
    {f : X → Y} {g : X → Y} {f' g'}
    (hf : HasVecFwdFDeriv K n f f') (hg : HasVecFwdFDeriv K n g g') :
    HasVecFwdFDeriv K n
      (fun x => f x - g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y - z, ⊞ i => dy[i] - dz[i])) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf
  -- have ⟨_,_,_,_⟩ := hg
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem Neg.neg.arg_a0.HasVecFwdFDeriv_comp_rule
    {f : X → Y} {f'}
    (hf : HasVecFwdFDeriv K n f f') :
    HasVecFwdFDeriv K n
      (fun x => - f x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        (- y, ⊞ i => -dy[i])) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasVecFwdFDeriv_comp_rule
    {f : X → K} {g : X → Y} {f' g'}
    (hf : HasVecFwdFDeriv K n f f') (hg : HasVecFwdFDeriv K n g g') :
    HasVecFwdFDeriv K n
      (fun x => f x • g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y • z, ⊞ i => y • dz[i] + dy[i] • z)) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf
  -- have ⟨_,_,_,_⟩ := hg
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem HMul.hMul.arg_a0a1.HasVecFwdFDeriv_comp_rule
    {f g : X → K} {f' g'}
    (hf : HasVecFwdFDeriv K n f f') (hg : HasVecFwdFDeriv K n g g') :
    HasVecFwdFDeriv K n
      (fun x => f x * g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y * z, ⊞ i => y * dz[i] + z * dy[i])) := by
  have ⟨_,_,_,_⟩ := hf
  have ⟨_,_,_,_⟩ := hg
  sorry_proof
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem HDiv.hDiv.arg_a0a1.HasVecFwdFDeriv_comp_rule
    {f g : X → K} {f' g'}
    (hf : HasVecFwdFDeriv K n f f') (hg : HasVecFwdFDeriv K n g g')
    (hg' : ∀ x, g x ≠ 0) :
    HasVecFwdFDeriv K n
      (fun x => f x / g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y / z, ⊞ i => (z * dy[i] - y * dz[i]) / z^2)) := by
  have ⟨_,_,_,_⟩ := hf
  have ⟨_,_,_,_⟩ := hg
  sorry_proof
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth (disch:=aesop)
  -- case simp => intros; simp_all

@[data_synth]
theorem HDiv.hDiv.arg_a0.HasVecFwdFDeriv_comp_rule
    {f : X → K} (c : K) {f'}
    (hf : HasVecFwdFDeriv K n f f')  :
    HasVecFwdFDeriv K n
      (fun x => f x / c)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        (y / c, ⊞ i => dy[i] / c)) := by
  have ⟨_,_,_,_⟩ := hf
  -- HasFDerivAt seems to miss this variant
  -- so the proof is not immediate
  sorry_proof


@[data_synth]
theorem HInv.hInv.arg_a0.HasVecFwdFDeriv_comp_rule
    {f : X → K} {f'}
    (hf : HasVecFwdFDeriv K n f f')
    (hf' : ∀ x, f x ≠ 0) :
    HasVecFwdFDeriv K n
      (fun x => (f x)⁻¹)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let iy := y⁻¹
        (iy, ⊞ i => - iy^2 • dy[i])) := by
  have ⟨_,_,_,_⟩ := hf
  sorry_proof
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth (disch:=aesop)
  -- case simp => intros; simp_all; ring

@[data_synth]
theorem HPow.hPow.arg_a0.HasVecFwdFDeriv_rule_nat
    {f : X → K} {f'}
    (hf : HasVecFwdFDeriv K m f f') (n : ℕ) :
    HasVecFwdFDeriv K m
      (fun x => (f x)^n)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        (y^n, ⊞ i => n • y^(n-1) • dy[i])) := by
  have ⟨_,_,_,_⟩ := hf
  sorry_proof
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all; ring

set_option linter.unusedVariables false in
@[data_synth]
theorem SciLean.sum.arg_f.HasVecFwdFDeriv_rule
    {I : Type*} [IndexType I]
    {f : X → I → Y} {f' : I → _}
    (hf : ∀ i, HasVecFwdFDeriv K n (f · i) (f' i)) :
    HasVecFwdFDeriv K n
      (fun x => ∑ i, f x i)
      (fun x dx =>
        ∑ i,
          let ydy := f' i x dx
          ydy) := by
  sorry_proof

-- set_option linter.unusedVariables false in
-- @[data_synth]
-- theorem Finset.sum.arg_f.HasVecFwdFDeriv_rule
--     {I : Type*} (A : Finset I)
--     {f : X → I → Y} {f' : I → _}
--     (hf : ∀ i, HasVecFwdFDeriv K n (f · i) (f' i)) :
--     HasVecFwdFDeriv K n
--       (fun x => ∑ i ∈ A, f x i)
--       (fun x dx =>
--         ∑ i ∈ A,
--           let ydy := f' i x dx
--           ydy) := by
--   sorry_proof


section OverReals

variable {R K : Type*} [RealScalar R] [Scalar R K] [ScalarSMul R K] [ScalarInner R K]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace R W] [CompleteSpace W]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y] [AdjointSpace K Y]

open ComplexConjugate

@[data_synth]
theorem Inner.inner.arg_a0a1.HasVecFwdFDeriv_comp_rule
    (f g : X → Y) (f' g')
    (hf : HasVecFwdFDeriv R n f f') (hg : HasVecFwdFDeriv R n g g') :
    HasVecFwdFDeriv R n
      (fun x => ⟪f x, g x⟫[K])
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (⟪y, z⟫[K], ⊞ i => ⟪dy[i], z⟫[K] + ⟪y, dz[i]⟫[K])) := by
  have ⟨_,_,_,_⟩ := hf
  have ⟨_,_,_,_⟩ := hg
  sorry_proof
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all


@[data_synth]
theorem Norm2.norm2.arg_a0.HasVecFwdFDeriv_simple_rule :
    HasVecFwdFDeriv R n
      (fun x : Y => ‖x‖₂²[K])
      (fun x dx => (‖x‖₂²[K],
        ⊞ i =>
          let z := ⟪x,dx[i]⟫[K]
          conj z + z)) := by
  sorry_proof

@[data_synth high]
theorem Norm2.norm2.arg_a0.HasVecFwdFDeriv_simple_rule_real :
    HasVecFwdFDeriv R n
      (fun x : Y => ‖x‖₂²[R])
      (fun x dx => (‖x‖₂²[R],
        ⊞ i => 2 * ⟪x,dx[i]⟫[R])) := by
  sorry_proof
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all; (conv_rhs => enter[1]; rw[←AdjointSpace.conj_symm]; simp); ring


set_option linter.unusedVariables false in
@[data_synth]
theorem SciLean.norm₂.arg_x.HasVecFwdFDeriv_comp_rule
    (f : X → Y) {f'} (hf : HasVecFwdFDeriv R n f f') (hf' : ∀ x, f x ≠ 0) :
    HasVecFwdFDeriv R n (fun x => ‖f x‖₂[K]) (fun x dx =>
      let' (y, dy) := f' x dx;
      let yn := ‖y‖₂[K]
      (yn, ⊞ i => ⟪y, dy[i]⟫[K] / yn)) := by
  have ⟨_,_,_,_⟩ := hf
  sorry_proof

end OverReals
