import SciLean.Core.Distribution.Basic
import SciLean.Core.FunctionTransformations
import SciLean.Core.FunctionPropositions
import SciLean.Core.Notation


open MeasureTheory

namespace SciLean

open Distribution

variable
  {R} [RealScalar R]
  {W} [Vec R W]
  {X} [Vec R X]
  {Y} [Vec R Y]
  {Z} [Vec R Z] [Module ℝ Z]

set_default_scalar R

noncomputable
def dpure (x dx : X) : 𝒟' X := ⟨fun φ => cderiv R φ x dx⟩


@[fun_prop]
def DistribDifferentiableAt (deg : ℕ∞) (f : X → 𝒟' Y) (x : X) :=
  ∀ (φ : X → Y → R), ContCDiff R deg (fun (x,y) => φ x y) → CDifferentiable R (fun x => ⟪f x, φ x⟫)


theorem distribDifferentiableAt_const_test_fun
    {deg : ℕ∞} {f : X → 𝒟' Y} {x : X}
    (hf : DistribDifferentiableAt deg f x)
    {φ : Y → R} (hφ : ContCDiff R deg φ := by fun_prop) :
    CDifferentiableAt R (fun x => ⟪f x, φ⟫) x := by
  apply hf
  fun_prop


@[fun_prop]
def DistribDifferentiable (deg : ℕ∞) (f : X → 𝒟' Y) :=
  ∀ x, DistribDifferentiableAt deg f x


open Classical in
@[fun_trans]
noncomputable
def parDistribDeriv (deg : ℕ∞) (f : X → 𝒟' Y) (x dx : X) : 𝒟' Y :=
  ⟨fun φ =>
    if _ : ContCDiff R deg φ then
      ∂ (x':=x;dx), ⟪f x', φ⟫
    else
      0⟩


----------------------------------------------------------------------------------------------------
-- Const rule --------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- TODO: we actually need some condition on `T` here
@[fun_prop]
theorem DistribDiffrentiable.const_rule (T : 𝒟' X) :
    DistribDifferentiable (R:=R) deg (fun w : W => T) := by
  intro x φ hφ
  simp
  sorry_proof

@[fun_trans]
theorem parDistribDeriv.const_rule (T : 𝒟' X) :
    parDistribDeriv (R:=R) deg (fun w : W => T)
    =
    fun w dw =>
      0 := by
  funext w dw; ext φ
  unfold parDistribDeriv
  fun_trans


----------------------------------------------------------------------------------------------------
-- Pure --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem Pure.pure.arg_x.DistribDiffrentiable_rule
    (f : X → Y) (hf : CDifferentiable R f) (hdeg : 0 < deg) :
    DistribDifferentiable (R:=R) deg (fun x => pure (f x))  := by
  intro x
  unfold DistribDifferentiableAt
  intro φ hφ
  simp only [action_pure, pure]
  fun_prop (disch:=assumption)


@[fun_trans]
theorem Pure.pure.arg_x.parDistribDeriv_rule
    (f : X → Y) (hf : CDifferentiable R f) (hdeg : 0 < deg) :
    parDistribDeriv (R:=R) deg (fun x => pure (f x))
    =
    fun x dx =>
      let ydy := fwdDeriv R f x dx
      (dpure (R:=R) ydy.1 ydy.2).restrictDeg deg := by
  funext x dx; ext φ
  unfold parDistribDeriv dpure
  simp [pure, fwdDeriv]
  if h : ContCDiff R deg φ then
    simp[h]
    fun_trans (disch:=assumption) only
  else
    simp[h]


----------------------------------------------------------------------------------------------------
-- Composition -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem DistribDiffrentiable.comp_rule
    (f : Y → 𝒟' Z) (g : X → Y)
    (hf : DistribDifferentiable deg f) (hg : CDifferentiable R g) :
    DistribDifferentiable deg (fun x => f (g x)) := by
  intro x
  unfold DistribDifferentiableAt
  intro φ hφ
  apply CDifferentiable.comp_rule (K:=R) (f:=fun xy : X×Y => ⟪f xy.2,φ xy.1⟫) (g:=fun x => (x, g x))
    (hg:=by fun_prop)
  intro x
  sorry_proof -- is this even true ?


@[fun_trans]
theorem parDistribDeriv.comp_rule
    (f : Y → 𝒟' Z) (g : X → Y)
    (hf : DistribDifferentiable deg f) (hg : CDifferentiable R g) :
    parDistribDeriv deg (fun x => f (g x))
    =
    fun x dx =>
      let ydy := fwdDeriv R g x dx
      parDistribDeriv deg f ydy.1 ydy.2 := by

  funext x dx; ext φ
  unfold parDistribDeriv
  if h : ContCDiff R deg φ then
    simp[h]
    rw[cderiv.comp_rule (K:=R) (f:=fun y => ⟪f y, φ⟫) (g:=g)
      (hf:=by intro y; apply (hf y); fun_prop) (hg:=by fun_prop)]
    rfl
  else
    simp[h]



----------------------------------------------------------------------------------------------------
-- Bind --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


-- The assumptions here are definitely not right!!!
-- I think `f` has to be `deg`
@[fun_prop]
theorem Bind.bind.arg_fx.DistribDifferentiable_rule
    (f : X → Y → 𝒟' Z) (g : X → 𝒟' Y)
    (hf : DistribDifferentiable deg (fun (x,y) => f x y)) -- `f` has to be nice enough to accomodate action of `g`
    (hg : DistribDifferentiable deg g) :
    DistribDifferentiable deg (fun x => g x >>= (f x)) := by

  intro x
  unfold DistribDifferentiableAt
  intro φ hφ
  simp
  intro x
  apply (hg x)
  . simp
    sorry_proof -- we need to strenghten assumptions on `f`


@[fun_trans]
theorem Bind.bind.arg_fx.parDistribDiff_rule
    (f : X → Y → 𝒟' Z) (g : X → 𝒟' Y)
    (hf : DistribDifferentiable deg (fun (x,y) => f x y)) -- `f` has to be nice enough to accomodate action of `g`
    (hg : DistribDifferentiable deg g) :
    parDistribDeriv deg (fun x => g x >>= (f x))
    =
    fun x dx =>
      ((parDistribDeriv deg g x dx) >>= (f x · ))
      +
      ((g x) >>= (fun y => parDistribDeriv deg (f · y) x dx)) := sorry_proof



----------------------------------------------------------------------------------------------------
-- Integral ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable [MeasureSpace X] [MeasureSpace Y] [MeasureSpace (X×Y)]

@[fun_trans]
theorem cintegral.arg_f.cderiv_distrib_rule (f : W → X → R) :
    cderiv R (fun w => ∫' x, f w x)
    =
    fun w dw =>
      ⟪parDistribDeriv ⊤ (fun w => (f w ·).toDistribution) w dw, fun _ => 1⟫ := sorry_proof


@[fun_trans]
theorem cintegral.arg_f.cderiv_distrib_rule' (f : W → X → R) (A : Set X):
    cderiv R (fun w => ∫' x in A, f w x)
    =
    fun w dw =>
      ⟪ifD A then
         parDistribDeriv ⊤ (fun w => (f w ·).toDistribution) w dw
       else
         0, fun _ => 1⟫ := sorry_proof



@[fun_trans]
theorem cintegral.arg_f.parDistribDeriv_rule (f : W → X → Y → R) :
    parDistribDeriv deg (fun w => (fun x => ∫' y, f w x y).toDistribution)
    =
    fun w dw =>
      ⟨fun φ => ⟪parDistribDeriv ⊤ (fun w => (fun (x,y) => f w x y).toDistribution) w dw, fun (x,_) => φ x⟫⟩ := sorry_proof


@[fun_trans]
theorem cintegral.arg_f.parDistribDeriv_rule' (f : W → X → Y → R) (B : X → Set Y) :
    parDistribDeriv deg (fun w => (fun x => ∫' y in B x, f w x y).toDistribution)
    =
    fun w dw =>
      ⟨fun φ => ⟪ifD {xy : X×Y | xy.2 ∈ B xy.1} then parDistribDeriv ⊤ (fun w => (fun (x,y) => f w x y).toDistribution) w dw else 0, fun (x,_) => φ x⟫⟩ := sorry_proof


-- @[fun_trans]
-- theorem cintegral.arg_f.cderiv_distrib_rule' (f : W → X → R) (A : Set X):
--     cderiv R (fun w => ∫' x in A, f w x)
--     =
--     fun w dw =>
--       ⟪ifD A then
--          parDistribDeriv ⊤ (fun w => (f w ·).toDistribution) w dw
--        else
--          0, fun _ => 1⟫ := sorry_proof




----------------------------------------------------------------------------------------------------
-- Add ---------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.DistribDifferentiable_rule (f g : W → X → R)
    /- (hf : ∀ x, CDifferentiable R (f · x)) (hg : ∀ x, CDifferentiable R (g · x)) -/ :
    DistribDifferentiable deg (fun w => (fun x => f w x + g w x).toDistribution) := by
  intro _ φ hφ; simp; sorry_proof -- fun_prop (disch:=assumption)

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.parDistribDeriv_rule (f g : W → X → R)
    /- (hf : ∀ x, CDifferentiable R (f · x)) (hg : ∀ x, CDifferentiable R (g · x)) -/ :
    parDistribDeriv deg (fun w => (fun x => f w x + g w x).toDistribution)
    =
    fun w dw =>
      parDistribDeriv deg (fun w => (f w ·).toDistribution) w dw
      +
      parDistribDeriv deg (fun w => (g w ·).toDistribution) w dw := by
  funext w dw; ext φ; simp[parDistribDeriv]
  fun_trans
  if h : ContCDiff R deg φ then
    simp[h]
    sorry_proof
  else
    simp[h]


----------------------------------------------------------------------------------------------------
-- Sub ---------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0a1.DistribDifferentiable_rule (f g : W → X → R) (hdeg : 0 < deg)
    /- (hf : ∀ x, CDifferentiable R (f · x)) (hg : ∀ x, CDifferentiable R (g · x)) -/ :
    DistribDifferentiable deg (fun w => (fun x => f w x - g w x).toDistribution) := by
  intro _ φ hφ; simp; sorry_proof -- fun_prop (disch:=assumption)


@[fun_trans]
theorem HSub.hSub.arg_a0a1.parDistribDeriv_rule (f g : W → X → R) (hdeg : 0 < deg)
    /- (hf : ∀ x, CDifferentiable R (f · x)) (hg : ∀ x, CDifferentiable R (g · x)) -/ :
    parDistribDeriv deg (fun w => (fun x => f w x - g w x).toDistribution)
    =
    fun w dw =>
      parDistribDeriv deg (fun w => (f w ·).toDistribution) w dw
      -
      parDistribDeriv deg (fun w => (g w ·).toDistribution) w dw := by
  funext w dw; ext φ; simp[parDistribDeriv]
  fun_trans
  if h : ContCDiff R deg φ then
    simp[h]
    sorry_proof
  else
    simp[h]


----------------------------------------------------------------------------------------------------
-- Mul ---------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem HMul.hMul.arg_a0a1.DistribDifferentiable_rule (f : W → X → R) (r : R)
    /- (hf : ∀ x, CDifferentiable R (f · x)) (hg : ∀ x, CDifferentiable R (g · x)) -/ :
    DistribDifferentiable deg (fun w => (fun x => r * f w x).toDistribution) := by
  intro _ φ hφ; simp; sorry_proof -- fun_prop (disch:=assumption)


@[fun_trans]
theorem HMul.hMul.arg_a0a1.parDistribDeriv_rule (f : W → X → R) (r : R)
    /- (hf : ∀ x, CDifferentiable R (f · x)) (hg : ∀ x, CDifferentiable R (g · x)) -/ :
    parDistribDeriv deg (fun w => (fun x => r * f w x).toDistribution)
    =
    fun w dw =>
      r • (parDistribDeriv deg (fun w => (f w ·).toDistribution) w dw) := by
  funext w dw; ext φ; simp[parDistribDeriv]
  fun_trans
  if h : ContCDiff R deg φ then
    simp[h]
    sorry_proof
  else
    simp[h]


----------------------------------------------------------------------------------------------------
-- Div ---------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem HDiv.hDiv.arg_a0a1.DistribDifferentiable_rule (f : W → X → R) (r : R)
    /- (hf : ∀ x, CDifferentiable R (f · x)) (hg : ∀ x, CDifferentiable R (g · x)) -/ :
    DistribDifferentiable deg (fun w => (fun x => f w x / r).toDistribution) := by
  intro _ φ hφ; simp; sorry_proof -- fun_prop (disch:=assumption)


@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.parDistribDeriv_rule (f : W → X → R) (r : R)
    /- (hf : ∀ x, CDifferentiable R (f · x)) (hg : ∀ x, CDifferentiable R (g · x)) -/ :
    parDistribDeriv deg (fun w => (fun x => f w x / r).toDistribution)
    =
    fun w dw =>
      r⁻¹ • (parDistribDeriv deg (fun w => (f w ·).toDistribution) w dw) := by
  funext w dw; ext φ; simp[parDistribDeriv]
  fun_trans
  if h : ContCDiff R deg φ then
    simp[h]
    sorry_proof
  else
    simp[h]
