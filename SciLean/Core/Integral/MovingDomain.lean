import SciLean.Core.Notation
import SciLean.Core.Integral.CIntegral
import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.Surface

import SciLean.Tactic.RefinedSimp

import Mathlib.MeasureTheory.Decomposition.Lebesgue

open MeasureTheory

namespace SciLean


variable
  {R} [RealScalar R]
  {W} [Vec R W]
  {W'} [Vec R W']
  {X} [SemiHilbert R X]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z] [Module ℝ Z]

set_default_scalar R


def IsLipschitzDomain (A : Set U) : Prop :=
  ∃ (φ : U → ℝ),
    A = {x | φ x = 0}
    -- and some lipshitz contition

-- !!!not sure about the sign!!!
noncomputable
def levelSetSpeed (φ : W → X → R) (w dw : W) (x : X) : R :=
  - (∂ w':=w;dw, (φ w' x)) / ‖∇ (φ w ·) x‖₂

open Classical in
noncomputable
def interfaceSpeed' (A : W → Set X) (w dw : W) (x : frontier (A w)) : R :=
  -- todo: use some version of `IsLipschitzDomain` to get `φ`
  sorry
  -- if h : ∃ φ : W → X → R, ∀ w, A w = {x | 0 ≤ φ w x} then
  --   let φ := choose h
  --   levelSetSpeed φ w dw x.1
  -- else
  --   0

variable (R)
open Classical in
noncomputable
def frontierSpeed (A : W → Set X) (w dw : W) (x : X) : R :=
  match Classical.dec (∃ (φ : W → X → R), (∀ w, A w = {x | φ w x = 0})) with
  | .isTrue h =>
    let φ := Classical.choose h
    (-(∂ (w':=w;dw), φ w' x)/‖∇ x':=x, φ w x'‖₂)
  | .isFalse _ => 0

variable {R}


@[simp, ftrans_simp]
theorem frontierSpeed_levelSet (φ ψ : W → X → R) (w dw : W) (x : X) (h : φ w x = ψ w x) :
     frontierSpeed R (fun w => {x | φ w x ≤ ψ w x}) w dw x
     =
     - (∂ (w':=w;dw), (ψ w' x - φ w' x)) / ‖∇ (x':=x), (ψ w x' - φ w x')‖₂ := sorry_proof


variable [MeasureSpace X]

open FiniteDimensional

-- Probably the domain needs to be differentiable in time and lipschitz in space
@[fun_prop]
theorem moving_volume_differentiable (f : W → X → Y) (A : W → Set X)
    (hf : ∀ x, CDifferentiable R (f · x)) (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1})
    (μ : Measure X) /- todo: add absolute continuous w.r.t to lebesgue measure -/  :
    CDifferentiable R fun  w => ∫' x in A w, f w x ∂μ := sorry_proof

-- Probably the domain needs to be differentiable in time and lipschitz in space
-- @[fun_trans]
theorem moving_volume_derivative (f : W → X → Y) (A : W → Set X) (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1}) :
    (∂ w, ∫' x in A w, f w x)
    =
    fun w dw =>
      (∫' x in A w, (∂ (w':=w;dw), f w' x))
      +
      ∫' x in frontier (A w), (frontierSpeed R A w dw x) • f w x ∂(surfaceMeasure (finrank R X - 1)) := sorry_proof



----------------------------------------------------------------------------------------------------
-- Moving Frontier Integral ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

#exit

variable (R)
@[fun_trans]
noncomputable
def movingFrontierIntegral (A : W → Set X) (B : Set X) (f : X → Y) (w dw : W) : Y :=
  ∫' x in frontier (A w) ∩ B, frontierSpeed R A w dw x • f x ∂(surfaceMeasure (finrank R X - 1))
variable {R}


variable (R)
@[fun_trans]
noncomputable
def movingFrontierIntegral' (A : W → Set X) (f : X → Y) (μ : Measure X) (w dw : W) : Y :=
  ∫' x in frontier (A w),
    let s := frontierSpeed R A w dw x
    let dμdΛ := Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
    (s * dμdΛ) • f x ∂(surfaceMeasure (finrank R X - 1))
variable {R}



@[fun_trans]
theorem movingFrontierIntegral_const_rule (A B : Set X) (f : X → Y) :
    movingFrontierIntegral R (fun _ : W => A) B f
    =
    fun _ _ => 0 := sorry_proof


@[fun_trans]
theorem movingFrontierIntegral_comp_rule (h : W' → W) (A : W → Set X) (f : X → Y)
    (hf : CDifferentiable R h) :
    movingFrontierIntegral R (fun w' => A (h w')) B f
    =
    fun w' dw' =>
      let wdw := fwdDeriv R h w' dw'
      movingFrontierIntegral R A B f wdw.1 wdw.2 := sorry_proof


@[fun_trans]
noncomputable
def _root_.Set.inter.arg_s₁s₂.movingFrontierIntegral_rule (A A' : W → Set X) (B : Set X) (f : X → Y) :
    -- (hA : ∀ w, surfaceMeasure (finrank R X - 1) (frontier (A w) ∩ frontier (A' w)) = 0) :
    movingFrontierIntegral R (fun w => A w ∩ A' w) B f
    =
    fun w dw =>
      movingFrontierIntegral R (fun w => A w) (B ∩ A' w) f w dw
      +
      movingFrontierIntegral R (fun w => A' w) (B ∩ A w) f w dw := sorry_proof


@[fun_trans]
noncomputable
def _root_.Set.union.arg_s₁s₂.movingFrontierIntegral_rule (A A' : W → Set X) (B : Set X) (f : X → Y) :
    -- (hA : ∀ w, surfaceMeasure (finrank R X - 1) (frontier (A w) ∩ frontier (A' w)) = 0) :
    movingFrontierIntegral R (fun w => A w ∪ A' w) B f
    =
    fun w dw =>
      movingFrontierIntegral R (fun w => A w) (B ∩ (A' w)ᶜ) f w dw
      +
      movingFrontierIntegral R (fun w => A' w) (B ∩ (A w)ᶜ) f w dw := sorry_proof


@[rsimp ↓ (mid-1) guard A .notConst]
theorem cintegral.arg_fμ.cderiv_rule_measure (f : W → X → Y) (A : W → Set X) (μ : Measure X) :
    -- (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1}) :
    (∂ w, ∫' x in A w, f w x ∂μ)
    =
    fun w dw =>
      let ds := movingFrontierIntegral R A ⊤ (fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x) • f w x) w dw
      let di := ∂ (w':=w;dw), ∫' x in A w, f w' x ∂μ
      ds + di := sorry_proof


@[rsimp ↓ guard A .notConst]
theorem cintegral.arg_fμ.cderiv_rule (f : W → X → Y) (A : W → Set X) :
    -- (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1}) :
    (∂ w, ∫' x in A w, f w x)
    =
    fun w dw =>
      let ds := movingFrontierIntegral R A ⊤ (f w) w dw
      let di := ∂ (w':=w;dw), ∫' x in A w, f w' x
      ds + di := sorry_proof


@[rsimp ↓ (mid-1) guard A .notConst]
theorem cintegral.arg_fμ.fwdDeriv_rule_measure (f : W → X → Y) (A : W → Set X) (μ : Measure X) :
    -- (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1}) :
    (∂> w, ∫' x in A w, f w x)
    =
    fun w dw =>
      let ds := movingFrontierIntegral R A ⊤ (fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x) • f w x) w dw
      let idi := ∂> (w':=w;dw), ∫' x in A w, f w' x
      (idi.1, idi.2 + ds) := sorry_proof


@[rsimp ↓ guard A .notConst]
theorem cintegral.arg_fμ.fwdDeriv_rule (f : W → X → Y) (A : W → Set X) :
    -- (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1}) :
    (∂> w, ∫' x in A w, f w x)
    =
    fun w dw =>
      let ds := movingFrontierIntegral R A ⊤ (f w) w dw
      let idi := ∂> (w':=w;dw), ∫' x in A w, f w' x
      (idi.1, idi.2 + ds) := sorry_proof


@[rsimp ↓]
theorem cintegral.arg_fμ.cderiv_rule_if_le (f g : W → X → Y) (φ ψ : W → X → R) (A : Set X) :
    -- (hA : ∀ w, surfaceMeasure (finrank R X - 1) (frontier A) ∩ {x : φ w x = ψ w x}) = 0) :
    (∂ w, ∫' x in A, if φ w x ≤ ψ w x then f w x else g w x)
    =
    fun w dw =>
      let ds := movingFrontierIntegral R (fun w => {x : X | φ w x ≤ ψ w x}) A (fun x => f w x - g w x) w dw
      let dy := ∂ (w':=w;dw), ∫' x in (A ∩ {x : X | φ w x ≤ ψ w x}), f w' x
      let dz := ∂ (w':=w;dw), ∫' x in (A ∩ {x : X | φ w x ≤ ψ w x}ᶜ), g w' x
      ds + dy + dz := sorry_proof


@[rsimp ↓]
theorem cintegral.arg_fμ.cderiv_rule_if_lt (f g : W → X → Y) (φ ψ : W → X → R) (A : Set X) :
    -- (hA : ∀ w, surfaceMeasure (finrank R X - 1) (frontier A) ∩ {x : φ w x = ψ w x}) = 0) :
    (∂ w, ∫' x in A, if φ w x < ψ w x then f w x else g w x)
    =
    fun w dw =>
      let ds := movingFrontierIntegral R (fun w => {x : X | φ w x < ψ w x}) A (fun x => f w x - g w x) w dw
      let dy := ∂ (w':=w;dw), ∫' x in (A ∩ {x : X | φ w x ≤ ψ w x}), f w' x
      let dz := ∂ (w':=w;dw), ∫' x in (A ∩ {x : X | φ w x ≤ ψ w x}ᶜ), g w' x
      ds + dy + dz := sorry_proof




@[rsimp ↓]
theorem cintegral.arg_fμ.cderiv_rule_add (f g : W → X → Y) (A : Set X) :
    (∂ w, ∫' x in A, f w x + g w x)
    =
    fun w dw =>
      let dy := ∂ (w':=w;dw), ∫' x in A, f w' x
      let dz := ∂ (w':=w;dw), ∫' x in A, g w' x
      ds + dy + dz := sorry_proof


#exit

variable (R)
/-- -/
def HasDerivUnderIntegralAt
    (f : W → X → Y) (μ : Measure X) (w : W)
    (f' : outParam <| W → X → Y) (s : outParam <| W → Y) : Prop :=
  CDifferentiable R (fun w' => ∫' x, f w' x ∂μ)
  ∧
  ∀ dw, (∂ (w':=w;dw), ∫' x, f w' x ∂μ) = (∫' x, f' dw x ∂μ) + s dw
variable {R}



theorem cintegral.arg_f.cderiv_rule'
    (f : W → X → Y) (μ : Measure X) (w : W)
    (f' : W → X → Y) (sf : W → Y)
    (hf : HasDerivUnderIntegralAt R f μ w f' sf) :
    (∂ (w':=w), ∫' x, f w' x ∂μ)
    =
    fun dw =>
      let di := ∫' x, f' dw x ∂μ
      let sf' := sf dw
      di + sf' := sorry_proof



theorem hasDerivUnderIntegralAt_of_differentiable
    (f : W → X → Y) (μ : Measure X) (w : W)
    (hf : ∀ x, CDifferentiable R (fun w' => f w' x))
    /- μ-integrable and derivative uniformly bounded -/ :
    HasDerivUnderIntegralAt R f μ w (fun dw x => ∂ (w':=w;dw), f w' x) 0 := sorry_proof



theorem ite.arg_cte.HasDerivUnderIntegral_rule
  (t e : W → X → Y) (μ : Measure X) (w : W)
  (c : W → X → Prop) [∀ w x, Decidable (c w x)]
  (t' e' : W → X → Y) (st se : W → Y)
  (hμ : μ ≪ volume)
  (hf : HasDerivUnderIntegralAt R t (μ.restrict {x | c w x}) w t' st)
  (hg : HasDerivUnderIntegralAt R e (μ.restrict {x | c w x}ᶜ) w e' se) :
  HasDerivUnderIntegralAt R
    (fun w x => if c w x then t w x else e w x) μ w
    (fun dw x => if c w x then t' dw x else e' dw x)
    (fun dw =>
       let ds := movingFrontierIntegral' R (fun w => {x | c w x}) (fun x => t w x - e w x) μ w dw
       let st' := st dw
       let se' := se dw
       st' + se' + ds) := sorry_proof



theorem HAdd.hAdd.arg_a0a1.HasDerivUnderIntegral_rule
  (f g : W → X → Y) (μ : Measure X) (w : W)
  (f' g' : W → X → Y) (sf sg : W → Y)
  (hf : HasDerivUnderIntegralAt R f μ w f' sf)
  (hg : HasDerivUnderIntegralAt R g μ w g' sg) :
  HasDerivUnderIntegralAt R
    (fun w x => f w x + g w x) μ w
    (fun dw x =>
       let df := f' dw x
       let dg := g' dw x
       df + dg)
    (fun dw =>
       let sf' := sf dw
       let sg' := sg dw
       sf' + sg') := sorry_proof


theorem HSub.hSub.arg_a0a1.HasDerivUnderIntegral_rule
  (f g : W → X → Y) (μ : Measure X) (w : W)
  (f' g' : W → X → Y) (sf sg : W → Y)
  (hf : HasDerivUnderIntegralAt R f μ w f' sf)
  (hg : HasDerivUnderIntegralAt R g μ w g' sg) :
  HasDerivUnderIntegralAt R
    (fun w x => f w x - g w x) μ w
    (fun dw x =>
       let df := f' dw x
       let dg := g' dw x
       df - dg)
    (fun dw =>
       let sf' := sf dw
       let sg' := sg dw
       sf' - sg') := sorry_proof


theorem Neg.neg.arg_a0.HasDerivUnderIntegral_rule
  (f : W → X → Y) (μ : Measure X) (w : W)
  (f' : W → X → Y) (sf : W → Y)
  (hf : HasDerivUnderIntegralAt R f μ w f' sf) :
  HasDerivUnderIntegralAt R
    (fun w x => -f w x) μ w
    (fun dw x =>
       let df := f' dw x
       (-df))
    (fun dw =>
       let sf' := sf dw
       (-sf')) := sorry_proof

theorem HSMul.hSMul.arg_a1.HasDerivUnderIntegral_rule
  (c : R) (f : W → X → Y) (μ : Measure X) (w : W)
  (f' : W → X → Y) (sf : W → Y)
  (hf : HasDerivUnderIntegralAt R f μ w f' sf) :
  HasDerivUnderIntegralAt R
    (fun w x => c • f w x) μ w
    (fun dw x =>
       let df := f' dw x
       c • df)
    (fun dw =>
       let sf' := sf dw
       c • sf') := sorry_proof

theorem HSMul.hSMul.arg_a0.HasDerivUnderIntegral_rule
  (f : W → X → R) (y : Y) (μ : Measure X) (w : W)
  (f' : W → X → R) (sf : W → R)
  (hf : HasDerivUnderIntegralAt R f μ w f' sf) :
  HasDerivUnderIntegralAt R
    (fun w x => f w x • y) μ w
    (fun dw x =>
       let df := f' dw x
       df • y)
    (fun dw =>
       let sf' := sf dw
       sf' • y) := sorry_proof


----------------------------------------------------------------------------------------------------

variable (R)
def HasFwdDerivUnderIntegralAt
    (f : W → X → Y) (μ : Measure X) (w : W)
    (f' : outParam <| W → X → Y×Y) (s : outParam <| W → Y) : Prop :=
  ∀ dw, (∂> (w':=w;dw), ∫' x, f w' x ∂μ) = (∫' x, f' dw x ∂μ) + (0, s dw)
variable {R}


theorem ite.arg_cte.HasFwdDerivUnderIntegral_rule
  (t e : W → X → Y) (μ : Measure X) (w : W)
  (c : W → X → Prop) [∀ w x, Decidable (c w x)]
  (t' e' : W → X → Y×Y) (st se : W → Y)
  (hf : HasFwdDerivUnderIntegralAt R t (μ.restrict {x | c w x}) w t' st)
  (hg : HasFwdDerivUnderIntegralAt R e (μ.restrict {x | c w x}ᶜ) w e' se) :
  HasFwdDerivUnderIntegralAt R
    (fun w x => if c w x then t w x else e w x) μ w
    (fun dw x => if c w x then t' dw x else e' dw x)
    (fun dw =>
       let ds := movingFrontierIntegral R (fun w => {x : X | c w x}) A (fun x => t w x - e w x) w dw
       let st' := st dw
       let se' := se dw
       (st' + se' + ds)) := sorry_proof

theorem HAdd.hAdd.arg_a0a1.HasFwdDerivUnderIntegral_rule
  (f g : W → X → Y) (μ : Measure X) (w : W)
  (f' g' : W → X → Y×Y) (sf sg : W → Y)
  (hf : HasFwdDerivUnderIntegralAt R f μ w f' sf)
  (hg : HasFwdDerivUnderIntegralAt R g μ w g' sg) :
  HasFwdDerivUnderIntegralAt R
    (fun w x => f w x + g w x) μ w
    (fun dw x =>
       let df := f' dw x
       let dg := g' dw x
       (df.1 + dg.1, df.2 + dg.2))
    (fun dw =>
       let sf' := sf dw
       let sg' := sg dw
       sf' + sg') := sorry_proof


theorem HSub.hSub.arg_a0a1.HasFwdDerivUnderIntegral_rule
  (f g : W → X → Y) (μ : Measure X) (w : W)
  (f' g' : W → X → Y×Y) (sf sg : W → Y)
  (hf : HasFwdDerivUnderIntegralAt R f μ w f' sf)
  (hg : HasFwdDerivUnderIntegralAt R g μ w g' sg) :
  HasFwdDerivUnderIntegralAt R
    (fun w x => f w x - g w x) μ w
    (fun dw x =>
       let df := f' dw x
       let dg := g' dw x
       (df.1 - dg.1, df.2 - dg.2))
    (fun dw =>
       let sf' := sf dw
       let sg' := sg dw
       sf' - sg') := sorry_proof


theorem Neg.neg.arg_a0.HasFwdDerivUnderIntegral_rule
  (f : W → X → Y) (μ : Measure X) (w : W)
  (f' : W → X → Y×Y) (sf : W → Y)
  (hf : HasFwdDerivUnderIntegralAt R f μ w f' sf) :
  HasFwdDerivUnderIntegralAt R
    (fun w x => -f w x) μ w
    (fun dw x =>
       let df := f' dw x
       (-df.1, -df.2))
    (fun dw =>
       let sf' := sf dw
       (-sf')) := sorry_proof

theorem HSMul.hSMul.arg_a0.HasFwdDerivUnderIntegral_rule
  (f : W → X → R) (y : Y) (μ : Measure X) (w : W)
  (f' : W → X → R×R) (sf : W → R)
  (hf : HasFwdDerivUnderIntegralAt R f μ w f' sf) :
  HasFwdDerivUnderIntegralAt R
    (fun w x => f w x • y) μ w
    (fun dw x =>
       let df := f' dw x
       (df.1 • y, df.2 • y))
    (fun dw =>
       let sf' := sf dw
       sf' • y) := sorry_proof

theorem HSMul.hSMul.arg_a1.HasFwdDerivUnderIntegral_rule
  (c : R) (f : W → X → Y) (μ : Measure X) (w : W)
  (f' : W → X → Y×Y) (sf : W → Y)
  (hf : HasFwdDerivUnderIntegralAt R f μ w f' sf) :
  HasFwdDerivUnderIntegralAt R
    (fun w x => c • f w x) μ w
    (fun dw x =>
       let df := f' dw x
       (c • df.1, c • df.2))
    (fun dw =>
       let sf' := sf dw
       c • sf') := sorry_proof


----------------------------------------------------------------------------------------------------

section HasRevDerivUnderIntegralAt

variable
  {W : Type u} [SemiInnerProductSpace R W] [Module ℝ W]
  {Y : Type u} [SemiInnerProductSpace R Y] [Module ℝ Y]


variable (R)
def HasRevDerivUnderIntegralAt
    (f : W → X → Y) (μ : Measure X) (w : W)
    (f' : outParam <| X → Y×(Y→W)) (s : outParam <| Y → W) : Prop :=
  (<∂ (w':=w), ∫' x, f w' x ∂μ) = (∫' x, f' x ∂μ) + (0,s)
variable {R}


theorem cintegral.arg_f.revDeriv_rule
    (f : W → X → Y) (μ : Measure X) (w : W)
    (f' : X → Y×(Y→W)) (sf : Y → W)
    (hf : HasRevDerivUnderIntegralAt R f μ w f' sf):
    (<∂ (w':=w), ∫' x, f w x ∂μ)
    =
    let ydf := ∫' x, f' x ∂μ
    (ydf.1,
     fun dy =>
       let sf' := sf dy
       ydf.2 dy + sf') := sorry_proof


theorem HAdd.hAdd.arg_a0a1.HasRevDerivUnderIntegralAt_rule
  (f g : W → X → Y) (μ : Measure X) (w : W)
  (f' g' : X → Y×(Y→W)) (sf sg : Y → W)
  (hf : HasRevDerivUnderIntegralAt R f μ w f' sf)
  (hg : HasRevDerivUnderIntegralAt R g μ w g' sg) :
  HasRevDerivUnderIntegralAt R
    (fun w x => f w x + g w x) μ w
    (fun x =>
      let df := f' x
      let dg := g' x
      (df.1 + dg.1,
       fun dy =>
         df.2 dy + dg.2 dy))
    (λ dy =>
      let sf' := sf dy
      let sg' := sg dy
      sf' + sg') := sorry_proof
