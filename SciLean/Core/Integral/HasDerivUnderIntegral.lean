import SciLean.Notation
import SciLean.Core.Integral.CIntegral
import SciLean.Core.Integral.Surface
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation

import SciLean.Tactic.GTrans

import Mathlib.MeasureTheory.Decomposition.Lebesgue

open MeasureTheory FiniteDimensional

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [Vec R W]
  {W'} [Vec R W']
  {X} [SemiHilbert R X] [MeasurableSpace X]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z] [Module ℝ Z]


set_default_scalar R


variable (R)

/-- -/
@[gtrans]
def HasDerivUnderIntegralAt
    (f : W → X → Y) (μ : Measure X) (w : W)
    (f' : outParam <| W → X → Y) (s : outParam <| W → Y) : Prop :=
  CDifferentiable R (fun w' => ∫' x, f w' x ∂μ)
  ∧
  ∀ dw, (∂ (w':=w;dw), ∫' x, f w' x ∂μ) = (∫' x, f' dw x ∂μ) + s dw


-- TODO: add option to `fun_trans` to specify main argument
--       right now it picks the right most argument that has function type
@[fun_trans]
noncomputable
def movingFrontierIntegral (f : X → Y) (A : W → Set X) (μ : Measure X) (w dw : W) : Y :=
  ∂ (w':=w;dw), ∫' x in (A w'), f x ∂μ


variable {R}


----------------------------------------------------------------------------------------------------
-- Moving Frontier Integral ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- This does not seem to play well with `fun_trans`
-- `rsimp` is the best option here as it indexes the lambda correctly
@[ftrans_simp, rsimp ↓]
theorem movingFrontierIntegral_le_set {X} [SemiHilbert R X] [MeasureSpace X] (φ ψ : W → X → R) (f : X → Y) (μ : Measure X) :
    movingFrontierIntegral R f (fun w : W => {x | φ w x ≤ ψ w x}) μ
    =
    fun w dw =>
      let st := fun x => ∂ (w':=w;dw), (φ w' x - ψ w' x)
      let sx := fun x => ‖∇ (x':=x), (φ w x' - ψ w x')‖₂
      let s := fun x => -st x/sx x
      let density := fun x => Scalar.ofENNReal (μ.rnDeriv volume x)
      ∫' x in {x | φ w x = ψ w x}, (s x * density x) • f x ∂(surfaceMeasure (finrank R X - 1)) := sorry_proof


@[fun_trans]
theorem movingFrontierIntegral_const_rule (A : Set X) (f : X → Y) (μ : Measure X) :
    movingFrontierIntegral R f (fun _ : W => A) μ
    =
    fun _ _ => 0 := sorry_proof


@[fun_trans]
theorem movingFrontierIntegral_comp_rule (g : W' → W) (A : W → Set X) (f : X → Y) (μ : Measure X)
    (hg : CDifferentiable R g) :
    movingFrontierIntegral R f (fun w' => A (g w')) μ
    =
    fun w' dw' =>
      let wdw := fwdDeriv R g w' dw'
      movingFrontierIntegral R f A μ wdw.1 wdw.2 := sorry_proof


@[fun_trans]
noncomputable
def _root_.Set.inter.arg_s₁s₂.movingFrontierIntegral_rule (A A' : W → Set X) (f : X → Y) (μ : Measure X) :
    -- (hμ : μ ≪ volume)
    -- (hA : ∀ w, surfaceMeasure (finrank R X - 1) (frontier (A w) ∩ frontier (A' w)) = 0) :
    movingFrontierIntegral R f (fun w => A w ∩ A' w) μ
    =
    fun w dw =>
      movingFrontierIntegral R f (fun w => A w) (μ.restrict (A' w)) w dw
      +
      movingFrontierIntegral R f (fun w => A' w) (μ.restrict (A w)) w dw := sorry_proof


@[fun_trans]
noncomputable
def _root_.Set.union.arg_s₁s₂.movingFrontierIntegral_rule (A A' : W → Set X) (f : X → Y) (μ : Measure X) :
    -- (hμ : μ ≪ volume)
    -- (hA : ∀ w, surfaceMeasure (finrank R X - 1) (frontier (A w) ∩ frontier (A' w)) = 0) :
    movingFrontierIntegral R f (fun w => A w ∪ A' w) μ
    =
    fun w dw =>
      movingFrontierIntegral R f (fun w => A w) (μ.restrict (A' w)ᶜ) w dw
      +
      movingFrontierIntegral R f (fun w => A' w) (μ.restrict (A w)ᶜ) w dw := sorry_proof


----------------------------------------------------------------------------------------------------
-- HasDerivUnderIntegral ---------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


@[fun_trans]
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



@[gtrans] -- (priority:=low)
theorem hasDerivUnderIntegralAt_of_differentiable
    (f : W → X → Y) (μ : Measure X) (w : W)
    (hf : ∀ x, CDifferentiable R (fun w' => f w' x))
    /- μ-integrable and derivative uniformly bounded -/ :
    HasDerivUnderIntegralAt R f μ w (fun dw x => ∂ (w':=w;dw), f w' x) 0 := sorry_proof


@[gtrans]
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


@[gtrans]
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


@[gtrans]
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


@[gtrans]
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


@[gtrans]
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


@[gtrans]
theorem cintegral.arg_f.HasDerivUnderIntegral_rule
  {Y} [SemiHilbert R Y] [MeasurableSpace Y]
  (w : W) (f : W → X → Y → Z) (μ : Measure X) (ν : Measure Y)
  (f' : W → X×Y → Z) (sf : W → Z)
  (hf : HasDerivUnderIntegralAt R (fun w (xy : X×Y) => f w xy.1 xy.2) (μ.prod ν) w f' sf) :
  HasDerivUnderIntegralAt R (fun w x => ∫' y, f w x y ∂ν) μ w (fun dw x => ∫' y, f' dw (x,y) ∂ν) sf := sorry_proof


@[gtrans]
theorem ite.arg_cte.HasDerivUnderIntegral_rule
  (t e : W → X → Y) (μ : Measure X) (w : W)
  (c : W → X → Prop) [∀ w x, Decidable (c w x)]
  (t' e' : W → X → Y) (st se : W → Y)
  -- (hμ : μ ≪ volume)
  (hf : HasDerivUnderIntegralAt R t (μ.restrict {x | c w x}) w t' st)
  (hg : HasDerivUnderIntegralAt R e (μ.restrict {x | c w x}ᶜ) w e' se) :
  HasDerivUnderIntegralAt R
    (fun w x => if c w x then t w x else e w x) μ w
    (fun dw x => if c w x then t' dw x else e' dw x)
    (fun dw =>
       let ds := movingFrontierIntegral R (fun x => t w x - e w x) (fun w => {x | c w x}) μ w dw
       let st' := st dw
       let se' := se dw
       st' + se' + ds) := sorry_proof
