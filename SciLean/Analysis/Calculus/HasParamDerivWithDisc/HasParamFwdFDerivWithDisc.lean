import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.HasParamDerivWithDisc.HasParamFDerivWithDisc

set_option linter.unusedVariables false

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [NormedSpace ℝ X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Y₁} [NormedAddCommGroup Y₁] [NormedSpace R Y₁] [NormedSpace ℝ Y₁]
  {Y₂} [NormedAddCommGroup Y₂] [NormedSpace R Y₂] [NormedSpace ℝ Y₂]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z] [CompleteSpace Z]

set_default_scalar R


variable (R)
@[gtrans]
def HasParamFwdFDerivWithDiscAt (f : W → X → Y) (w : W)
    (f' : outParam <| W → X → Y×Y)
    (disc : outParam <| DiscontinuityDataList R W X Y) : Prop :=
  HasParamFDerivWithDiscAt R f w (fun w x => (f' w x).2) disc
  ∧
  ∀ dw x, (f' dw x).1 = f w x


@[gtrans]
def HasParamFwdFDerivWithDisc (f : W → X → Y)
    (f' : outParam <| W → W → X → Y×Y)
    (disc : outParam <| List (DiscontinuityData R W X Y))
    := ∀ w : W, HasParamFwdFDerivWithDiscAt R f w (f' w) disc

variable {R}



open FiniteDimensional
@[fun_trans]
theorem fwdFDeriv_under_integral
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  (f : W → X → Y) (w : W) (μ : Measure X)
  {f' disc}
  (hf : HasParamFwdFDerivWithDiscAt R f w f' disc)
  /- (hμ : μ ≪ volume) -/ :
  (fwdFDeriv R (fun w' => ∫ x, f w' x ∂μ) w)
  =
  fun dw =>
    let interior := ∫ x, f' dw x ∂μ
    let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
    let shocks := disc.foldl (init:=0)
      fun sum ⟨df,s,S⟩ => sum +
        ∫ x in S,
          let vals := df x
          (s dw x * density x) • (vals.1 - vals.2) ∂μH[finrank R X - (1:ℕ)]
    (interior.1, interior.2 + shocks) := by

  unfold fwdFDeriv
  funext dw; ext
  · simp only [fst_integral (hf := sorry_proof), hf.2]
  · simp only [fderiv_under_integral R f w dw μ hf.1, add_left_inj, snd_integral (hf:=sorry_proof)]

open FiniteDimensional
@[fun_trans]
theorem fwdFDeriv_under_integral_over_set
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [NormedSpace ℝ X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  (f : W → X → Y) (w : W) (μ : Measure X) (A : Set X)
  {f' disc}
  (hf : HasParamFwdFDerivWithDiscAt R f w f' disc)
  (hA : AlmostDisjoint (frontier A) disc.getDiscontinuity μH[finrank ℝ X - (1:ℕ)])
  /- (hμ : μ ≪ volume) -/ :
  (fwdFDeriv R (fun w' => ∫ x in A, f w' x ∂μ) w)
  =
  fun dw =>
    let interior := ∫ x in A, f' dw x ∂μ
    let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
    let shocks := disc.foldl (init:=0)
      fun sum ⟨df,s,S⟩ => sum +
        ∫ x in S ∩ A,
          let vals := df x
          (s dw x * density x) • (vals.1 - vals.2) ∂μH[finrank R X - (1:ℕ)]
    (interior.1, interior.2 + shocks) := by

  unfold fwdFDeriv
  funext dw; ext
  · simp only [fst_integral (hf := sorry_proof), hf.2]
  · simp only [fderiv_under_integral_over_set R f w dw μ A hf.1 hA, add_left_inj, snd_integral (hf:=sorry_proof)]



----------------------------------------------------------------------------------------------------
-- Lambda rules ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasParamFwdFDerivWithDiscAt

@[gtrans high]
theorem smooth_rule
    (f : W → X → Y) (w : W) (hf : ∀ x, DifferentiableAt R (f · x) w) :
    HasParamFwdFDerivWithDiscAt (R:=R) f w
      (f' := fun dw x => fwdFDeriv R (f · x) w dw)
      []
      := by

  unfold HasParamFwdFDerivWithDiscAt
  constructor
  · apply HasParamFDerivWithDiscAt.differentiable_at_rule R w f hf
  · simp only [fwdFDeriv, implies_true]



theorem comp_differentiable_discs_rule
    (f : W → Y → Z) (g : W → X → Y) (w : W)
    {g' disc}
    (hf : Differentiable R (fun (w,y) => f w y))
    (hg : HasParamFwdFDerivWithDiscAt R g w g' disc) :
    HasParamFwdFDerivWithDiscAt (R:=R) (fun w x => f w (g w x)) w
      (f' := fun dw x =>
         let ydy := g' dw x
         let zdz := fwdFDeriv R (fun (w,y) => f w y) (w,ydy.1) (dw,ydy.2)
         zdz)
      (disc := disc.map fun ⟨vals,speed,d⟩ =>
        { vals := fun x =>
            let y := vals x
            (f w y.1, f w y.2)
          speed := speed
          discontinuity := d })
       := by

  unfold HasParamFwdFDerivWithDiscAt
  constructor
  · convert HasParamFDerivWithDiscAt.comp_differentiable_discs_rule R f g w hf hg.1
    simp [fwdFDeriv, hg.2]
  · simp [fwdFDeriv,hg.2]



@[gtrans]
theorem _root_.Prod.mk.arg_fstsnd.HasParamFwdFDerivWithDiscAt_rule
    (f : W → X → Y) (g : W → X → Z) (w : W)
    {f' fdisc} {g' gdisc}
    (hf : HasParamFwdFDerivWithDiscAt R f w f' fdisc)
    (hg : HasParamFwdFDerivWithDiscAt R g w g' gdisc)
    (hdisjoint : AlmostDisjoint fdisc.getDiscontinuity gdisc.getDiscontinuity μH[finrank ℝ X - (1:ℕ)]) :
    HasParamFwdFDerivWithDiscAt (R:=R) (fun w x => (f w x, g w x)) w
      (f' := fun dw x =>
        let ydy := f' dw x
        let zdz := g' dw x
        ((ydy.1,zdz.1), (ydy.2, zdz.2)))
      (disc :=
        fdisc.map (fun d =>
          { d with vals := fun x =>
              let y := d.vals x
              let z := g w x
              ((y.1, z), (y.2, z)) })
        ++
        gdisc.map (fun d =>
          { d with vals := fun x =>
              let y := f w x
              let z := d.vals x
              ((y, z.1), (y, z.2)) })) := by

  unfold HasParamFwdFDerivWithDiscAt
  constructor
  · exact Prod.mk.arg_fstsnd.HasParamFDerivWithDiscAt_rule _ _ _ _ (hf.1) (hg.1) hdisjoint
  · simp [hf.2, hg.2]


theorem comp1_differentiable_discs_rule
    (f : W → Y → Z) (hf : Differentiable R (fun (w,y) => f w y))
    (g : W → X → Y) (w : W)
    {g' disc}
    (hg : HasParamFwdFDerivWithDiscAt R g w g' disc) :
    HasParamFwdFDerivWithDiscAt (R:=R) (fun w x => f w (g w x)) w
      (f' := fun dw x =>
         let ydy := g' dw x
         let zdz := fwdFDeriv R (fun (w,y) => f w y) (w,ydy.1) (dw,ydy.2)
         zdz)
      (disc := disc.map fun ⟨vals,speed,d⟩ =>
        { vals := fun x =>
            let y := vals x
            (f w y.1, f w y.2)
          speed := speed
          discontinuity := d }) :=

  comp_differentiable_discs_rule f g w hf hg


theorem comp2_differentiable_discs_rule
    (f : W → Y₁ → Y₂ → Z) (hf : Differentiable R (fun (w,y₁,y₂) => f w y₁ y₂))
    (g₁ : W → X → Y₁) (g₂ : W → X → Y₂) (w : W)
    {g₁' dg₁} {g₂' dg₂}
    (hg₁ : HasParamFwdFDerivWithDiscAt R g₁ w g₁' dg₁)
    (hg₂ : HasParamFwdFDerivWithDiscAt R g₂ w g₂' dg₂)
    (hdisjoint : AlmostDisjoint dg₁.getDiscontinuity dg₂.getDiscontinuity μH[finrank ℝ X - (1:ℕ)]) :
    HasParamFwdFDerivWithDiscAt (R:=R) (fun w x => f w (g₁ w x) (g₂ w x)) w
      (f' := fun dw x =>
         let ydy₁ := g₁' dw x
         let ydy₂ := g₂' dw x
         let zdz := fwdFDeriv R (fun (w,y₁,y₂) => f w y₁ y₂) (w,ydy₁.1,ydy₂.1) (dw,ydy₁.2,ydy₂.2)
         zdz)
      (disc :=
        (dg₁.map fun d => { d with
          vals := fun x =>
           let y₁ := d.vals x
           let y₂ := g₂ w x
           (f w y₁.1 y₂, f w y₁.2 y₂) })
        ++
        (dg₂.map fun d => { d with
          vals := fun x =>
           let y₁ := g₁ w x
           let y₂ := d.vals x
           (f w y₁ y₂.1, f w y₁ y₂.2) })) := by

  convert comp_differentiable_discs_rule (R:=R) (fun w (y:Y₁×Y₂) => f w y.1 y.2) (fun w x => (g₁ w x, g₂ w x)) w
    hf (by gtrans (disch:=first | fun_prop | assumption))
  · simp[List.map_append]; rfl


end HasParamFwdFDerivWithDiscAt
open HasParamFwdFDerivWithDiscAt


@[gtrans]
def Prod.fst.arg_self.HasParamFwdFDerivWithDiscAt_rule :=
  (comp1_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Y) (fun _ yz => yz.1) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def Prod.snd.arg_self.HasParamFwdFDerivWithDiscAt_rule :=
  (comp1_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Z) (fun _ yz => yz.2) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def HAdd.hAdd.arg_a0a1.HasParamFwdFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ + y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def HSub.hSub.arg_a0a1.HasParamFwdFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ - y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def Neg.neg.arg_a0.HasParamFwdFDerivWithDiscAt_rule :=
  (comp1_differentiable_discs_rule (R:=R) (X:=X) (Y:=Y) (Z:=Y) (fun (w : W) y => - y) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def HMul.hMul.arg_a0a1.HasParamFwdFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=R) (Z:=R) (fun _ y₁ y₂ => y₁ * y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def HPow.hPow.arg_a0.HasParamFwdFDerivWithDiscAt_rule (n:ℕ) :=
  (comp1_differentiable_discs_rule (R:=R) (X:=X) (Y:=R) (Z:=R) (fun (w : W) y => y^n) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def HSMul.hSMul.arg_a0a1.HasParamFwdFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ • y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
theorem HDiv.hDiv.arg_a0a1.HasParamFwdFDerivWithDiscAt_rule
    (f g : W → X → R) (w : W)
    {f' fdisc} {g' gdisc}
    (hf : HasParamFwdFDerivWithDiscAt R f w f' fdisc)
    (hg : HasParamFwdFDerivWithDiscAt R g w g' gdisc)
    (hdisjoint : AlmostDisjoint fdisc.getDiscontinuity gdisc.getDiscontinuity μH[finrank ℝ X - (1:ℕ)])
    (hg' : ∀ x, g w x ≠ 0) :
    HasParamFwdFDerivWithDiscAt (R:=R) (fun w x => f w x / g w x) w
      (f' := fun (dw : W) x =>
         let ydy := f' dw x
         let zdz := g' dw x
         (ydy.1/zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / (zdz.1^2)))
      (disc :=
        fdisc.map (fun d =>
          { d with vals := fun x =>
              let y := d.vals x
              let z := g w x
              (y.1/z, y.2/z) })
        ++
        gdisc.map (fun d =>
          { d with vals := fun x =>
              let y := f w x
              let z := d.vals x
              (y/z.1, y/z.2) })) := by

  unfold HasParamFwdFDerivWithDiscAt
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor
  · convert HDiv.hDiv.arg_a0a1.HasParamFDerivWithDiscAt_rule _ _ _ _ (hf.1) (hg.1) hdisjoint hg'
    simp[hf.2,hg.2]
  · simp [hf.2, hg.2]


@[gtrans]
theorem ite.arg_te.HasParamFwdFDerivWithDiscAt_rule
    (f g : W → X → Y) (w : W)
    {c : W → X → Prop} [∀ w x, Decidable (c w x)]
    {f' df} {g' dg}
    (hf : HasParamFwdFDerivWithDiscAt R f w f' df)
    (hg : HasParamFwdFDerivWithDiscAt R g w g' dg)
    (hdisjoint : AlmostDisjointList (frontier {x | c w x} :: df.getDiscontinuities ++ dg.getDiscontinuities) μH[finrank ℝ X - (1:ℕ)]) :
    HasParamFwdFDerivWithDiscAt (R:=R) (fun w x => if c w x then f w x else g w x) w
      (f' := fun dw x => if c w x then f' dw x else g' dw x)
      (disc :=
        {vals := fun x => (f w x, g w x)
         speed := frontierSpeed R (fun w => {x | c w x}) w
         discontinuity := frontier {x | c w x}}
        ::
        df.map (fun d => {d with discontinuity := d.discontinuity ∩ {x | c w x}})
        ++
        dg.map (fun d => {d with discontinuity := d.discontinuity ∩ {x | ¬c w x}})) := by

  unfold HasParamFwdFDerivWithDiscAt
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor
  · convert ite.arg_te.HasParamFDerivWithDiscAt_rule _ _ _ _ (hf.1) (hg.1) hdisjoint
    simp only [hf.2, hg.2]; split_ifs <;> dsimp
  · dsimp; intros; split_ifs <;> simp [hf.2, hg.2]
