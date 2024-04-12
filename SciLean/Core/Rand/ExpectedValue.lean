import SciLean.Core.Rand.Rand
import SciLean.Core.Distribution.ParametricDistribFwdDeriv

namespace SciLean

open MeasureTheory

variable
  {R} [RealScalar R]
  {W} [Vec R W]
  {X} [MeasurableSpace X] [Vec R X]
  {Y} [Vec R Y] [Module ℝ Y]

set_default_scalar R

@[fun_trans]
theorem Rand.𝔼.arg_r.cderiv_rule (r : W → Rand X) (f : X → Y) :
  cderiv R (fun w => (r w).𝔼 f)
  =
  fun w dw =>
    let d := parDistribDeriv (fun w => (r w).ℙ.toDistribution (R:=R)) w dw
    d.extAction f (fun r ⊸ fun y ⊸ ((r • y) : Y)) := sorry_proof

@[fun_trans]
theorem Rand.𝔼.arg_rf.cderiv_rule' (r : W → Rand X) (f : W → X → Y)
  (hf : ∀ x, CDifferentiable R (f · x)) :
  cderiv R (fun w => (r w).𝔼 (f w))
  =
  fun w dw =>
    let dr := parDistribFwdDeriv (fun w => (r w).ℙ.toDistribution (R:=R)) w dw
    let df := fun x => fwdDeriv R (f · x) w dw
    dr.extAction df (fun rdr ⊸ fun ydy ⊸ rdr.1•ydy.2 + rdr.2•ydy.1) := sorry_proof



theorem Rand.𝔼_deriv_as_distribDeriv {X} [Vec R X] [MeasureSpace X]
  (r : W → Rand X) (f : W → X → Y) :
  cderiv R (fun w => (r w).𝔼 (f w))
  =
  fun w dw =>
    parDistribDeriv (fun w => (fun x => ((r w).pdf R volume x) • f w x).toDistribution (R:=R)) w dw |>.integrate := sorry


-- variable
--   {X : Type _} [SemiInnerProductSpace R X] [MeasurableSpace X]
--   {W : Type _} [SemiInnerProductSpace R W]
--   {Y : Type _} [SemiInnerProductSpace R Y] [Module ℝ Y]
--   {Z : Type _} [SemiInnerProductSpace R Z] [Module ℝ Z]
--   {U} [SemiHilbert R U] [MeasureSpace U]


-- @[fun_trans]
-- theorem Rand.𝔼.arg_r.revDeriv_rule' (r : W → Rand X) (f : W → X → Y)
--   (hf : ∀ x, HasAdjDiff R (f · x)) :
--   revDeriv R (fun w => (r w).𝔼 (f w))
--   =
--   fun w =>
--     let dr := parDistribRevDeriv (fun w => (r w).ℙ.toDistribution (R:=R)) w
--     let df := fun x => revDeriv' R (f · x) w
--     dr.extAction df ⟨fun rdr => ⟨fun ydf => (rdr.1•ydf.1, fun dy => ydf.2 (rdr.1•dy) + rdr.2 ⟪ydf.1,dy⟫),sorry_proof⟩,sorry_proof⟩ := sorry_proof
