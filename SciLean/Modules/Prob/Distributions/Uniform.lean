import SciLean.Modules.Prob.RandFwdDeriv
import SciLean.Core.FloatAsReal

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob

open Rand

variable {R} [RealScalar R]

instance {R} [RealScalar R] : MeasureSpace R where
  volume := sorry

def uniform (a b : R) : Rand R := {
  μ := erase (1 • volume.restrict (Set.uIcc a b) )
  is_prob := sorry
  rand := fun g => do
    let g : StdGen := g.down
    let N := 1000000000000000
    let (n,g) := _root_.randNat g 0 N
    let w := (n : R) / (N : R)
    return (a + w*(b-a),(← ULiftable.up g))
}

-- TODO: this is incorrect if `a>b`
def duniform (a b da db : R) : DRand R := {
  action := fun φ => (Scalar.toReal R db) * φ b - (Scalar.toReal R da) * φ a
}

def fduniform (a b da db : R) : FDRand R := {
  val := uniform a b
  dval := duniform a b da db
}

@[rand_simp,simp]
theorem uniform_pure_mutally_singular (a b c : R) (h : a≠b) : (uniform a b).μ ⟂ₘ (Rand.pure c).μ.out := sorry

@[rand_simp,simp]
theorem uniform_pure_mutally_singular' (a b c : R) (h : a≠b) : (Rand.pure c).μ ⟂ₘ (uniform a b).μ.out  := sorry

@[rand_simp,simp]
theorem uniform_pdf (a b : R) (θ θ' : R) (h : a < b) :
    (uniform a b).pdf R (uniform a b +[θ] (Rand.pure a +[θ'] Rand.pure b)).μ
    =
    (fun x =>
      if a < x ∧ x < b then (1-θ)⁻¹ else 0) := sorry

@[rand_simp,simp]
theorem duniform_density (a b da db : R) (θ θ' : R) (h : a < b) :
    (duniform a b da db).density R (uniform a b +[θ] (Rand.pure a +[θ'] Rand.pure b)).μ
    =
    (fun x =>
      if a < x ∧ x < b then
        (1-θ)⁻¹
      else if x = a then
        - da * θ⁻¹ * (1-θ')⁻¹
      else if x = b then
        db * θ⁻¹ * θ'⁻¹
      else
        0) := sorry


variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]


@[simp,rand_AD]
theorem uniform.arg_ab.randDeriv_rule (a b : W → R) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    randDeriv (fun w => uniform (a w) (b w))
    =
    fun w dw =>
      let da := fderiv ℝ a w dw
      let db := fderiv ℝ b w dw
      (duniform (a w) (b w) da db) := sorry


@[simp,rand_AD]
theorem uniform.arg_ab.randFwdDeriv_rule (a b : W → R) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    randFwdDeriv (fun w => uniform (a w) (b w))
    =
    fun w dw =>
      let ada := fwdFDeriv ℝ a w dw
      let bdb := fwdFDeriv ℝ b w dw
      ⟨uniform ada.1 bdb.1, duniform ada.1 bdb.1 ada.2 bdb.2⟩ := by

  funext w dw
  simp (disch:=first | assumption | sorry) [randFwdDeriv,fwdFDeriv,fduniform]


@[simp,rand_AD]
theorem uniform.arg_x.randFwdDeriv_rule_siple :
    randFwdDeriv (fun ab : R×R => uniform ab.1 ab.2)
    =
    fun ab dab =>
      ⟨uniform ab.1 ab.2, duniform ab.1 ab.2 dab.1 dab.2⟩ := sorry
