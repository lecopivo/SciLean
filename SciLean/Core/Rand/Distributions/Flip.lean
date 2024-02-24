import SciLean.Core.Rand.Rand
import SciLean.Core.FloatAsReal

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob

variable {R} [RealScalar R]

def flip (x : R) : Rand Bool := {
  spec :=
    let t := (Scalar.toReal R x)     -- todo: clamp to [0,1]
    let f := (Scalar.toReal R (1-x)) -- todo: clamp to [0,1]
    erase (⟨fun φ => t • φ true + f • φ false⟩)
  rand :=
    fun g => do
    let g : StdGen := g.down
    let N := 1000000000000000
    let (n,g) := _root_.randNat g 0 N
    let y := (n : R) / (N : R)
    let b := if y ≤ x then true else false
    pure (b, ← ULiftable.up g)
}

instance (θ : R) : LawfulRand (flip θ) where
  is_measure := sorry_proof
  is_prob    := sorry_proof

@[rand_simp,simp]
theorem flip.pdf_wrt_flip (θ θ' : R) :
    (flip θ).pdf R (flip θ').ℙ
    =
    fun b => if b then θ / θ' else (1-θ) / (1-θ') := by sorry_proof

@[rand_simp,simp]
theorem flip.pdf (x : R) (_hx : x ∈ Set.Icc 0 1) :
    (flip x).pdf R .count
    =
    fun b => if b then x else (1-x) := by sorry_proof

theorem flip.measure (θ : R) :
    (flip θ).ℙ = (ENNReal.ofReal (Scalar.toReal R θ)) • Measure.dirac true
                 +
                 (ENNReal.ofReal (Scalar.toReal R (1-θ))) • Measure.dirac false :=
  sorry_proof


variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace R W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace R X] [CompleteSpace X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace R Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]


@[rand_simp,simp]
theorem flip.integral (θ : R) (f : Bool → X) :
    ∫ x, f x ∂(flip θ).ℙ = θ • f true + (1-θ) • f false := by
  simp [rand_simp,flip.measure]; sorry_proof

theorem flip.E (θ : R) (f : Bool → X) :
    (flip θ).E f = θ • f true + (1-θ) • f false := by
  simp only [Rand.E_as_integral,flip.integral]

theorem add_as_flip_E {x y : X} (θ : R) (h : θ ∈ Set.Ioo 0 1) :
    x + y = (flip θ).E (fun b => if b then θ⁻¹ • x else (1-θ)⁻¹ • y) := by
  simp[flip.E]
  have : θ ≠ 0 := by aesop
  have : 1 - θ ≠ 0 := by sorry_proof
  simp (disch:=assumption)
