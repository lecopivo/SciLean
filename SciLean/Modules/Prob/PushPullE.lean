import SciLean.Modules.Prob.Rand
import SciLean.Modules.Prob.DRand
import SciLean.Modules.Prob.FDRand

namespace SciLean.Prob

variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace R X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace R Z] [MeasurableSpace Z]


open Rand

@[rand_pull_E]
theorem weightByDensity'_pull_mean (p q : R) (x : Rand (X×X)) :
    weightByDensity' p q x.mean = (let x' ~ x; pure (weightByDensity' p q x')).mean := sorry

-- def weightByDensityM' (p q : ℝ) (ydy : Rand (Y×Y)) : Rand (Y×Y) := let ydy' ~ ydy; pure (weightByDensity' p q ydy')
@[rand_pull_E]
theorem weightByDensity'_bind (p q : R) (x : Rand (X×X)) :
    (let x' ~ x; pure (weightByDensity' p q x')) = weightByDensityM' p q x := by rfl

-- @[rand_push_E]
-- theorem ite_push_E {c} [Decidable c] (t f : FDRand X) (φ : X → Y) :
--     (if c then t else f).fdE φ = if c then t.fdE φ else f.fdE φ := by
--   if h : c then simp[h] else simp[h]


@[rand_push_E]
theorem ite_push_fdE {c} [Decidable c] (t f : FDRand X) (φ : X → Y) :
    (if c then t else f).fdE φ = if c then t.fdE φ else f.fdE φ := by
  if h : c then simp[h] else simp[h]

@[rand_pull_E mid-1]
theorem ite_pull_E_t {c} [Decidable c] (t : Rand X) (f : X) :
    (if c then t.mean else f) = (if c then t else pure f).mean  := sorry

@[rand_pull_E mid-1]
theorem ite_pull_E_f {c} [Decidable c] (t : X) (f : Rand X) :
    (if c then t else f.mean) = (if c then Rand.pure t else f).mean  := sorry

@[rand_pull_E]
theorem ite_pull_E {c} [Decidable c] (t f : Rand X) :
    (if c then t.mean else f.mean) = (if c then t else f).mean  := sorry

@[rand_pull_E]
theorem bind_pull_mean (x : Rand X) (f : X → Rand Y) :
    (x.bind (fun x' => pure (f x').mean)).mean
    =
    (x.bind f).mean := sorry


@[rand_pull_E mid-1]
theorem add_pull_mean (x : X) (f : Rand X) :
    x + f.mean = Rand.mean (X:=X) (f.bind (fun y => pure (x + y))) := sorry_proof
