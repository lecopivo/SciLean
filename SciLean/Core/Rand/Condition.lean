import SciLean.Core.Rand.Rand

namespace SciLean


/-- Given random variable `r : Rand (X×Y)`. Can we condition `r` based on observation of `X`?

Can we come up with conditional rand variable `r₂ : X₁ → Rand X₁`  -/
def Rand.HasCondition (r : Rand (X×Y))  : Prop :=
  ∃ r₂ : X → Rand Y,
    (do
      let x₁ ← r.fst
      let x₂ ← r₂ x₁
      return (x₁,x₂))
    =
    r

open Classical in
noncomputable
def Rand.condition (r : Rand (X×Y)) (x : X) : Rand Y :=
  if h : r.HasCondition  then
    choose h x
  else
    r.snd -- this should be some junk value

/-- Condition on the first variable of a pair. -/
noncomputable
abbrev Rand.conditionFst (r : Rand (X×Y)) (x : X) : Rand Y := r.condition x

/-- Condition on the second variable of a pair. -/
noncomputable
abbrev Rand.conditionSnd (r : Rand (X×Y)) (y : Y) : Rand X := (r.map (fun (x,y) => (y,x))).condition y
