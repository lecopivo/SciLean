import SciLean

open SciLean

variable
  {R : Type _} [RealScalar R]
  {X : Type _} [SemiInnerProductSpace R X]
  {Y : Type _} [SemiHilbert R Y]

open ComplexConjugate

example
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDeriv R fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revDeriv R f x
      let y₂dg := revDeriv R g x
      let dx₁ := y₁df.2 y₂dg.1
      let dx₂ := y₂dg.2 y₁df.1
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr =>
         conj dr • dx₁ + dr • dx₂):=
by
  simp[revDeriv]
  funext x
  autodiff
  simp[revDeriv,revDerivUpdate,smul_push]
