import SciLean

open SciLean

variable
  {R : Type _} [RealScalar R]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]

open ComplexConjugate


example
  (f : X → Y) (g : X → Y)
  (hf : Differentiable R f) (hg : Differentiable R g)
  : (revFDeriv R fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revFDeriv R f x
      let y₂dg := revFDeriv R g x
      let dx₁ := y₁df.2 y₂dg.1
      let dx₂ := y₂dg.2 y₁df.1
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr =>
         conj dr • dx₁ + dr • dx₂):=
by
  simp[revFDeriv]
  funext x
  fun_trans
  simp[revFDeriv,smul_push]
