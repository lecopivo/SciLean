import SciLean

open SciLean

variable
  {R : Type} [RealScalar R]
  {X : Type _} [SemiInnerProductSpace R X]

open ComplexConjugate

example {Y : Type _} [SemiHilbert R Y]
  (g : X → Y)
  (hg : HasSemiAdjoint R g)
  : ∀ y₁ : Y, SciLean.HasSemiAdjoint R (fun xy : X×Y =>
        let dy₂ := g xy.1;
        ⟪xy.snd, g x⟫[R] + ⟪y₁, dy₂⟫[R]) :=
by
  intros
  fun_prop

example {Y : Type} [SemiHilbert R Y]
  (g : X → Y)
  (hg : HasSemiAdjoint R g) (y₁ : Y)
  : SciLean.HasSemiAdjoint R (fun xy : X×Y =>
        let dy₂ := g xy.1;
        ⟪xy.snd, g x⟫[R] + ⟪y₁, dy₂⟫[R]) :=
by
  intros
  fun_prop


variable
  {K : Type*} [IsROrC K]
  {α : Type*} -- problematic universe

example (i : α) : CDifferentiable K (fun (xy : (α → K) × (α → K)) => xy.fst i) := by fun_prop
