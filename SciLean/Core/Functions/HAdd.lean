import SciLean.Core


section NormedSpaces

variable 
  {R : Type _} [NontriviallyNormedField R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace R (E i)]


@[fprop]
theorem HAdd.hAdd.arg_a0a1.DifferentiableAt_rule
  (x : X) (f g : X → Y) (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x)
  : DifferentiableAt R (fun x => f x + g x) x
  := DifferentiableAt.add hf hg


end NormedSpaces
