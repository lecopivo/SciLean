import SciLean.FunctionSpaces.ContinuousLinearMap.Basic

open SciLean


variable 
  {R : Type _} [Semiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y]
  {Z : Type _} [TopologicalSpace Z] [AddCommMonoid Z] [Module R Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, TopologicalSpace (E i)] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]


example 
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : Y → Z) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun x => f (g x) := by is_continuous_linear_map

example 
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : X → Z) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun x => (f x, g x) := by is_continuous_linear_map

example 
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : X → Y → Z) (hf : IsContinuousLinearMap R (fun xy : X×Y => f xy.1 xy.2))
  : IsContinuousLinearMap R fun x => f x (g x) := by is_continuous_linear_map

example 
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : X → Y → Z) (hf : IsContinuousLinearMap R (fun xy : X×Y => f xy.1 xy.2))
  : IsContinuousLinearMap R fun x => let y := g x; let y' := g x; let y'' := g x; let y'' := g x; let y'' := g x; f x y := by is_continuous_linear_map


example 
  (F : (X→X) → (X →L[R] X))
  (g : X → X)
  : IsContinuousLinearMap R fun x => F g (F g x) := by is_continuous_linear_map


example 
  (F : (X→X) → (X →L[R] X))
  (g : X → X)
  : IsContinuousLinearMap R fun x => 
      let y := F g x 
      let z := F g y
      z := by is_continuous_linear_map
