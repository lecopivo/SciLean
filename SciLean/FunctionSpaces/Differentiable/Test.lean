import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

import SciLean.FunctionSpaces.Differentiable.Basic


open SciLean



variable 
  {R : Type _} [NontriviallyNormedField R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace R (E i)]


example
  (f : X → Y×Z) (hf : Differentiable R f)
  : Differentiable R (fun x => (f x).1)
  := by fprop

example : 
  Differentiable R (@Prod.fst X Y)
:= by fprop

example
  (f : X → Y×Z) (hf : Differentiable R f)
  : Differentiable R (fun x => (f x).2)
  := by fprop

example : 
  Differentiable R (@Prod.snd X Y)
:= by fprop

example
  (x' : X)
  : Differentiable R fun x : X => x' + x
  := by fprop


example
  {R : Type _} [NontriviallyNormedField R]
  {K : Type _} [NontriviallyNormedField K] [NormedAlgebra R K]
  (x : R) (f : R → K) (g : R → K) 
  (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x) (hx : g x ≠ 0)
  : DifferentiableAt R (fun x => f x / g x) x 
  := by fprop


example
  {R : Type _} [NontriviallyNormedField R]
  {K : Type _} [NontriviallyNormedField K] [NormedAlgebra R K]
  (x : R) (k : K) (g : R → K) 
   (hg : DifferentiableAt R g x) (hx : g x ≠ 0)
  : DifferentiableAt R (fun x => k / g x) x 
  := by fprop


example
  {R : Type _} [NontriviallyNormedField R]
  {K : Type _} [NontriviallyNormedField K] [NormedAlgebra R K]
  (x : R) (f : R → K) (k : K)
  (hf : DifferentiableAt R f x) (hx : k ≠ 0)
  : DifferentiableAt R (fun x => f x / k) x 
  := by fprop

