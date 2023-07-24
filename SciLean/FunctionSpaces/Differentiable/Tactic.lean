import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

import SciLean.FunctionSpaces.Differentiable.Basic

set_option profiler true
set_option profiler.threshold 10

example : Differentiable ℝ (fun x : ℝ => x) := by fprop

example (y : ℝ) : Differentiable ℝ (fun _ : ℝ => y + y) := by fprop

example : Differentiable ℝ (fun x : ℝ => x + x) := by fprop

example : Differentiable ℝ (fun x : ℝ => x + x + x + x) := by fprop

example : Differentiable ℝ (fun x : ℝ => x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x) := by fprop

example (x : ℝ) : Differentiable ℝ (HAdd.hAdd x) := by fprop

example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ f := by fprop
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ (fun x => f x) := by fprop
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ (fun x => f x) := by fprop
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ (fun x => f x + x) := by fprop
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ (fun x => f x + f x) := by fprop
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ (fun x => f (f x)) := by fprop

-- set_option trace.Meta.Tactic.fprop.step true
-- set_option trace.Meta.Tactic.fprop.unify true
-- set_option trace.Meta.Tactic.fprop.apply true
-- set_option trace.Meta.Tactic.fprop.discharge true 

example (op : ℝ → ℝ → ℝ) (hop : Differentiable ℝ (fun (x,y) => op x y)) 
  (f : ℝ → ℝ) (hf : Differentiable ℝ f)
  (g : ℝ → ℝ) (hg : Differentiable ℝ g)
  : Differentiable ℝ (fun x => op (f x) (g x)) := by fprop

example (op : ℝ → ℝ → ℝ) (hop : Differentiable ℝ (fun (x,y) => op x y)) 
  (f : ℝ → ℝ) (hf : Differentiable ℝ f)
  (g : ℝ → ℝ) (hg : Differentiable ℝ g)
  : Differentiable ℝ (fun x => op (f x) (op (f x) (g x))) := by fprop

example 
  (g : ℝ → ℝ) (hg : Differentiable ℝ g)
  (f : ℝ → ℝ → ℝ) (hf : Differentiable ℝ (fun (x,y) => f x y))
  : Differentiable ℝ (fun x => f x (g x)) := by fprop

example 
  (g : ℝ → ℝ) (hg : Differentiable ℝ g)
  (f : ℝ → ℝ → ℝ) (hf : Differentiable ℝ (fun (x,y) => f x y))
  : Differentiable ℝ (fun x => let y := g x; f x y) := by fprop

example (f : ι → ℝ → ℝ) (i : ι) (hf : ∀ i, Differentiable ℝ (f i))
  : Differentiable ℝ (fun x => f i x) := by fprop

example (f : ι → ℝ → ℝ) (i : ι) (hf : ∀ i, Differentiable ℝ (f i))
  : Differentiable ℝ (f i) := by fprop


example [Fintype ι] (f : ℝ → ι → ℝ) (hf : ∀ i, Differentiable ℝ (fun x => f x i))
  : Differentiable ℝ (fun x i => f x i) := by fprop


theorem b [Fintype ι] (f : ℝ → ι → ℝ) (hf : ∀ i, Differentiable ℝ (fun x => f x i))
  : ∀ i, Differentiable ℝ (fun x => f x i) := by fprop


example : Differentiable ℝ (fun x : ℝ => let y := x + x; y) := by fprop

-- set_option trace.Meta.Tactic.fprop.apply true in
-- set_option trace.Meta.Tactic.fprop.step true in
-- set_option trace.Meta.Tactic.fprop.discharge true in
-- set_option pp.funBinderTypes true in
example : Differentiable ℝ (fun x : ℝ => let y := x; x) := by fprop

example : Differentiable ℝ (fun x : ℝ => 
  let x1 := x
  let x2 := x1
  let x3 := x2
  x) := by fprop

example : Differentiable ℝ (fun x : ℝ => 
  let x1 := x
  let x2 := x1
  let x3 := x2
  x3) := by fprop

example : Differentiable ℝ (fun x : ℝ => 
  let x1 := x
  let x2 := x1
  let x3 := x2
  let x4 := x3
  x4) := by fprop

example : Differentiable ℝ (fun x : ℝ => 
  let x1 := x
  let x2 := x1
  let x3 := x2
  let x4 := x3
  let x5 := x4
  let x6 := x5
  x6) := by fprop


example : Differentiable ℝ (fun x : ℝ => 
  let x1 := x
  let x2 := x + x1
  let x3 := x + x1 + x2
  let x4 := x + x1 + x2 + x3
  x4) := by fprop


example : Differentiable ℝ (fun x : ℝ => 
  let x1 := x
  let x2 := x + x1
  let x3 := x + x1 + x2
  let x4 := x + x1 + x2 + x3
  let x5 := x + x1 + x2 + x3 + x4
  let x6 := x + x1 + x2 + x3 + x4 + x5
  let x7 := x + x1 + x2 + x3 + x4 + x5 + x6
  x7) := by fprop


example : Differentiable ℝ (fun x : ℝ => 
  let x1 := x + x
  let x2 := x1 + x1
  let x3 := x2 + x2
  let x4 := x3 + x3
  let x5 := x4 + x4
  let x6 := x5 + x5
  let x7 := x6 + x6
  x7) := by fprop


example : Differentiable ℝ (fun x : ℝ => 
  let x1 := x
  let x2 := x + x1
  let x3 := x + x1 + x2
  let x4 := x + x1 + x2 + x3
  x4) := by fprop


theorem hoho : Differentiable ℝ (fun x : ℝ => let y := x + x + x + x + x + (x + x + x + x + x + x + x + x + x + x + (x + x + x) + x) + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + (x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x + x + x + x); y + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x) := by fprop


example : Differentiable ℝ (fun x : ℝ => x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x) := by fprop

example : Differentiable ℝ (fun x : ℝ => x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x) := by differentiable

example : Differentiable ℝ (fun x : ℝ => let y := x + x; let z := x + y; let f := fun x : ℝ => x + x; f y + y + x + z) := by differentiable


