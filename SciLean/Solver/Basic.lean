import SciLean.Prelude

inductive Solver : (α : Type _)  → (spec : α) → Type _
  | pure  {α : Type u} 
          (impl : α) : Solver α impl

  | limit {α X : Type u} {spec : α} [Vec X] 
          (l : Nat → X) (f : X → α) 
          (impl : (n : Nat) → Solver α (f (l n))) (n : Nat) 
          (h : spec = f (limit l)) 
          (tag : String) (help : String) : Solver α spec

  | check {α : Type u} {spec : α} {P : Prop} [Decidable P] 
          (impl : P → Solver α spec) 
          (help : String) : Solver α spec

  | assumption {α : Type u} {spec : α} {P : Prop} 
          (impl : P → Solver α spec) 
          (help : String) : Solver α spec
  -- | profile {α β : Type u} {spec speca : α} {specb : α → β} (x : Solver α speca) (f : (a : α) → Solver β (specb a)) (help : String) : Solver β spec
  -- | bind {α β : Type u} {speca : α} {spec : β} (a : Solver α speca) (f : α → Solver β spec) : Solver β spec
  -- | something {α β : Type u} {spec : α → β}
  -- | pair {α β γ : Type u} (val : Solver α) (val' : Solver β) (f : α → β → γ) : Solver γ


def Impl {α} (a : α) := Solver α a
def finish_impl {α} (a : α) : Impl a := Solver.pure a

namespace Solver

  def assemble {α} {spec : α} : Solver α spec → IO α := sorry
  def assemble! {α} {spec : α} : Solver α spec → α := sorry

end Solver
