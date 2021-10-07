import SciLean.Prelude

inductive Solver : {α : Type _}  → (spec : α) → Type _
  | pure  {α : Type u} 
          (impl : α) : Solver impl

  | limit {α X : Type u} {spec : α} [Vec α] 
          (lim_spec : Nat → α) 
          (n : Nat) 
          (impl : Solver (lim_spec n)) 
          (h : spec = limit lim_spec) 
          (tag : String) (help : String) : Solver spec

  | check {α : Type u} {spec : α} {P : Prop} [Decidable P] 
          (impl : P → Solver spec) 
          (help : String) : Solver spec

  | assumption {α : Type u} {spec : α} {P : Prop} 
          (impl : P → Solver spec) 
          (help : String) : Solver spec
  -- | profile {α β : Type u} {spec speca : α} {specb : α → β} (x : Solver α speca) (f : (a : α) → Solver β (specb a)) (help : String) : Solver β spec
  -- | bind {α β : Type u} {speca : α} {spec : β} (a : Solver α speca) (f : α → Solver β spec) : Solver β spec
  -- | something {α β : Type u} {spec : α → β}
  -- | pair {α β γ : Type u} (val : Solver α) (val' : Solver β) (f : α → β → γ) : Solver γ


def Impl {α} (a : α) := Solver a
def finish_impl {α} (a : α) : Impl a := Solver.pure a

namespace Solver

  def assemble {α} {spec : α} : Solver spec → IO α := sorry
  def assemble! {α} {spec : α} : Solver spec → α := sorry

end Solver
