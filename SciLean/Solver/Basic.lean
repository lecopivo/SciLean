import SciLean.Prelude

inductive Impl : {α : Type _}  → (spec : α) → Type _
  | pure  {α : Type u} 
          (impl : α) : Impl impl

  | limit {α : Type u} {spec : α} [Vec α] 
          (lim_spec : Nat → α) 
          (n : Nat) 
          (impl : Impl (lim_spec n)) 
          (h : spec = limit lim_spec) 
          (help : String) : Impl spec

  | check {α : Type u} {spec : α} {P : Prop} [Decidable P] 
          (impl : P → Impl spec) 
          (help : String) : Impl spec

  | assumption {α : Type u} {spec : α} {P : Prop} 
          (impl : P → Impl spec) 
          (help : String) : Impl spec
  -- | profile {α β : Type u} {spec speca : α} {specb : α → β} (x : Solver α speca) (f : (a : α) → Solver β (specb a)) (help : String) : Solver β spec
  -- | bind {α β : Type u} {speca : α} {spec : β} (a : Solver α speca) (f : α → Solver β spec) : Solver β spec
  -- | something {α β : Type u} {spec : α → β}
  -- | pair {α β γ : Type u} (val : Solver α) (val' : Solver β) (f : α → β → γ) : Solver γ

namespace Impl

  def assemble {α} {spec : α} : Impl spec → IO α 
    | pure impl => impl
    | limit _ _ impl _ _ => impl.assemble
    | @check _ _ _ dec impl help => 
       match dec with
         | isFalse h => throw (IO.userError s!"Failed check: {help}")
         | isTrue  h => (impl h).assemble
    | assumption impl _ => (impl sorry).assemble

  def assemble! {α} {spec : α} : Impl spec → α 
    | pure impl => impl
    | limit _ _ impl _ _ => impl.assemble!
    | @check _ _ _ dec impl help => (impl sorry).assemble!
    | assumption impl _ => (impl sorry).assemble!

end Impl
