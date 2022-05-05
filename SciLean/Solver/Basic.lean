import SciLean.Operators.Limit

namespace SciLean

-- Think about `spec` as: if `h : spec a` then `a` satisfies the specification
--
-- Note: Originally `spec` had type `α` and was the non-computable function specifying our program.
-- However, this caused some problems with runtime. Using `α → Prop` deletes the spec from runtime
-- and it no longer caused some odd non-computability issues.
inductive ImplSpec {α : Type _} : (spec : α → Prop) → Type _
  | pure  {spec : α → Prop}
          (impl : α) 
          : spec impl → ImplSpec spec

  | limit {spec : α → Prop} [Vec α]
          (l : Nat → α)
          (n : Nat)
          (impl : ImplSpec (Eq (l n)))
          (help : String) 
          : spec (limit l) → ImplSpec spec

  -- | newSpec {newSpec : α → Prop}
  --         {oldSpec : α → Prop}
  --         (valid : ∀ α, newSpec a → oldSpec a)
  --         (impl : α)
  --         (h : newSpec impl) 
  --         : ImplSpec oldSpec

  | check {spec : α → Prop} 
          {P : Prop} [Decidable P]
          (impl : P → ImplSpec spec)
          (help : String) 
          : ImplSpec spec

  | assumption {spec : α → Prop}
          {P : Prop}
          (impl : P → ImplSpec spec)
          (help : String) 
          : ImplSpec spec

--- These other constructors might be usefull down the line, mainly to turn Solver into a monad. Maybe it is a monad already, but profiling might be really usefull.

  -- | profile {α β : Type u} {spec speca : α} {specb : α → β} (x : Solver α speca) (f : (a : α) → Solver β (specb a)) (help : String) : Solver β spec
  -- | bind {α β : Type u} {speca : α} {spec : β} (a : Solver α speca) (f : α → Solver β spec) : Solver β spec
  -- | something {α β : Type u} {spec : α → β}
  -- | pair {α β γ : Type u} (val : Solver α) (val' : Solver β) (f : α → β → γ) : Solver γ

namespace ImplSpec

  def assemble {α} {pred : α → Prop} : ImplSpec pred → IO α
    | pure impl _ => Pure.pure impl
    | limit _ _ impl _ _ => impl.assemble
    | @check _ _ _ dec impl help => 
        match dec with
          | isTrue h => (impl h).assemble
          | isFalse _ => throw (IO.userError s!"Failed check: {help}")
    | assumption impl _ => (impl sorry).assemble
  
  def assemble! {α} {pred : α → Prop} : ImplSpec pred → α
    | pure impl _ => impl
    | limit _ _ impl _ _ => impl.assemble!
    | check impl _ => (impl sorry).assemble!
    | assumption impl _ => (impl sorry).assemble!

end ImplSpec

def Impl {α} (a : α) := ImplSpec (Eq a)
def implspec_to_impl {α}  (a : α) : ImplSpec (Eq a) = Impl a := by rfl
-- def finish_impl {α} [Inhabited α] {a : α} : Impl a := ImplSpec.pure a (by rfl)


namespace Impl

  variable {a}

  def assemble {a : α} (impl : Impl a) : IO α := ImplSpec.assemble impl
  def assemble! {a : α} (impl : Impl a) : α := ImplSpec.assemble! impl
  
end Impl
