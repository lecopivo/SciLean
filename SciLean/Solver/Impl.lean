axiom limit {α} : (Nat → α) → α

-- Think about `spec` as: if `h : spec a` then `a` satisfies the specification
--
-- Note: Originally `spec` had type `α` and was the non-computable function specifying our program.
-- However, this caused some problems with runtime. Using `α → Prop` deletes the spec from runtime
-- and it no longer caused some odd non-computability issues.
inductive ImplSpec {α : Type _} [Inhabited α] : (spec : α → Prop) → Type _
  | pure  {spec : α → Prop}
          (impl : α) 
          : spec impl → ImplSpec spec

  | limit {spec : α → Prop}
          (l : Nat → α)
          (n : Nat)
          (impl : ImplSpec (Eq (l n)))
          (help : String) 
          : spec (limit l) → ImplSpec spec

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



axiom opaque_id : Nat → Nat
axiom opaque_id_definition (b : Nat) : opaque_id b = b

namespace ImplSpec

  -- set_option trace.compiler true in
  def assemble {α} [Inhabited α] {pred : α → Prop} : ImplSpec pred → IO α
    | pure impl _ => impl
    | limit _ _ impl _ _ => impl.assemble
    | @check _ _ _ _ dec impl help => 
        match dec with
          | isTrue h => (impl h).assemble
          | isFalse _ => throw (IO.userError s!"Failed check: {help}")
    | assumption impl _ => (impl sorry).assemble
  
  def assemble! {α} [Inhabited α] {pred : α → Prop} : ImplSpec pred → α
    | pure impl _ => impl
    | limit _ _ impl _ _ => impl.assemble!
    | check impl _ => (impl sorry).assemble!
    | assumption impl _ => (impl sorry).assemble!

end ImplSpec

def Impl {α} [Inhabited α] (a : α) := ImplSpec (Eq a)
def finish_impl {α} [Inhabited α] {a : α} : Impl a := ImplSpec.pure a (by rfl)

namespace Impl

  variable {a} [Inhabited α]

  def assemble {a : α} (impl : Impl a) : IO α := ImplSpec.assemble impl
  def assemble! {a : α} (impl : Impl a) : α := ImplSpec.assemble! impl
  
end Impl

def id_impl : Impl opaque_id := by

  conv => enter [1,n]
          rw [opaque_id_definition]
  
  apply finish_impl

#check id_impl.assemble!

#eval id_impl.assemble! 42 -- 42


