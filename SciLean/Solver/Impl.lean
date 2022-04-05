import SciLean.Operators

namespace SciLean

inductive Solver {α : Type _} [Vec α] : (spec : α → Prop) → Type _ 
| exact {spec : α → Prop}
    (impl : α)
    (h : spec impl)
    : Solver spec
| approx {spec : α → Prop}
    (specₙ : ℕ → α → Prop)
    (consistent : ∀ (aₙ : ℕ → α),
      (∀ n, specₙ n (aₙ n)) →
      (∃ a, (limit aₙ = a) → spec a))
    (n₀ : ℕ) -- default value of `n` to be used when asembling
    (impl : (n : ℕ) → Solver (specₙ n))
    (key help : String) -- `key` is used to modify value of `n₀`
    : Solver spec
| weakApprox {spec : α → Prop}
    (specₙ : ℕ → α → Prop)
    (consistent : ∀ (aₙ : ℕ → α),
      (∀ n, specₙ n (aₙ n)) →
      (∃ a, (limit aₙ = a) → spec a))
    (n : ℕ) -- fixed aproximation at compile time
    (impl : Solver (specₙ n))
    (help : String)
    : Solver spec
| check {spec : α → Prop}
    {P : Prop} [dec : Decidable P]
    (impl : P → Solver spec)
    (help : String)
    : Solver spec
| assumption {spec : α → Prop}
    {P : Prop}
    (impl : P → Solver spec)
    (help : String)
    : Solver spec


namespace Solver

    -- Why does the termination proof fail here ???
    partial def assemble {α} {pred : α → Prop} [Vec α] : Solver pred → IO α
    | exact impl _ => Pure.pure impl
    | approx _ _ n impl key _   => (impl n).assemble
    | weakApprox _ _ _ impl _ => impl.assemble
    | check (dec := dec) impl help => 
        match dec with
          | isTrue h => (impl h).assemble
          | isFalse _ => throw (IO.userError s!"Failed check: {help}")
    | assumption impl _ => (impl sorry).assemble

    partial def assemble! {α} {pred : α → Prop} [Vec α] : Solver pred → α
    | exact impl _ => impl
    | approx _ _ n impl key _ => (impl n).assemble!
    | weakApprox _ _ _ impl _ => impl.assemble!
    | check      impl _ => (impl sorry).assemble!
    | assumption impl _ => (impl sorry).assemble!

end Solver
