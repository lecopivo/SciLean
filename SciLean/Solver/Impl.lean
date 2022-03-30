import SciLean.Operators

namespace SciLean

structure ApproxSpec {α} [Vec α] (spec : α → Prop) where
  specₙ : ℕ → α → Prop
  consistent : ∀ (aₙ : ℕ → α),
    (∀ n, specₙ n (aₙ n)) →
    (∃ a, (limit aₙ = a) → spec a)

instance {α} [Vec α] (spec : α → Prop) : CoeFun (ApproxSpec spec) (λ _ => ℕ → α → Prop) :=
  ⟨λ s n => s.specₙ n⟩

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
    (key help : String) -- `key` is used to modify value of `n₀`
    : Solver spec
| check {spec : α → Prop}
    {P : Prop} [Decidable P]
    (impl : P → Solver spec)
    (help : String)
    : Solver spec
| assumption {spec : α → Prop}
    {P : Prop}
    (impl : P → Solver spec)
    (help : String)
    : Solver spec
