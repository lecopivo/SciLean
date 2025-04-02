import Mathlib.Data.Nat.Notation


@[inline, specialize]
def natRecFun {n : ℕ} {X : ℕ → Type u} {Y : ℕ → Type v}
    (F : {m : ℕ} → (X m → Y m) → X (m+1) → Y (m+1))
    (F₀ : X 0 → Y 0) (x : X n) : Y n :=
  match n with
  | 0 => F₀ x
  | n+1 => F (natRecFun (n:=n) F F₀) x
