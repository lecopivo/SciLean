import Mathlib.Algebra.Ring.Basic

class Nontrivial (α : Type u_3) : Prop where
  exists_pair_ne : ∃ (x y : α), x ≠ y

class Field (K : Type u) extends CommRing K, Div K, Inv K, HPow K Int K, Nontrivial K :=
(div_eq_mul_inv : ∀ a b : K, a / b = a * b⁻¹)
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)
(hpow_succ : ∀ (a : K) (n : Int), a^(n+1) = a * a^n)
(hpow_neg  : ∀ (a : K) (n : Int), (a^n)⁻¹ = a^(-n)) 


