import SciLean
import SciLean.Core.IsInv
import SciLean.Core.InvFun

open SciLean

-- Tests necessary to get wave equation example to work

example 
  : ∂ (λ (x : Fin n → ℝ) => ∑ i, ‖ x i‖²)
    =
    λ x dx => ∑ i, 2 * ⟪dx i, x i⟫
  := by fun_trans


example {ι} [Enumtype ι]
  : ∂ (λ (x : ι → ℝ) => ∑ i, ‖ x i ‖²)
    =
    λ x dx => ∑ i, 2 * ⟪dx i, x i⟫
  := by fun_trans

example 
  : ∇ (λ (x : Fin n → ℝ) => ∑ i, ‖ x i ‖²)
    =
    λ x i => 2 * x i
  := by 
    conv => lhs; unfold gradient; fun_trans; fun_trans

def _root_.Fin.shift (x : Fin n) (y : Int) : Fin n := ⟨((x.1 + y) % n).toNat, sorry⟩

function_properties Fin.shift {n} [Nonempty (Fin n)] (x : Fin n) (y : Int)
argument x
  IsInv := sorry_proof,
  abbrev ⁻¹ := λ x' => x'.shift (-y) by sorry_proof

example [Nonempty (Fin n)]
  : ∂† (λ (x : Fin n → ℝ) i => ‖ x (i.shift 1) - x i‖²)
    =
    λ g dg' i =>
      2 * dg' (Fin.shift i (-1)) * (g i - g (Fin.shift i (-1))) 
      + 
      -(2 * dg' i * (g (Fin.shift i 1) - g i))
  :=
by
  conv => lhs; fun_trans
  done

example [Nonempty (Fin n)]
  : ∇ (λ (x : Fin n → ℝ) => ∑ i, ‖ x (i.shift 1) - x i‖²)
    =
    λ x i => 2 * (x i - x (Fin.shift i (-1))) + -(2 * (x (Fin.shift i 1) - x i))
  :=
by
  unfold gradient
  conv => lhs; fun_trans; simp


example [Nonempty (Fin n)]
  : ∇ (λ (x : Fin n → ℝ) => ∑ i, ‖ x (i.shift 1) - x i‖²)
    =
    λ x i => 2 * (x i - x (Fin.shift i (-1))) + -(2 * (x (Fin.shift i 1) - x i))
  :=
by
  unfold gradient
  conv => lhs; fun_trans; simp

