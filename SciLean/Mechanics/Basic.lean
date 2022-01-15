import SciLean.Operators

open Function
namespace SciLean

noncomputable
def HamiltonianSystem {V} [Hilbert V] (H : V → V → ℝ) : V×V → V×V := 
  uncurry $
  λ x p : V =>
    let dHdx := ∇(λ x => H x p) x
    let dHdp := ∇(H x) p
    (dHdp, -dHdx)

-- def LagrangianSystem {V} [Vec V] (L : V → V → ℝ) : V×V → V×V :=
--   uncurry $ 
--   λ x v : V => 
--     let inverse_mass_matrix : V → V := (δ(∇(L x)) v)⁻¹
--     let potential_force : V := ∇(swap L v) x
--     let geometry_force : V := - ∇(δ L x v) v
--     (v, inverse_mass_matrix (potential_force + geometry_force))

-- def LagrangianToHamiltonian {V} [Hilbert V] (L : V → V → ℝ) : V → V → ℝ := 
--     λ x p : V => 
--       let v := (∇ (L x))⁻¹ p
--       ⟨p, v⟩ - L x v

-- def HamiltonianToLagrangian {V} [Hilbert V] (H : V → V → ℝ) : V → V → ℝ := 
--   λ x v : V => 
--     let p := (∇ (H x))⁻¹ v
--     ⟨p, v⟩ - H x p

