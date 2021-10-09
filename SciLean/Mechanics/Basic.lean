import SciLean.Prelude

def symp {V} [Vec V] : V×V → V×V := uncurry $ λ q p => (p, -q)
def HamiltonianSystem {V} [Hilbert V] (H : V → V → ℝ) : V×V → V×V := comp symp ∇(uncurry H)

def LagrangianSystem {V} [Hilbert V] (L : V → V → ℝ) : V×V → V×V :=
  uncurry $ λ x v : V => (v, (δ(∇(L x)) v)⁻¹ (∇(swap L v) x - ∇(δ L x v) v))

def LagrangianToHamiltonian {V} [Hilbert V] (L : V → V → ℝ) : V → V → ℝ := 
    λ x p : V => 
           let v := (∇ (L x))⁻¹ p
           ⟨p, v⟩ - L x v

