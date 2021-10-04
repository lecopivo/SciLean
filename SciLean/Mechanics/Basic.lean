import SciLean.Prelude

def symp {V} [Vec V] : V×V → V×V := uncurry $ λ q p => (p, -q)
def HamiltonianSystem {V} [Hilbert V] (H : V → V → ℝ) : V×V → V×V := comp symp ∇(uncurry H)
