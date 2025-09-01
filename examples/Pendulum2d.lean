import SciLean
-- import SciLean.Mechanics

-- import Lean.Meta.Tactic

set_option synthInstance.maxHeartbeats 5000000
set_option synthInstance.maxSize 2048

open SciLean


def ε : ℝ := 0.001
instance : Fact (ε≠0) := Fact.mk (by native_decide)

abbrev parm (l : ℝ) (Ω : ℝ) : ℝ^(2:ℕ) :=
  let e : ℝ^(2:ℕ) := ⟨0,-1⟩
  rotate2d Ω (l * e)

def g : ℝ := 9.81

def L (m : ℝ) (l : ℝ) (Ω ω : ℝ) : ℝ := 
  let e : ℝ^(2:ℕ) := ⟨0,-1⟩
  let x := parm l Ω
  let v := δ (λ t : ℝ => parm l (Ω + t * ω)) 0 1
    rewrite_by (simp[parm])
  m/2 * ∥v∥² - m * g * x.y
argument Ω
  isSmooth, diff, hasAdjDiff, adjDiff
argument ω
  isSmooth, diff, hasAdjDiff, adjDiff

def momentum (m : ℝ) (l : ℝ) (Ω ω : ℝ) : ℝ :=
  (δ† (λ ω' => L m l Ω ω') ω 1)
  rewrite_by
    simp

instance : ∀ {X} [Vec X] (x : X), Fact (x≠0) := sorry

-- set_option trace.Meta.Tactic.simp.discharge true in
def velocity (m : ℝ) (l : ℝ) (Ω ω' : ℝ) : ℝ := 
  ((λ ω => momentum m l Ω ω)⁻¹ ω')
  rewrite_by
    simp[momentum]
    simp[L.arg_ω.adjDiff]
    simp only [!?(∀ {X} [Hilbert X] (x y : X) (a : ℝ), ⟪a * x, y⟫ = a * ⟪x,y⟫)]
    simp only [!?(∀ (x y : ℝ^(2:ℕ)) (θ : ℝ), ⟪rotate2d θ x, rotate2d θ y⟫ = ⟪x,y⟫)]
    simp only [!?(∀ {X} [Hilbert X] (x y : X) (a : ℝ), ⟪a * x, a * y⟫ = a * a * ⟪x,y⟫)]
    simp only [!?(∀ {X} [Hilbert X] (x  : X), ⟪x,x⟫ = ∥x∥²)]
    simp; unfold hold; simp

