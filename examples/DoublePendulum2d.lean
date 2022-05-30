import SciLean
-- import SciLean.Mechanics

-- import Lean.Meta.Tactic

set_option synthInstance.maxHeartbeats 5000000
set_option synthInstance.maxSize 2048

open SciLean


def ε : ℝ := 0.001
instance : Fact (ε≠0) := Fact.mk (by native_decide)

@[simp]
theorem pair_add {X Y} [Add X] [Add Y] (x x' : X) (y y' : Y) : (x, y) + (x', y') = (x + x', y + y') := by simp[HAdd.hAdd, Add.add] done

@[simp]
theorem inner_zero  {X} [Hilbert X] (x : X) : ⟪0,x⟫ = 0 := sorry
@[simp]
theorem zero_inner  {X} [Hilbert X] (x : X) : ⟪x,0⟫ = 0 := sorry


def parm (l₁ l₂ : ℝ) (Ω : ℝ×ℝ) : (ℝ^(2:ℕ)) × (ℝ^(2:ℕ)) :=
  let e : ℝ^(2:ℕ) := ⟨0,-1⟩
  let Δx₁ := rotate2d Ω.1 (l₁ * e)
  let Δx₂ := rotate2d Ω.2 (l₂ * e)
  (Δx₁, Δx₁ + Δx₂)
argument Ω
  isSmooth, diff, hasAdjDiff, adjDiff?

set_option trace.Meta.Tactic.simp true

function_properties parm.arg_Ω.diff (l₁ l₂ : ℝ) (Ω dΩ : ℝ×ℝ) : (ℝ^(2:ℕ)) × (ℝ^(2:ℕ))
-- argument Ω
--   isSmooth, diff, hasAdjDiff, adjDiff
argument dΩ
  -- -- isLin := by simp[diff]; infer_instance; done,
  -- isSmooth, 
  -- diff  --_simp := parm.arg_Ω.diff l₁ l₂ Ω ddΩ by simp[diff] done, 
  -- hasAdjDiff,
  adjDiff -- := parm.arg_Ω.adjDiff l₁ l₂ Ω ddΩ' by simp[adjDiff,diff]; unfold hold;   imp done

def g : ℝ := 9.81

-- instance (priority := high) {X Y} [Vec X] [Vec Y] (f : X → Y) : IsSmooth f := sorry
-- instance (priority := high) {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : HasAdjDiff f := sorry

/-
def L (m₁ m₂ : ℝ) (l₁ l₂ : ℝ) (Ω ω : ℝ×ℝ) : ℝ := 
  let e : ℝ^(2:ℕ) := ⟨0,-1⟩
  let x := parm l₁ l₂ Ω
  let v := δ (λ t : ℝ => parm l₁ l₂ (Ω + t * ω)) 0 1
    rewrite_by (simp)
  m₁/2 * ∥v.1∥² - m₁ * g * x.1.y + 
  m₂/2 * ∥v.2∥² - m₂ * g * x.2.y
argument Ω
  isSmooth, diff, hasAdjDiff, adjDiff
argument ω
  isSmooth, diff, hasAdjDiff, adjDiff

def momentum (m₁ m₂ : ℝ) (l₁ l₂ : ℝ) (Ω ω : ℝ×ℝ) : ℝ×ℝ :=
  (δ† (λ ω' => L m₁ m₂ l₁ l₂ Ω ω') ω 1)
  rewrite_by
    simp

#print L.arg_Ω.diff


instance : ∀ {X} [Vec X] (x : X), Fact (x≠0) := sorry


set_option trace.Meta.Tactic.simp.discharge true in
def velocity (m₁ m₂ : ℝ) (l₁ l₂ : ℝ) (Ω ω' : ℝ×ℝ) : ℝ×ℝ := 
  ((λ ω => momentum m₁ m₂ l₁ l₂ Ω ω)⁻¹ ω')
  rewrite_by
    simp[momentum]
    simp[L.arg_ω.adjDiff]
    simp only [!?(∀ {X} [Hilbert X] (x y : X) (a : ℝ), ⟪a * x, y⟫ = a * ⟪x,y⟫)]
    simp only [!?(∀ (x y : ℝ^(2:ℕ)) (θ : ℝ), ⟪rotate2d θ x, rotate2d θ y⟫ = ⟪x,y⟫)]
    simp only [!?(∀ {X} [Hilbert X] (x y : X) (a : ℝ), ⟪a * x, a * y⟫ = a * a * ⟪x,y⟫)]
    simp only [!?(∀ {X} [Hilbert X] (x  : X), ⟪x,x⟫ = ∥x∥²)]
    simp; unfold hold; simp

-/
