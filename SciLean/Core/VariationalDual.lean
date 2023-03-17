-- import SciLean.Core.CoreFunctionProperties
import SciLean.Core.AdjDiff

namespace SciLean

--------------------------------------------------------------------------------
-- Variational Dual
--------------------------------------------------------------------------------

-- variational version of †
noncomputable
def variationalDual (F : (X⟿Y) → (LocIntDom X → ℝ)) : (X⟿Y) :=
  let has_dual := ∃ A : (X⟿Y) → (X⟿ℝ), HasAdjointT A ∧ ∀ ϕ, F ϕ = ∫ (A ϕ)
  match Classical.propDecidable (has_dual) with
  | isTrue h => 
    let A := Classical.choose h
    A† (λ _ ⟿ 1)
  | isFalse _ => 0

instance (F : (X⟿Y) → (LocIntDom X → ℝ)) 
  : Dagger F (variationalDual F) := ⟨⟩

-- variational version of ∇ 
noncomputable
def variationalGradient (F : (X⟿Y) → LocIntDom X → ℝ) (f : X⟿Y) : X ⟿ Y := (∂ F f)†

instance (F : (X⟿Y) → LocIntDom X → ℝ) : Nabla F (variationalGradient F) := ⟨⟩


-- Properties

instance integral.arg_f.isLin : IsLin (integral : (X⟿Y) → LocIntDom X → Y) := sorry_proof

-- @[simp ↓ low, diff low]
-- theorem variationalGradient_unfold (F : (X⟿Y) → LocIntDom X → ℝ)
--   : ∇ F = λ f => (∂ F f)† := by rfl

@[simp ↓, diff]
theorem varDual_smooth_fun (F : (X⟿Y) → (X⟿ℝ)) [HasAdjointT F]
  : (λ (f : X ⟿ Y) => ∫ (F f))† = F† (λ _ ⟿ 1) := sorry_proof


@[simp ↓, diff]
theorem variationalGradient_on_integral (F : (X⟿Y) → (X⟿ℝ)) [inst : HasAdjDiffT F]
  : ∇ f, ∫ (F f) = λ f => ∂† F f (λ _ ⟿ 1) := 
by 
  have _ := inst.1.1
  have _ := inst.1.2
  unfold variationalGradient
  unfold adjointDifferential
  symdiff
  symdiff
  done


@[simp ↓, diff]
theorem varDual_smooth_fun_elemwise [Hilbert Y] (A : X → Y → ℝ) [∀ x, HasAdjointT (A x)] [IsSmoothNT 2 A]
  : (λ (g : X ⟿ Y) => ∫ x, A x (g x))† = (λ x ⟿ (A x)† 1) := sorry_proof

@[simp ↓, diff]
theorem varDual_smooth_fun_elemwise' [Hilbert Y] [Vec Z] (f : X → Z) [IsSmoothT f] 
  (A : Y → Z → ℝ) [∀ z, HasAdjointT (λ y => A y z)] [IsSmoothNT 2 A]
  : (λ (g : X ⟿ Y) => ∫ x, A (g x) (f x))† = (λ x ⟿ (λ y => A y (f x))† 1) := 
by apply varDual_smooth_fun_elemwise (λ x y => A y (f x)); done


