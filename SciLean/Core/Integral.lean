-- import SciLean.Core.CoreFunctionProperties
import SciLean.Core.AdjDiff
import SciLean.Core.FinVec

namespace SciLean


opaque LocIntDom (X : Type) [Vec X] : Type

--------------------------------------------------------------------------------
-- Integral
--------------------------------------------------------------------------------


-- If `f` is integrable on `Ω` return integral otherwise return zero
-- IMPORTANT: We choose to integrate only over **bounded** domains.
--            This way the function `λ (f : X⟿Y) => ∫ x, f x` can be linear.
-- QUESTION: Do we need Y to be complete? For example smooth function
--   with compact support do not form closed subspace in `ℝ ⟿ ℝ`. 
--   Can we have `γ : ℝ ⟿ {f : ℝ ⟿ ℝ // TestFun f}` such that 
--   `∫ t ∈ [0,1], γ.1` is not a `TestFun`?
noncomputable
opaque integral {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Vec Y] (f : X ⟿ Y) (Ω : LocIntDom X) : Y 

noncomputable
opaque limitOverWholeDomain {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Vec Y] (F : LocIntDom X → Y) : Y

instance integral.instNotationIntegral 
  {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Vec Y] (f : X ⟿ Y) 
  : Integral f (integral f) := ⟨⟩

syntax intBinderType  := ":" term
syntax intBinder := ident (intBinderType)?
syntax "∫" intBinder "," term:66 : term
syntax "∫" "(" intBinder ")" "," term:66 : term
macro_rules
| `(∫ $x:ident, $f) =>
  `(∫ (SmoothMap.mk' λ $x => $f))
| `(∫ $x:ident : $type:term, $f) =>
  `(∫ (SmoothMap.mk' λ ($x : $type) => $f))
| `(∫ ($x:ident : $type:term), $f) =>
  `(∫ $x:ident : $type:term, $f)


--------------------------------------------------------------------------------
-- SemiHilbert structure on spaces like `ℝ^{n}⟿ℝ`
--------------------------------------------------------------------------------

variable {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Hilbert Y]

noncomputable
instance : Inner (X⟿Y) where
  inner f g := (integral ⟨λ x => ⟪f x, g x⟫, sorry_proof⟩) |> limitOverWholeDomain

instance : TestFunctions (X⟿Y) where
  TestFun f := sorry -- has compact support

noncomputable
instance : SemiHilbert (X⟿Y) := SemiHilbert.mkSorryProofs


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


