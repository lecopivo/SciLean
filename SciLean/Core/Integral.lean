-- import SciLean.Core.CoreFunctionProperties
-- import SciLean.Core.AdjDiff
import SciLean.Core.FinVec
import SciLean.Core.SmoothMap

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
opaque integral {X Y ι : Type} [EnumType ι] [FinVec X ι] [Vec Y] (f : X ⟿ Y) (Ω : LocIntDom X) : Y 

noncomputable
opaque limitOverWholeDomain {X Y ι : Type} [EnumType ι] [FinVec X ι] [Vec Y] (F : LocIntDom X → Y) : Y

instance integral.instNotationIntegral 
  {X Y ι : Type} [EnumType ι] [FinVec X ι] [Vec Y] (f : X ⟿ Y) 
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

variable {X Y ι : Type} [EnumType ι] [FinVec X ι] [Hilbert Y]

noncomputable
instance : Inner (X⟿Y) where
  inner f g := (integral (SmoothMap.mk (λ x => ⟪f x, g x⟫) sorry)) |> limitOverWholeDomain

instance : TestFunctions (X⟿Y) where
  TestFun f := sorry -- has compact support

noncomputable
instance : SemiHilbert (X⟿Y) := SemiHilbert.mkSorryProofs
