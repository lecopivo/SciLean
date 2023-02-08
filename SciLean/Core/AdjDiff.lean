import Lean
import Init.Classical

import SciLean.Core.Differential
import SciLean.Core.Adjoint
import SciLean.Core.HasAdjDiff

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] 
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι : Type} [Enumtype ι]


noncomputable 
def adjointDifferential (f : X → Y) (x : X) (dy' : Y) : X := (∂ f x)† dy'

@[default_instance]
instance (f : X → Y) : PartialDagger f (adjointDifferential f) := ⟨⟩


noncomputable
abbrev gradient (f : X → ℝ) (x : X) : X := ∂† f x 1

@[default_instance]
instance (f : X → ℝ) : Nabla f (gradient f) := ⟨⟩


-- Notation 
-- ∇ s, f s         --> ∇ λ s => f s
-- ∇ s : ℝ, f s     --> ∇ λ s : ℝ => f s
-- ∇ s := t, f s    --> (∇ λ s => f s) t
syntax "∇" diffBinder "," term:66 : term
syntax "∇" "(" diffBinder ")" "," term:66 : term
macro_rules 
| `(∇ $x:ident, $f) =>
  `(∇ λ $x => $f)
| `(∇ $x:ident : $type:term, $f) =>
  `(∇ λ $x : $type => $f)
| `(∇ $x:ident := $val:term, $f) =>
  `((∇ λ $x => $f) $val)
| `(∇ ($b:diffBinder), $f) =>
  `(∇ $b, $f)


instance (f : X → Y) [HasAdjDiff f] (x : X) : IsLin (∂† f x) := sorry

----------------------------------------------------------------------


@[simp ↓, autodiff]
theorem id.arg_x.adjDiff_simp
  : ∂† (λ x : X => x) = λ x dx => dx := by simp[adjointDifferential]; done

@[simp ↓, autodiff]
theorem const.arg_x.adjDiff_simp 
  : ∂† (λ (x : X) (i : ι) => x) = λ x f => ∑ i, f i := by simp[adjointDifferential]; done

@[simp ↓, autodiff]
theorem const.arg_y.adjDiff_simp (x : X)
  : ∂† (λ (y : Y) => x) = (λ y dy' => (0 : Y)) := by simp[adjointDifferential]; done

@[simp ↓ low-4, autodiff low-4]
theorem swap.arg_y.adjDiff_simp
  (f : ι → X → Z) [inst : ∀ i, HasAdjDiffT (f i)]
  : ∂† (λ x y => f y x) = (λ x dx' => ∑ i, (∂† (f i) x) (dx' i)) := 
by 
  have := λ i => (inst i).proof.1
  have := λ i => (inst i).proof.2

  simp[adjointDifferential]; done

@[simp ↓ low-3, autodiff low-3]
theorem subst.arg_x.adjDiff_simp
  (f : X → Y → Z) [instf : HasAdjDiffNT 2 f]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f x (g x)) 
    = 
    λ x dx' => 
      (∂† (hold λ x' => f x' (g x))) x dx'
      +
      (∂† g x) (∂† (f x) (g x) dx')
    := 
by 
  have := instg.proof.1
  have := instg.proof.2
  have := instf.proof.1

  funext x dx';
  -- have adjAdd : ∀ {X} [SemiHilbert X], HasAdjoint fun yy : X×X => yy.fst + yy.snd := sorry
  simp[adjointDifferential, tangentMap] --- bla bla bla
  admit


@[simp ↓ low-2, autodiff low-2]
theorem subst.arg_x.parm1.adjDiff_simp
  (a : α)
  (f : X → Y → α → Z) [HasAdjDiffNT 2 λ x y => f x y a]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f x (g x) a) 
    = 
    λ x dx' => 
      (∂† (hold λ x' => f x' (g x) a)) x dx'
      +
      (∂† g x) (∂† (hold λ y => f x y a) (g x) dx')
    := 
by 
  apply subst.arg_x.adjDiff_simp (λ x y => f x y a) g
  done

@[simp ↓ low-2, autodiff low-2]
theorem subst.arg_x.parm2.adjDiff_simp
  (a : α) (b : β)
  (f : X → Y → α → β → Z) [HasAdjDiffNT 2 λ x y => f x y a b]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f x (g x) a b) 
    = 
    λ x dx' => 
      (∂† (hold λ x' => f x' (g x) a b)) x dx'
      +
      (∂† g x) (∂† (hold λ y => f x y a b) (g x) dx')
    := 
by 
  apply subst.arg_x.adjDiff_simp (λ x y => f x y a b) g
  done

@[simp ↓ low-2, autodiff low-2]
theorem subst.arg_x.parm3.adjDiff_simp
  (a : α) (b : β) (c : γ)
  (f : X → Y → α → β → γ → Z) [HasAdjDiffNT 2 λ x y => f x y a b c]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f x (g x) a b c) 
    = 
    λ x dx' => 
      (∂† (hold λ x' => f x' (g x) a b c)) x dx'
      +
      (∂† g x) (∂† (hold λ y => f x y a b c) (g x) dx')
    := 
by 
  apply subst.arg_x.adjDiff_simp (λ x y => f x y a b c) g
  done

@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.adjDiff_simp
  (f : Y → Z) [instf : HasAdjDiffT f]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f (g x)) = λ x dx' => (∂† g x) ((∂† f (g x)) dx') := 
by 
  simp; unfold hold; simp
  done

@[simp ↓ low-2, autodiff low-2]
theorem diag.arg_x.adjDiff_simp
  (f : Y₁ → Y₂ → Z) [HasAdjDiffNT 2 f]
  (g₁ : X → Y₁) [hg : HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx' => 
      (∂† g₁ x) ((∂† λ y₁ => f y₁ (g₂ x)) (g₁ x) dx')
      +
      (∂† g₂ x) ((∂† λ y₂ => f (g₁ x) y₂) (g₂ x) dx')
    := 
by
  simp; unfold hold; simp; unfold hold; simp; done

@[simp ↓ low, autodiff low]
theorem eval.arg_f.adjDiff_simp
  (i : ι)
  : ∂† (λ (f : ι → X) => f i) = (λ f df' j => ([[i = j]] * df' : X))
:= sorry

@[simp ↓ low-1, autodiff low-1]
theorem eval.arg_x.parm1.adjDiff_simp
  (f : X → ι → Z) [HasAdjDiff f]
  : ∂† (λ x => f x i) = (λ x dx' => (∂† f x) (λ j => ([[i = j]] * dx' : Z)))
:= 
by 
  rw [comp.arg_x.adjDiff_simp (λ (x : ι → Z) => x i) f]
  simp


--------------------------------------------------------
-- These theorems are problematic when used with simp --


@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.parm1.adjDiff_simp
  (a : α) 
  (f : Y → α → Z) [HasAdjDiff λ y => f y a]
  (g : X → Y) [HasAdjDiff g]
  : 
    ∂† (λ x => f (g x) a) = λ x dx' => (∂† g x) ((∂† (hold λ y => f y a)) (g x) dx')
:= by 
  simp; unfold hold; simp
  done

@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.parm2.adjDiff_simp
  (a : α) (b : β)
  (f : Y → α → β → Z) [HasAdjDiff λ y => f y a b]
  (g : X → Y) [HasAdjDiff g]
  : 
    ∂† (λ x => f (g x) a b) = λ x dx' => (∂† g x) ((∂† (hold λ y => f y a b)) (g x) dx')
:= by 
  simp; unfold hold; simp
  done

@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.parm3.adjDiff_simp
  (a : α) (b : β) (c : γ)
  (f : Y → α → β → γ → Z) [HasAdjDiff λ y => f y a b c]
  (g : X → Y) [HasAdjDiff g]
  : 
    ∂† (λ x => f (g x) a b c) = λ x dx' => (∂† g x) ((∂† (hold λ y => f y a b c)) (g x) dx')
:= by 
  simp; unfold hold; simp
  done

example (a : α) (f : Y₁ → Y₂ → α → Z) [IsSmooth λ y₁ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [hg : IsSmooth g₁] : IsSmooth (λ x y => f (g₁ x) y a) := by infer_instance


@[simp ↓ low-1, autodiff low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm1.adjDiff_simp
  (a : α)
  (f : Y₁ → Y₂ → α → Z) [HasAdjDiffNT 2 λ y₁ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x) a)
    = 
    λ x dx' => 
      (∂† g₁ x) ((∂† (hold λ y₁ => f y₁ (g₂ x) a)) (g₁ x) dx')
      +
      (∂† g₂ x) ((∂† (hold λ y₂ => f (g₁ x) y₂ a)) (g₂ x) dx')
:= by 
  (apply diag.arg_x.adjDiff_simp (λ y₁ y₂ => f y₁ y₂ a) g₁ g₂)
  
@[simp ↓ low-1, autodiff low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm2.adjDiff_simp
  (a : α) (b : β)
  (f : Y₁ → Y₂ → α → β → Z) [HasAdjDiffNT 2 λ y₁ y₂ => f y₁ y₂ a b]
  (g₁ : X → Y₁) [HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x) a b)
    = 
    λ x dx' => 
      (∂† g₁ x) ((∂† (hold λ y₁ => f y₁ (g₂ x) a b)) (g₁ x) dx')
      +
      (∂† g₂ x) ((∂† (hold λ y₂ => f (g₁ x) y₂ a b)) (g₂ x) dx')
:= by 
  (apply diag.arg_x.adjDiff_simp (λ y₁ y₂ => f y₁ y₂ a b) g₁ g₂)
  done

@[simp ↓ low-1, autodiff low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm3.adjDiff_simp
  (a : α) (b : β) (c : γ)
  (f : Y₁ → Y₂ → α → β → γ → Z) [HasAdjDiffNT 2 λ y₁ y₂ => f y₁ y₂ a b c]
  (g₁ : X → Y₁) [HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x) a b c)
    = 
    λ x dx' => 
      (∂† g₁ x) ((∂† (hold λ y₁ => f y₁ (g₂ x) a b c)) (g₁ x) dx')
      +
      (∂† g₂ x) ((∂† (hold λ y₂ => f (g₁ x) y₂ a b c)) (g₂ x) dx')
:= by 
  (apply diag.arg_x.adjDiff_simp (λ y₁ y₂ => f y₁ y₂ a b c) g₁ g₂)
  done

----------------------------------------------------------------------


-- @[simp ↓]
-- theorem subst.arg_x.adjDiff_simp'''
--   (f : X → Y → Z) [IsSmooth f]
--   [instfx : ∀ y, HasAdjDiff λ x => f x y]
--   [instfy : ∀ x, HasAdjDiff (f x)]
--   (g : Y → X) [instg : HasAdjDiff g]
--   : ∂† (λ y => f (g y) y) 
--     = 
--     λ y dy' => 
--       (∂† (λ y' => f (g y) y')) y dy'
--       +
--       (∂† g y) (∂† (λ x => f x y) (g y) dy')
--     := 
-- by 
--   sorry




