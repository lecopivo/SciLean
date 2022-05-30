import SciLean.Core.Fun.Diff
import SciLean.Core.Fun.Adjoint
import SciLean.Core.Mor.HasAdjDiff

namespace SciLean


variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] 
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι : Type} [Enumtype ι]


noncomputable 
def adjDiff
  (f : X → Y) (x : X) : Y → X := (δ f x)†

prefix:max "δ†" => adjDiff
macro:max "∇" f:term:max : term => `(λ x => δ† $f x (1:ℝ))

instance (f : X → Y) [HasAdjDiff f] (x : X) : IsLin (δ† f x) := sorry

----------------------------------------------------------------------


@[simp ↓]
theorem id.arg_x.adjDiff_simp
  : δ† (λ x : X => x) = λ x dx => dx := by simp[adjDiff] done

@[simp ↓]
theorem const.arg_x.adjDiff_simp 
  : δ† (λ (x : X) (i : ι) => x) = λ x f => ∑ i, f i := by simp[adjDiff] done

@[simp ↓]
theorem const.arg_y.adjDiff_simp (x : X)
  : δ† (λ (y : Y) => x) = (λ y dy' => (0 : Y)) := by simp[adjDiff] done

@[simp ↓ low-4]
theorem swap.arg_y.adjDiff_simp
  (f : ι → X → Z) [inst : ∀ i, HasAdjDiff (f i)]
  : δ† (λ x y => f y x) = (λ x dx' => ∑ i, (δ† (f i) x) (dx' i)) := 
by 
  have isf := λ i => (inst i).isSmooth
  have iaf := λ i => (inst i).hasAdjDiff

  simp[adjDiff] done

@[simp ↓ low-3]
theorem subst.arg_x.adjDiff_simp
  (f : X → Y → Z) [IsSmooth f]
  [instfx : ∀ y, HasAdjDiff λ x => f x y]
  [instfy : ∀ x, HasAdjDiff (f x)]
  (g : X → Y) [instg : HasAdjDiff g]
  : δ† (λ x => f x (g x)) 
    = 
    λ x dx' => 
      (δ† (hold λ x' => f x' (g x))) x dx'
      +
      (δ† g x) (δ† (f x) (g x) dx')
    := 
by 
  have isfx := λ y => (instfx y).isSmooth
  have iafx := λ y => (instfx y).hasAdjDiff
  have isfy := λ x => (instfy x).isSmooth
  have iafy := λ x => (instfy x).hasAdjDiff
  have isg := instg.isSmooth
  have iag := instg.hasAdjDiff

  simp at iafx
  simp at iafy

  funext x dx';
  -- have adjAdd : ∀ {X} [SemiHilbert X], HasAdjoint fun yy : X×X => yy.fst + yy.snd := sorry
  simp[adjDiff] --- bla bla bla
  admit


@[simp ↓ low-2]
theorem subst.arg_x.parm1.adjDiff_simp
  (a : α)
  (f : X → Y → α → Z) [IsSmooth λ x y => f x y a]
  [instfx : ∀ y, HasAdjDiff λ x => f x y a]
  [instfy : ∀ x, HasAdjDiff λ y => f x y a]
  (g : X → Y) [instg : HasAdjDiff g]
  : δ† (λ x => f x (g x) a) 
    = 
    λ x dx' => 
      (δ† (hold λ x' => f x' (g x) a)) x dx'
      +
      (δ† g x) (δ† (hold λ y => f x y a) (g x) dx')
    := 
by 
  apply subst.arg_x.adjDiff_simp (λ x y => f x y a) g
  done

@[simp ↓ low-2]
theorem subst.arg_x.parm2.adjDiff_simp
  (a : α) (b : β)
  (f : X → Y → α → β → Z) [IsSmooth λ x y => f x y a b]
  [instfx : ∀ y, HasAdjDiff λ x => f x y a b]
  [instfy : ∀ x, HasAdjDiff λ y => f x y a b]
  (g : X → Y) [instg : HasAdjDiff g]
  : δ† (λ x => f x (g x) a b) 
    = 
    λ x dx' => 
      (δ† (hold λ x' => f x' (g x) a b)) x dx'
      +
      (δ† g x) (δ† (hold λ y => f x y a b) (g x) dx')
    := 
by 
  apply subst.arg_x.adjDiff_simp (λ x y => f x y a b) g
  done

@[simp ↓ low-2]
theorem subst.arg_x.parm3.adjDiff_simp
  (a : α) (b : β) (c : γ)
  (f : X → Y → α → β → γ → Z) [IsSmooth λ x y => f x y a b c]
  [instfx : ∀ y, HasAdjDiff λ x => f x y a b c]
  [instfy : ∀ x, HasAdjDiff λ y => f x y a b c]
  (g : X → Y) [instg : HasAdjDiff g]
  : δ† (λ x => f x (g x) a b c) 
    = 
    λ x dx' => 
      (δ† (hold λ x' => f x' (g x) a b c)) x dx'
      +
      (δ† g x) (δ† (hold λ y => f x y a b c) (g x) dx')
    := 
by 
  apply subst.arg_x.adjDiff_simp (λ x y => f x y a b c) g
  done

@[simp ↓ low-1]
theorem comp.arg_x.adjDiff_simp
  (f : Y → Z) [instf : HasAdjDiff f] --[IsSmooth f] [∀ y, HasAdjoint $ δ f y] 
  (g : X → Y) [instg : HasAdjDiff g] -- [IsSmooth g] [∀ x, HasAdjoint $ δ g x] 
  : δ† (λ x => f (g x)) = λ x dx' => (δ† g x) ((δ† f (g x)) dx') := 
by 
  simp; unfold hold; simp
  done

@[simp ↓ low-2]
theorem diag.arg_x.adjDiff_simp
  (f : Y₁ → Y₂ → Z) [IsSmooth f]
  [∀ y₂, HasAdjDiff λ y₁ => f y₁ y₂]
  [∀ y₁, HasAdjDiff λ y₂ => f y₁ y₂]
  (g₁ : X → Y₁) [hg : HasAdjDiff g₁]
  (g₂ : X → Y₂) [HasAdjDiff g₂]
  : δ† (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx' => 
      (δ† g₁ x) ((δ† λ y₁ => f y₁ (g₂ x)) (g₁ x) dx')
      +
      (δ† g₂ x) ((δ† λ y₂ => f (g₁ x) y₂) (g₂ x) dx')
    := 
by 
  have sg := hg.1
  simp; unfold hold; simp; unfold hold; simp; done

@[simp ↓ low]
theorem eval.arg_f.adjDiff_simp
  (i : ι)
  : δ† (λ (f : ι → X) => f i) = (λ f df' j => ((kron i j) * df' : X))
:= sorry

@[simp ↓ low-1]
theorem eval.arg_x.parm1.adjDiff_simp
  (f : X → ι → Z) [HasAdjDiff f]
  : δ† (λ x => f x i) = (λ x dx' => (δ† f x) (λ j => ((kron i j) * dx' : Z)))
:= 
by 
  rw [comp.arg_x.adjDiff_simp (λ (x : ι → Z) => x i) f]
  simp


--------------------------------------------------------
-- These theorems are problematic when used with simp --


@[simp ↓ low-1]
theorem comp.arg_x.parm1.adjDiff_simp
  (a : α) 
  (f : Y → α → Z) [HasAdjDiff λ y => f y a]
  (g : X → Y) [HasAdjDiff g]
  : 
    δ† (λ x => f (g x) a) = λ x dx' => (δ† g x) ((δ† (hold λ y => f y a)) (g x) dx')
:= by 
  simp; unfold hold; simp
  done

@[simp ↓ low-1]
theorem comp.arg_x.parm2.adjDiff_simp
  (a : α) (b : β)
  (f : Y → α → β → Z) [HasAdjDiff λ y => f y a b]
  (g : X → Y) [HasAdjDiff g]
  : 
    δ† (λ x => f (g x) a b) = λ x dx' => (δ† g x) ((δ† (hold λ y => f y a b)) (g x) dx')
:= by 
  simp; unfold hold; simp
  done

@[simp ↓ low-1]
theorem comp.arg_x.parm3.adjDiff_simp
  (a : α) (b : β) (c : γ)
  (f : Y → α → β → γ → Z) [HasAdjDiff λ y => f y a b c]
  (g : X → Y) [HasAdjDiff g]
  : 
    δ† (λ x => f (g x) a b c) = λ x dx' => (δ† g x) ((δ† (hold λ y => f y a b c)) (g x) dx')
:= by 
  simp; unfold hold; simp
  done

example (a : α) (f : Y₁ → Y₂ → α → Z) [IsSmooth λ y₁ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [hg : IsSmooth g₁] : IsSmooth (λ x y => f (g₁ x) y a) := by infer_instance


@[simp ↓ low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm1.adjDiff_simp
  (a : α)
  (f : Y₁ → Y₂ → α → Z) [IsSmooth λ y₁ y₂ => f y₁ y₂ a]
  [∀ y₂, HasAdjDiff λ y₁ => f y₁ y₂ a]
  [∀ y₁, HasAdjDiff λ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [hg : HasAdjDiff g₁]
  (g₂ : X → Y₂) [HasAdjDiff g₂]
  : δ† (λ x => f (g₁ x) (g₂ x) a)
    = 
    λ x dx' => 
      (δ† g₁ x) ((δ† (hold λ y₁ => f y₁ (g₂ x) a)) (g₁ x) dx')
      +
      (δ† g₂ x) ((δ† (hold λ y₂ => f (g₁ x) y₂ a)) (g₂ x) dx')
:= by 
  have sg := hg.1

  admit
  
@[simp ↓ low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm2.adjDiff_simp
  (a : α) (b : β)
  (f : Y₁ → Y₂ → α → β → Z) [IsSmooth λ y₁ y₂ => f y₁ y₂ a b]
  [∀ y₂, HasAdjDiff λ y₁ => f y₁ y₂ a b]
  [∀ y₁, HasAdjDiff λ y₂ => f y₁ y₂ a b]
  (g₁ : X → Y₁) [HasAdjDiff g₁]
  (g₂ : X → Y₂) [HasAdjDiff g₂]
  : δ† (λ x => f (g₁ x) (g₂ x) a b)
    = 
    λ x dx' => 
      (δ† g₁ x) ((δ† (hold λ y₁ => f y₁ (g₂ x) a b)) (g₁ x) dx')
      +
      (δ† g₂ x) ((δ† (hold λ y₂ => f (g₁ x) y₂ a b)) (g₂ x) dx')
:= by 
  (apply diag.arg_x.adjDiff_simp (λ y₁ y₂ => f y₁ y₂ a b) g₁ g₂)
  done

@[simp ↓ low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm3.adjDiff_simp
  (a : α) (b : β) (c : γ)
  (f : Y₁ → Y₂ → α → β → γ → Z) [IsSmooth λ y₁ y₂ => f y₁ y₂ a b c]
  [∀ y₂, HasAdjDiff λ y₁ => f y₁ y₂ a b c]
  [∀ y₁, HasAdjDiff λ y₂ => f y₁ y₂ a b c]
  (g₁ : X → Y₁) [HasAdjDiff g₁]
  (g₂ : X → Y₂) [HasAdjDiff g₂]
  : δ† (λ x => f (g₁ x) (g₂ x) a b c)
    = 
    λ x dx' => 
      (δ† g₁ x) ((δ† (hold λ y₁ => f y₁ (g₂ x) a b c)) (g₁ x) dx')
      +
      (δ† g₂ x) ((δ† (hold λ y₂ => f (g₁ x) y₂ a b c)) (g₂ x) dx')
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
--   : δ† (λ y => f (g y) y) 
--     = 
--     λ y dy' => 
--       (δ† (λ y' => f (g y) y')) y dy'
--       +
--       (δ† g y) (δ† (λ x => f x y) (g y) dy')
--     := 
-- by 
--   sorry




