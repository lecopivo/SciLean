import Lean
import Init.Classical

import SciLean.Core.DifferentialDep
import SciLean.Core.Adjoint
import SciLean.Core.HasAdjDiffDep

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbertDiff X] [SemiHilbertDiff Y] [SemiHilbertDiff Z] 
variable {Y₁ Y₂ : Type} [SemiHilbertDiff Y₁] [SemiHilbertDiff Y₂]
variable {ι : Type} [Enumtype ι]


noncomputable 
def adjointDifferentialDep (f : X → Y) (x : X) (dy' : 𝒯[f x] Y) : 𝒯[x] X := (∂ f x)† dy'

instance (priority:=low) (f : X → Y) : PartialDagger f (adjointDifferentialDep f) := ⟨⟩


-- Question: Should there be `𝒯[y] Y` or `𝒯[f x] Y`?
-- Maybe return `(y:Y)×(𝒯[y] Y → 𝒯[x] X)×(f x = y)` but there is a problem with `Sigma` vs `PSigma`
noncomputable
def reverseDifferentialDep (f : X → Y) (x : X) : (Σ' (y:Y) (_:𝒯[y] Y → 𝒯[x] X), (f x=y)) := ⟨f x, λ dy => ∂† f x dy, rfl⟩

instance (priority:=low) (f : X → Y) : ReverseDifferential f (reverseDifferentialDep f) := ⟨⟩

noncomputable
abbrev gradientDep (f : X → ℝ) (x : X) : 𝒯[x] X := ∂† f x 1

instance (priority:=low) (f : X → ℝ) : Nabla f (gradientDep f) := ⟨⟩


-- -- Notation 
-- -- ∇ s, f s         --> ∇ λ s => f s
-- -- ∇ s : ℝ, f s     --> ∇ λ s : ℝ => f s
-- -- ∇ s := t, f s    --> (∇ λ s => f s) t
-- syntax "∇" diffBinder "," term:66 : term
-- syntax "∇" "(" diffBinder ")" "," term:66 : term
-- macro_rules 
-- | `(∇ $x:ident, $f) =>
--   `(∇ λ $x => $f)
-- | `(∇ $x:ident : $type:term, $f) =>
--   `(∇ λ $x : $type => $f)
-- | `(∇ $x:ident := $val:term, $f) =>
--   `((∇ λ $x => $f) $val)
-- | `(∇ ($b:diffBinder), $f) =>
--   `(∇ $b, $f)


instance (f : X → Y) [HasAdjDiffDepT f] (x : X) : IsLinT (∂† f x) := sorry

----------------------------------------------------------------------


@[simp ↓, autodiff]
theorem id.arg_x.adjDiffDep_simp
  : ∂† (λ x : X => x) = λ x dx => dx := by simp[adjointDifferentialDep]; done

@[simp ↓, autodiff]
theorem const.arg_x.adjDiffDep_simp 
  : ∂† (λ (x : X) (i : ι) => x) = λ x f => ∑ i, f i := by simp[adjointDifferentialDep]; done

@[simp ↓, autodiff]
theorem const.arg_y.adjDiffDep_simp (x : X)
  : ∂† (λ (y : Y) => x) = (λ y dy' => 0) := by simp[adjointDifferentialDep]; done

@[simp ↓ low-4, autodiff low-4]
theorem swap.arg_y.adjDiffDep_simp
  (f : ι → X → Z) [inst : ∀ i, HasAdjDiffDepT (f i)]
  : ∂† (λ x y => f y x) = (λ x dx' => ∑ i, (∂† (f i) x) (dx' i)) := 
by 
  have := λ i => (inst i).proof.1
  have := λ i => (inst i).proof.2

  simp[adjointDifferentialDep]; done

@[simp ↓ low-3, autodiff low-3]
theorem subst.arg_x.adjDiffDep_simp
  (f : X → Y → Z) [instf : HasAdjDiffDepNT 2 f]
  (g : X → Y) [instg : HasAdjDiffDepT g]
  : ∂† (λ x => f x (g x)) 
    = 
    λ x dx' => 
      let ⟨y,dg',h⟩ := ℛ g x
      (∂† (hold λ x' => f x' y)) x (h ▸ dx')
      +
      dg' (∂† (f x) y (h ▸ dx'))
    := 
by 
  have := instg.proof.1
  have := instg.proof.2
  have := instf.proof.1

  funext x dx';
  simp[adjointDifferentialDep, tangentMapDep]
  admit


@[simp ↓ low-2, autodiff low-2]
theorem subst.arg_x.parm1.adjDiffDep_simp
  (a : α)
  (f : X → Y → α → Z) [HasAdjDiffDepNT 2 λ x y => f x y a]
  (g : X → Y) [instg : HasAdjDiffDepT g]
  : ∂† (λ x => f x (g x) a) 
    = 
    λ x dx' => 
      let ⟨y,dg',h⟩ := ℛ g x
      (∂† (hold λ x' => f x' y a)) x (h ▸ dx')
      +
      dg' (∂† (hold λ y' => f x y' a) y (h ▸ dx'))
    := 
by 
  apply subst.arg_x.adjDiffDep_simp (λ x y => f x y a) g
  done

@[simp ↓ low-2, autodiff low-2]
theorem subst.arg_x.parm2.adjDiffDep_simp
  (a : α) (b : β)
  (f : X → Y → α → β → Z) [HasAdjDiffDepNT 2 λ x y => f x y a b]
  (g : X → Y) [instg : HasAdjDiffDepT g]
  : ∂† (λ x => f x (g x) a b) 
    = 
    λ x dx' => 
      let ⟨y,dg',h⟩ := ℛ g x
      (∂† (hold λ x' => f x' y a b)) x (h ▸ dx')
      +
      dg' (∂† (hold λ y' => f x y' a b) y (h ▸ dx'))
    := 
by 
  apply subst.arg_x.adjDiffDep_simp (λ x y => f x y a b) g
  done

@[simp ↓ low-2, autodiff low-2]
theorem subst.arg_x.parm3.adjDiffDep_simp
  (a : α) (b : β) (c : γ)
  (f : X → Y → α → β → γ → Z) [HasAdjDiffDepNT 2 λ x y => f x y a b c]
  (g : X → Y) [instg : HasAdjDiffDepT g]
  : ∂† (λ x => f x (g x) a b c) 
    = 
    λ x dx' => 
      let ⟨y,dg',h⟩ := ℛ g x
      (∂† (hold λ x' => f x' y a b c)) x (h ▸ dx')
      +
      dg' (∂† (hold λ y => f x y a b c) y (h ▸ dx'))
    := 
by 
  apply subst.arg_x.adjDiffDep_simp (λ x y => f x y a b c) g
  done

@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.adjDiffDep_simp
  (f : Y → Z) [instf : HasAdjDiffDepT f]
  (g : X → Y) [instg : HasAdjDiffDepT g]
  : ∂† (λ x => f (g x)) 
    = 
    λ x dx' => 
      let ⟨y,dg',h⟩ := ℛ g x
      dg' ((∂† f y) (h ▸ dx')) := 
by 
  simp; unfold hold; simp
  done

@[simp ↓ low-2, autodiff low-2]
theorem diag.arg_x.adjDiffDep_simp
  (f : Y₁ → Y₂ → Z) [HasAdjDiffDepNT 2 f]
  (g₁ : X → Y₁) [hg : HasAdjDiffDepT g₁]
  (g₂ : X → Y₂) [HasAdjDiffDepT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx' => 
      let ⟨y₁,dg₁',h₁⟩ := ℛ g₁ x
      let ⟨y₂,dg₂',h₂⟩ := ℛ g₂ x
      dg₁' ((∂† λ y₁ => f y₁ y₂) y₁ (h₁ ▸ h₂ ▸ dx'))
      +
      dg₂' ((∂† λ y₂ => f y₁ y₂) y₂ (h₂ ▸ h₁ ▸ dx'))
    := 
by
  simp; unfold hold; simp; unfold hold; simp[reverseDifferentialDep,adjointDifferentialDep]; done

@[simp ↓ low, autodiff low]
theorem eval.arg_f.adjDiffDep_simp
  (i : ι)
  : ∂† (λ (f : ι → X) => f i) 
    = 
    (λ f df' j => if h : i = j then h ▸ df' else 0) 
  := 
by 
  simp[reverseDifferentialDep,adjointDifferentialDep]; done

@[simp ↓ low-1, autodiff low-1]
theorem eval.arg_x.parm1.adjDiffDep_simp
  (f : X → ι → Z) [HasAdjDiffDep f]
  : ∂† (λ x => f x i) 
    = 
    (λ x dx' => (∂† f x) (λ j => if h : i = j then h ▸ dx' else 0)) 
  := 
by 
  rw [comp.arg_x.adjDiffDep_simp (λ (x : ι → Z) => x i) f]
  simp[reverseDifferentialDep,adjointDifferentialDep]


--------------------------------------------------------
-- These theorems are problematic when used with simp --


@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.parm1.adjDiffDep_simp
  (a : α) 
  (f : Y → α → Z) [HasAdjDiffDep λ y => f y a]
  (g : X → Y) [HasAdjDiffDep g]
  : 
    ∂† (λ x => f (g x) a)
    = 
    λ x dx' => 
      let ⟨y,dg',h⟩ := ℛ g x
      dg' ((∂† (hold λ y => f y a)) y (h ▸ dx'))
:= by 
  simp; unfold hold; simp
  done

@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.parm2.adjDiffDep_simp
  (a : α) (b : β)
  (f : Y → α → β → Z) [HasAdjDiffDep λ y => f y a b]
  (g : X → Y) [HasAdjDiffDep g]
  : 
    ∂† (λ x => f (g x) a b)
    = 
    λ x dx' => 
      let ⟨y,dg',h⟩ := ℛ g x
      dg' ((∂† (hold λ y => f y a b)) y (h ▸ dx'))
:= by 
  simp; unfold hold; simp
  done

@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.parm3.adjDiffDep_simp
  (a : α) (b : β) (c : γ)
  (f : Y → α → β → γ → Z) [HasAdjDiffDep λ y => f y a b c]
  (g : X → Y) [HasAdjDiffDep g]
  : 
    ∂† (λ x => f (g x) a b c)
    = 
    λ x dx' => 
      let ⟨y,dg',h⟩ := ℛ g x
      dg' ((∂† (hold λ y => f y a b c)) y (h ▸ dx'))
:= by 
  simp; unfold hold; simp
  done

@[simp ↓ low-1, autodiff low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm1.adjDiffDep_simp
  (a : α)
  (f : Y₁ → Y₂ → α → Z) [HasAdjDiffDepNT 2 λ y₁ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [HasAdjDiffDepT g₁]
  (g₂ : X → Y₂) [HasAdjDiffDepT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x) a)
    = 
    λ x dx' => 
      let ⟨y₁,dg₁',h₁⟩ := ℛ g₁ x
      let ⟨y₂,dg₂',h₂⟩ := ℛ g₂ x
      dg₁' ((∂† λ y₁ => f y₁ y₂ a) y₁ (h₁ ▸ h₂ ▸ dx'))
      +
      dg₂' ((∂† λ y₂ => f y₁ y₂ a) y₂ (h₂ ▸ h₁ ▸ dx'))
:= by 
  (apply diag.arg_x.adjDiffDep_simp (λ y₁ y₂ => f y₁ y₂ a) g₁ g₂)
  
@[simp ↓ low-1, autodiff low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm2.adjDiffDep_simp
  (a : α) (b : β)
  (f : Y₁ → Y₂ → α → β → Z) [HasAdjDiffDepNT 2 λ y₁ y₂ => f y₁ y₂ a b]
  (g₁ : X → Y₁) [HasAdjDiffDepT g₁]
  (g₂ : X → Y₂) [HasAdjDiffDepT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x) a b)
    = 
    λ x dx' => 
      let ⟨y₁,dg₁',h₁⟩ := ℛ g₁ x
      let ⟨y₂,dg₂',h₂⟩ := ℛ g₂ x
      dg₁' ((∂† λ y₁ => f y₁ y₂ a b) y₁ (h₁ ▸ h₂ ▸ dx'))
      +
      dg₂' ((∂† λ y₂ => f y₁ y₂ a b) y₂ (h₂ ▸ h₁ ▸ dx'))
:= by 
  (apply diag.arg_x.adjDiffDep_simp (λ y₁ y₂ => f y₁ y₂ a b) g₁ g₂)
  done

@[simp ↓ low-1, autodiff low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm3.adjDiffDep_simp
  (a : α) (b : β) (c : γ)
  (f : Y₁ → Y₂ → α → β → γ → Z) [HasAdjDiffDepNT 2 λ y₁ y₂ => f y₁ y₂ a b c]
  (g₁ : X → Y₁) [HasAdjDiffDepT g₁]
  (g₂ : X → Y₂) [HasAdjDiffDepT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x) a b c)
    = 
    λ x dx' => 
      let ⟨y₁,dg₁',h₁⟩ := ℛ g₁ x
      let ⟨y₂,dg₂',h₂⟩ := ℛ g₂ x
      dg₁' ((∂† λ y₁ => f y₁ y₂ a b c) y₁ (h₁ ▸ h₂ ▸ dx'))
      +
      dg₂' ((∂† λ y₂ => f y₁ y₂ a b c) y₂ (h₂ ▸ h₁ ▸ dx'))
:= by 
  (apply diag.arg_x.adjDiffDep_simp (λ y₁ y₂ => f y₁ y₂ a b c) g₁ g₂)
  done

--------------------------------------------------------------------------------


@[simp ↓, autodiff]
theorem id.arg_x.revDiffDep_simp
  : ℛ (λ x : X => x) = λ x => ⟨x, λ x => x, rfl⟩ := by simp[reverseDifferentialDep]; done

@[simp ↓, autodiff]
theorem const.arg_x.revDiffDep_simp 
  : ℛ (λ (x : X) (i : ι) => x) 
    = 
    λ x => 
      ⟨(λ i => x), (λ f => ∑ i, f i), rfl⟩ 
  := by simp[reverseDifferentialDep]; done

@[simp ↓, autodiff]
theorem const.arg_y.revDiffDep_simp (x : X)
  : ℛ (λ (y : Y) => x) 
    =
    λ y => 
      ⟨x, (λ dy' => 0), rfl⟩
  := by simp[reverseDifferentialDep]; done

@[simp ↓ low-4, autodiff low-4]
theorem swap.arg_y.revDiffDep_simp
  (f : ι → X → Z) [inst : ∀ i, HasAdjDiffDepT (f i)]
  : ∂† (λ x y => f y x) = (λ x dx' => ∑ i, (∂† (f i) x) (dx' i)) := 
by 
  have := λ i => (inst i).proof.1
  have := λ i => (inst i).proof.2

  simp[adjointDifferentialDep]; done

@[simp ↓ low-3, autodiff low-3]
theorem subst.arg_x.revDiffDep_simp
  (f : X → Y → Z) [instf : HasAdjDiffDepNT 2 f]
  (g : X → Y) [instg : HasAdjDiffDepT g]
  : ℛ (λ x => f x (g x)) 
    = 
    λ x => 
      let ⟨y,dg',hg⟩ := ℛ g x
      let ⟨z,df',hf⟩ := ℛ (uncurryN 2 f) (x,y)
      ⟨z, λ dz' => 
           let (dx₁,dy) := df' dz'
           dx₁ + dg' dy
      , by 
          rw[hg]
          rw[(rfl : uncurryN 2 f (x,y) = f x y)] at hf
          apply hf
          done⟩
    := 
by 
  have := instg.proof.1
  have := instg.proof.2
  have := instf.proof.1

  funext x;
  simp[adjointDifferentialDep, tangentMapDep, reverseDifferentialDep,uncurryN, Prod.Uncurry.uncurry,instUncurryHAddNatInstHAddInstAddNatOfNatForAllProd]
  admit


@[simp ↓ low-2, autodiff low-2]
theorem subst.arg_x.parm1.revDiffDep_simp
  (a : α)
  (f : X → Y → α → Z) [HasAdjDiffDepNT 2 λ x y => f x y a]
  (g : X → Y) [instg : HasAdjDiffDepT g]
  : ℛ (λ x => f x (g x) a) 
    = 
    λ x => 
      let ⟨y,dg',hg⟩ := ℛ g x
      let ⟨z,df',hf⟩ := ℛ (uncurryN 2 (λ x y => f x y a)) (x,y)
      ⟨z, λ dz' => 
           let (dx₁,dy) := df' dz'
           dx₁ + dg' dy
      , by 
          rw[hg]
          rw[(rfl : (uncurryN 2 (λ x y => f x y a)) (x,y) = f x y a)] at hf
          apply hf
          done⟩
    := 
by 
  apply subst.arg_x.revDiffDep_simp (λ x y => f x y a) g
  done

@[simp ↓ low-2, autodiff low-2]
theorem subst.arg_x.parm2.revDiffDep_simp
  (a : α) (b : β)
  (f : X → Y → α → β → Z) [HasAdjDiffDepNT 2 λ x y => f x y a b]
  (g : X → Y) [instg : HasAdjDiffDepT g]
  : ℛ (λ x => f x (g x) a b) 
    = 
    λ x => 
      let ⟨y,dg',hg⟩ := ℛ g x
      let ⟨z,df',hf⟩ := ℛ (uncurryN 2 (λ x y => f x y a b)) (x,y)
      ⟨z, λ dz' => 
           let (dx₁,dy) := df' dz'
           dx₁ + dg' dy
      , by 
          rw[hg]
          rw[(rfl : (uncurryN 2 (λ x y => f x y a b)) (x,y) = f x y a b)] at hf
          apply hf
          done⟩
    := 
by 
  apply subst.arg_x.revDiffDep_simp (λ x y => f x y a b) g
  done

@[simp ↓ low-2, autodiff low-2]
theorem subst.arg_x.parm3.revDiffDep_simp
  (a : α) (b : β) (c : γ)
  (f : X → Y → α → β → γ → Z) [HasAdjDiffDepNT 2 λ x y => f x y a b c]
  (g : X → Y) [instg : HasAdjDiffDepT g]
  : ℛ (λ x => f x (g x) a b c) 
    = 
    λ x => 
      let ⟨y,dg',hg⟩ := ℛ g x
      let ⟨z,df',hf⟩ := ℛ (uncurryN 2 (λ x y => f x y a b c)) (x,y)
      ⟨z, λ dz' => let (dx₁,dy) := df' dz'; dx₁ + dg' dy, 
       by rw[hg]; rw[← hf]; done⟩
    := 
by 
  apply subst.arg_x.revDiffDep_simp (λ x y => f x y a b c) g
  done


-- @[simp ↓ low-10, autodiff low-10]
theorem uncurryN2.arg_x.diffDep_simp
  (f : X → Y → Z) [HasAdjDiffDepNT 2 f]
  : ∂† (uncurryN 2 f) 
    =
    λ (x,y) dz =>
      (∂† (λ x' => f x' y) x dz, ∂† (λ y' => f x y') y dz)
  := sorry_proof

@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.revDiffDep_simp
  (f : Y → Z) [instf : HasAdjDiffDepT f]
  (g : X → Y) [instg : HasAdjDiffDepT g]
  : ℛ (λ x => f (g x)) 
    = 
    λ x => 
      let ⟨y,dg',hg⟩ := ℛ g x
      let ⟨z,df',hf⟩ := ℛ f y
      ⟨z, λ dz => dg' (df' dz), by rw[hg]; rw[hf]; done⟩ := 
by 
  simp[reverseDifferentialDep, uncurryN2.arg_x.diffDep_simp]
  done

@[simp ↓ low-2, autodiff low-2]
theorem diag.arg_x.revDiffDep_simp
  (f : Y₁ → Y₂ → Z) [HasAdjDiffDepNT 2 f]
  (g₁ : X → Y₁) [hg : HasAdjDiffDepT g₁]
  (g₂ : X → Y₂) [HasAdjDiffDepT g₂]
  : ℛ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x => 
      let ⟨y₁,dg₁',h₁⟩ := ℛ g₁ x
      let ⟨y₂,dg₂',h₂⟩ := ℛ g₂ x
      let ⟨z, df', hf⟩ := ℛ (uncurryN 2 f) (y₁,y₂)
      ⟨z, λ dz => let (dy₁,dy₂) := df' dz; dg₁' dy₁ + dg₂' dy₂, 
       by rw[h₁,h₂]; rw[← hf]; done⟩
      -- dg₁' ((∂† λ y₁ => f y₁ y₂) y₁ (h₁ ▸ h₂ ▸ dx'))
      -- +
      -- dg₂' ((∂† λ y₂ => f y₁ y₂) y₂ (h₂ ▸ h₁ ▸ dx'))
    := 
by
  simp[reverseDifferentialDep, uncurryN2.arg_x.diffDep_simp]; unfold hold;simp
  done

@[simp ↓ low, autodiff low]
theorem eval.arg_f.revDiffDep_simp
  (i : ι)
  : ℛ (λ (f : ι → X) => f i) 
    = 
    λ f => 
      ⟨f i,
       λ dx j => if h : i = j then h ▸ dx else 0,
       rfl⟩
  := 
by 
  simp[reverseDifferentialDep,adjointDifferentialDep]; done

@[simp ↓ low-1, autodiff low-1]
theorem eval.arg_x.parm1.revDiffDep_simp
  (f : X → ι → Z) [HasAdjDiffDep f] (i : ι)
  : ℛ (λ x => f x i) 
    = 
    λ x =>
      let ⟨fx, df', hf⟩ := ℛ f x
      ⟨fx i, 
      λ dx' => df' (λ j => if h : i = j then h ▸ dx' else 0),
      by rw[hf]; done⟩
  := 
by 
  rw [comp.arg_x.revDiffDep_simp (λ (x : ι → Z) => x i) f]
  simp[reverseDifferentialDep,adjointDifferentialDep]


-- @[simp ↓]
-- theorem subst.aprg_x.revDiffDep_simp'''
--   (f : X → Y → Z) [IsSmooth f]
--   [instfx : ∀ y, HasAdjDiffDep λ x => f x y]
--   [instfy : ∀ x, HasAdjDiffDep (f x)]
--   (g : Y → X) [instg : HasAdjDiffDep g]
--   : ∂† (λ y => f (g y) y) 
--     = 
--     λ y dy' => 
--       (∂† (λ y' => f (g y) y')) y dy'
--       +
--       (∂† g y) (∂† (λ x => f x y) (g y) dy')
--     := 
-- by 
--   sorry




