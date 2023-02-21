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


-- noncomputable 
-- def adjointDifferential (f : X → Y) (x : X) (dy' : Y) : X := (∂ f x)† dy'

-- @[default_instance]
-- instance (f : X → Y) : PartialDagger f (adjointDifferential f) := ⟨⟩

-- Someting wrong here :(
-- noncomputable 
-- def Smooth.adjointDifferential {X Y} [Hilbert X] [Hilbert Y] (f : X ⟿ Y) : X⟿Y⊸X := λ x ⟿ λ dy ⊸ adjoint (∂ f x) dy

-- @[default_instance]
-- instance (f : X → Y) : PartialDagger f (adjointDifferential f) := ⟨⟩


-- Question: Should there be `𝒯[y] Y` or `𝒯[f x] Y`?
-- Maybe return `(y:Y)×(𝒯[y] Y → 𝒯[x] X)×(f x = y)` but there is a problem with `Sigma` vs `PSigma`
-- noncomputable
-- def reverseDifferential (f : X → Y) (x : X) : Y×(Y→X) := (f x, λ dy => ∂† f x dy)

-- instance (priority:=low) (f : X → Y) : ReverseDifferential f (reverseDifferential f) := ⟨⟩


-- noncomputable
-- abbrev gradient (f : X → ℝ) (x : X) : X := ∂† f x 1

-- @[default_instance]
-- instance (f : X → ℝ) : Nabla f (gradient f) := ⟨⟩

-- noncomputable
-- abbrev Smooth.gradient (f : X ⟿ ℝ) : X⟿X := SmoothMap.mk (λ x => adjoint (λ dx => ∂ f x dx) 1) sorry_proof

-- instance (f : X ⟿ ℝ) : Nabla f (Smooth.gradient f) := ⟨⟩


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
    λ x dz =>
      let (y,dg') := ℛ g x
      -- let (dx,dy) := ∂† (uncurryN 2 f) (x,y) dz
      -- dx + dg' dy
      (∂† (λ x' => f x' y)) x dz
      +
      dg' (∂† (f x) y dz)
    := 
by 
  have := instg.proof.1
  have := instg.proof.2
  have := instf.proof.1
  -- these follow from instf.proof.2
  have : ∀ x y, HasAdjointT (λ dx => ∂ f x dx y) := sorry_proof
  have : ∀ x y, HasAdjointT (λ dy => ∂ (f x) y dy) := sorry_proof

  simp[adjointDifferential, reverseDifferential, tangentMap, -comp.arg_x.parm1.adj_simp]
  done

@[simp ↓ low-2, autodiff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm1.adjDiff_simp
  (a : α)
  (f : X → Y → α → Z) [HasAdjDiffNT 2 λ x y => f x y a]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f x (g x) a) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      -- let (dx,dy) := ∂† (uncurryN 2 (λ x y => f x y a)) (x,y) dz
      -- dx + dg' dy
      (∂† (λ x' => f x' y a)) x dz
      +
      dg' (∂† (λ y' => f x y' a) y dz)
    := 
by 
  rw[subst.arg_x.adjDiff_simp (λ x y => f x y a) g]
  done

@[simp ↓ low-2, autodiff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm2.adjDiff_simp
  (a : α) (b : β)
  (f : X → Y → α → β → Z) [HasAdjDiffNT 2 λ x y => f x y a b]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f x (g x) a b) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      (∂† (λ x' => f x' y a b)) x dz
      +
      dg' (∂† (λ y' => f x y' a b) y dz)
    := 
by 
  apply subst.arg_x.adjDiff_simp (λ x y => f x y a b) g
  done

@[simp ↓ low-2, autodiff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm3.adjDiff_simp
  (a : α) (b : β) (c : γ)
  (f : X → Y → α → β → γ → Z) [HasAdjDiffNT 2 λ x y => f x y a b c]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f x (g x) a b c) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      (∂† (λ x' => f x' y a b c)) x dz
      +
      dg' (∂† (λ y' => f x y' a b c) y dz)
    := 
by 
  apply subst.arg_x.adjDiff_simp (λ x y => f x y a b c) g
  done

@[simp ↓ low-1, autodiff low-1, simp_guard g (λ x => x)]
theorem comp.arg_x.adjDiff_simp
  (f : Y → Z) [instf : HasAdjDiffT f]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f (g x)) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      dg' ((∂† f y) dz) 
  := by simp; done

@[simp ↓ low-2, autodiff low-2, simp_guard g₁ Prod.fst, g₂ Prod.snd]
theorem diag.arg_x.adjDiff_simp
  (f : Y₁ → Y₂ → Z) [HasAdjDiffNT 2 f]
  (g₁ : X → Y₁) [hg : HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dz => 
      let (y₁,dg₁') := ℛ g₁ x
      let (y₂,dg₂') := ℛ g₂ x
      dg₁' ((∂† λ y₁' => f y₁' y₂) y₁ dz)
      +
      dg₂' ((∂† λ y₂' => f y₁ y₂') y₂ dz)
    := 
by
  rw[subst.arg_x.adjDiff_simp]
  simp only [hold,reverseDifferential]
  funext x dz
  rw[comp.arg_x.adjDiff_simp (λ y₁ => f y₁ (g₂ x))]
  simp only [reverseDifferential]
  done

@[simp ↓ low, autodiff low]
theorem eval.arg_f.adjDiff_simp
  (i : ι)
  : ∂† (λ (f : ι → X) => f i) 
    = 
    (λ f df' j => ([[i = j]] * df' : X))
:= sorry

@[simp ↓ low-1, autodiff low-1]
theorem eval.arg_x.parm1.adjDiff_simp
  (f : X → ι → Z) [HasAdjDiff f]
  : ∂† (λ x => f x i) 
    = 
    (λ x dx' => (∂† f x) (λ j => ([[i = j]] * dx' : Z)))
:= 
by 
  rw [comp.arg_x.adjDiff_simp (λ (x : ι → Z) => x i) f]
  simp[reverseDifferential]


--------------------------------------------------------
-- These theorems are problematic when used with simp --


@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.parm1.adjDiff_simp
  (a : α) 
  (f : Y → α → Z) [HasAdjDiff λ y => f y a]
  (g : X → Y) [HasAdjDiff g]
  : 
    ∂† (λ x => f (g x) a) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      dg' ((∂† (hold λ y => f y a)) y dz)
:= by 
  rw[subst.arg_x.parm1.adjDiff_simp]
  simp[-subst.arg_x.parm1.adjDiff_simp,hold]
  done

@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.parm2.adjDiff_simp
  (a : α) (b : β)
  (f : Y → α → β → Z) [HasAdjDiff λ y => f y a b]
  (g : X → Y) [HasAdjDiff g]
  : 
    ∂† (λ x => f (g x) a b) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      dg' ((∂† (hold λ y => f y a b)) y dz)
:= by 
  rw[subst.arg_x.parm2.adjDiff_simp]
  simp[-subst.arg_x.parm2.adjDiff_simp,hold]
  done

@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.parm3.adjDiff_simp
  (a : α) (b : β) (c : γ)
  (f : Y → α → β → γ → Z) [HasAdjDiff λ y => f y a b c]
  (g : X → Y) [HasAdjDiff g]
  : 
    ∂† (λ x => f (g x) a b c) 
    = 
    λ x dx' => 
      let (y,dg') := ℛ g x
      dg' ((∂† (hold λ y => f y a b c)) y dx')
:= by 
  rw[subst.arg_x.parm3.adjDiff_simp]
  simp[-subst.arg_x.parm3.adjDiff_simp,hold]
  done


-- TODO: fix this!!!
example (a : α) (f : Y₁ → Y₂ → α → Z) [IsSmoothT λ y₁ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [hg : IsSmoothT g₁] : IsSmoothT (λ x y => f (g₁ x) y a) := by (try infer_instance); admit


@[simp ↓ low-1, autodiff low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm1.adjDiff_simp
  (a : α)
  (f : Y₁ → Y₂ → α → Z) [HasAdjDiffNT 2 λ y₁ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x) a)
    = 
    λ x dz => 
      let (y₁,dg₁') := ℛ g₁ x
      let (y₂,dg₂') := ℛ g₂ x
      dg₁' ((∂† (hold λ y₁' => f y₁' y₂ a)) y₁ dz)
      +
      dg₂' ((∂† (hold λ y₂' => f y₁ y₂' a)) y₂ dz)
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
    λ x dz => 
      let (y₁,dg₁') := ℛ g₁ x
      let (y₂,dg₂') := ℛ g₂ x
      dg₁' ((∂† (hold λ y₁' => f y₁' y₂ a b)) y₁ dz)
      +
      dg₂' ((∂† (hold λ y₂' => f y₁ y₂' a b)) y₂ dz)
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
    λ x dz => 
      let (y₁,dg₁') := ℛ g₁ x
      let (y₂,dg₂') := ℛ g₂ x
      dg₁' ((∂† (hold λ y₁' => f y₁' y₂ a b c)) y₁ dz)
      +
      dg₂' ((∂† (hold λ y₂' => f y₁ y₂' a b c)) y₂ dz)
:= by 
  (apply diag.arg_x.adjDiff_simp (λ y₁ y₂ => f y₁ y₂ a b c) g₁ g₂)
  done

----------------------------------------------------------------------


@[simp ↓, autodiff]
theorem Prod.fst.arg_xy.adjDiff_simp
  : ∂† (Prod.fst : X×Y → X)
    =
    λ xy dx => (dx,0)
  := by unfold adjointDifferential; simp; done

@[simp ↓, autodiff]
theorem Prod.snd.arg_xy.adjDiff_simp
  : ∂† (Prod.snd : X×Y → Y)
    =
    λ xy dy => (0,dy)
  := by unfold adjointDifferential; simp; done

@[simp ↓, autodiff]
theorem HAdd.hAdd.arg_xy.adjDiff_simp
  : ∂† (uncurryN 2 λ x y : X => x + y)
    =
    λ xy dx => (dx,dx)
  :=  by unfold adjointDifferential; simp; done

@[simp ↓, autodiff]
theorem Prod.fst.arg_xy.revDiff_simp
  : ℛ (Prod.fst : X×Y → X)
    =
    λ (x,y) => (x, λ dx => (dx,0))
  := by unfold reverseDifferential; simp; done

@[simp ↓, autodiff]
theorem Prod.snd.arg_xy.revDiff_simp
  : ℛ (Prod.snd : X×Y → Y)
    =
    λ (x,y) => (y, λ dy => (0,dy))
  := by unfold reverseDifferential; simp; done

@[simp ↓, autodiff]
theorem HAdd.hAdd.arg_xy.revDiff_simp
  : ℛ (uncurryN 2 λ x y : X => x + y)
    =
    λ (x,y) => (x+y, λ dx => (dx,dx))
  := by unfold reverseDifferential; simp; done


--------------------------------------------------------------------------------


@[simp ↓, autodiff]
theorem id.arg_x.revDiff_simp
  : ℛ (λ x : X => x) = λ x => (x, λ x => x) := by simp[reverseDifferential]; done

@[simp ↓, autodiff]
theorem const.arg_x.revDiff_simp 
  : ℛ (λ (x : X) (i : ι) => x) 
    = 
    λ x => ((λ i => x), (λ f => ∑ i, f i))
  := by simp[reverseDifferential]; done

@[simp ↓, autodiff]
theorem const.arg_y.revDiff_simp (x : X)
  : ℛ (λ (y : Y) => x) 
    =
    λ y => 
      (x, (λ dy' => 0))
  := by simp[reverseDifferential]; done

@[simp ↓ low-4, autodiff low-4]
theorem swap.arg_y.revDiff_simp
  (f : ι → X → Z) [inst : ∀ i, HasAdjDiffT (f i)]
  : ∂† (λ x y => f y x) = (λ x dx' => ∑ i, (∂† (f i) x) (dx' i)) := 
by 
  have := λ i => (inst i).proof.1
  have := λ i => (inst i).proof.2

  simp[adjointDifferential]; done

@[simp ↓ low-3, autodiff low-3, simp_guard g (λ x => x)]
theorem subst.arg_x.revDiff_simp
  (f : X → Y → Z) [instf : HasAdjDiffNT 2 f]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ℛ (λ x => f x (g x)) 
    = 
    λ x => 
      let (y,dg') := ℛ g x
      let (z,df') := ℛ (uncurryN 2 f) (x,y)
      (z, λ dz' => 
           let (dx₁,dy) := df' dz'
           dx₁ + dg' dy)
      
    := 
by 
  have := instg.proof.1
  have := instg.proof.2
  have := instf.proof.1

  funext x;
  unfold reverseDifferential
  rw[subst.arg_x.adjDiff_simp]

  simp only [uncurryN, Prod.Uncurry.uncurry]
  simp only [hold, reverseDifferential]
  conv => (rhs; rw[diag.arg_x.adjDiff_simp])
  simp only [reverseDifferential, 
             Prod.fst.arg_xy.adjDiff_simp, 
             Prod.snd.arg_xy.adjDiff_simp,
             prod_add_elemwise, 
             add_zero, zero_add]
  done


@[simp ↓ low-2, autodiff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm1.revDiff_simp
  (a : α)
  (f : X → Y → α → Z) [HasAdjDiffNT 2 λ x y => f x y a]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ℛ (λ x => f x (g x) a) 
    = 
    λ x => 
      let (y,dg') := ℛ g x
      let (z,df') := ℛ (uncurryN 2 (λ x y => f x y a)) (x,y)
      (z, λ dz' => 
           let (dx₁,dy) := df' dz'
           dx₁ + dg' dy)
    := 
by 
  apply subst.arg_x.revDiff_simp (λ x y => f x y a) g
  done

@[simp ↓ low-2, autodiff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm2.revDiff_simp
  (a : α) (b : β)
  (f : X → Y → α → β → Z) [HasAdjDiffNT 2 λ x y => f x y a b]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ℛ (λ x => f x (g x) a b) 
    = 
    λ x => 
      let (y,dg') := ℛ g x
      let (z,df') := ℛ (uncurryN 2 (λ x y => f x y a b)) (x,y)
      (z, λ dz' => 
           let (dx₁,dy) := df' dz'
           dx₁ + dg' dy)
    := 
by 
  apply subst.arg_x.revDiff_simp (λ x y => f x y a b) g
  done

@[simp ↓ low-2, autodiff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm3.revDiff_simp
  (a : α) (b : β) (c : γ)
  (f : X → Y → α → β → γ → Z) [HasAdjDiffNT 2 λ x y => f x y a b c]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ℛ (λ x => f x (g x) a b c) 
    = 
    λ x => 
      let (y,dg') := ℛ g x
      let (z,df') := ℛ (uncurryN 2 (λ x y => f x y a b c)) (x,y)
      (z, λ dz' => let (dx₁,dy) := df' dz'; dx₁ + dg' dy)
    := 
by 
  apply subst.arg_x.revDiff_simp (λ x y => f x y a b c) g
  done


-- @[simp ↓ low-10, autodiff low-10]
theorem uncurryN2.arg_x.diff_simp
  (f : X → Y → Z) [HasAdjDiffNT 2 f]
  : ∂† (uncurryN 2 f) 
    =
    λ (x,y) dz =>
      (∂† (λ x' => f x' y) x dz, ∂† (λ y' => f x y') y dz)
  := sorry_proof

@[simp ↓ low-1, autodiff low-1]
theorem comp.arg_x.revDiff_simp
  (f : Y → Z) [instf : HasAdjDiffT f]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ℛ (λ x => f (g x)) 
    = 
    λ x => 
      let (y,dg') := ℛ g x
      let (z,df') := ℛ f y
      (z, λ dz => dg' (df' dz)) := 
by 
  unfold reverseDifferential
  simp only [comp.arg_x.adjDiff_simp]
  simp only [reverseDifferential]
  done

@[simp ↓ low-2, autodiff low-2]
theorem diag.arg_x.revDiff_simp
  (f : Y₁ → Y₂ → Z) [HasAdjDiffNT 2 f]
  (g₁ : X → Y₁) [hg : HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ℛ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x => 
      let (y₁,dg₁') := ℛ g₁ x
      let (y₂,dg₂') := ℛ g₂ x
      let (z, df') := ℛ (uncurryN 2 f) (y₁,y₂)
      (z, λ dz => let (dy₁,dy₂) := df' dz; dg₁' dy₁ + dg₂' dy₂)
      -- dg₁' ((∂† λ y₁ => f y₁ y₂) y₁ (h₁ ▸ h₂ ▸ dx'))
      -- +
      -- dg₂' ((∂† λ y₂ => f y₁ y₂) y₂ (h₂ ▸ h₁ ▸ dx'))
    := 
by
  unfold reverseDifferential
  funext x
  simp only [uncurryN, Prod.Uncurry.uncurry]
  conv => lhs; enter [2,dz]; rw [diag.arg_x.adjDiff_simp]
  conv => rhs; enter [2,dz]; rw [diag.arg_x.adjDiff_simp]
  simp only [reverseDifferential,             
             Prod.fst.arg_xy.adjDiff_simp, 
             Prod.snd.arg_xy.adjDiff_simp, 
             prod_add_elemwise, 
             add_zero, zero_add]
  done

@[simp ↓ low, autodiff low]
theorem eval.arg_f.revDiff_simp
  (i : ι)
  : ℛ (λ (f : ι → X) => f i) 
    = 
    λ f => (f i, (λ dx j => ([[i=j]] * dx : X)))
  := 
by 
  simp[reverseDifferential,adjointDifferential]; done

@[simp ↓ low-1, autodiff low-1]
theorem eval.arg_x.parm1.revDiff_simp
  (f : X → ι → Z) [HasAdjDiff f] (i : ι)
  : ℛ (λ x => f x i)
    = 
    λ x =>
      let (fx, df') := ℛ f x
      (fx i, 
      λ dz => df' (λ j => ([[i=j]] * dz)))
  := 
by 
  rw [comp.arg_x.revDiff_simp (λ (x : ι → Z) => x i) f]
  simp[reverseDifferential,adjointDifferential]


-- @[simp ↓]
-- theorem subst.arg_x.revDiff_simp'''
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








