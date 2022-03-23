import SciLean.Basic
import SciLean.Tactic

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U V W : Type} [SemiHilbert U] [SemiHilbert V] [SemiHilbert W]

class AtomicSmoothFun (f : X → Y) where
  is_smooth : IsSmooth f
  df : X → X → Y
  is_diff : δ f = df

class AtomicSmoothFun₂ (f : X → Y → Z) where
  is_smooth₁ : IsSmooth f
  is_smooth₂ (x : X) : IsSmooth (f x)
  df₁ : X → X → Y → Z
  df₂ : X → Y → Y → Z
  is_df₁ : δ f = df₁
  is_df₂ : ∀ x, δ (f x) = df₂ x

attribute [reducible] AtomicSmoothFun.df
attribute [reducible] AtomicSmoothFun₂.df₁
attribute [reducible] AtomicSmoothFun₂.df₂

@[simp]
theorem differential_of_atomic (f : X → Y) [AtomicSmoothFun f]
  : δ f = AtomicSmoothFun.df f :=
by
  apply AtomicSmoothFun.is_diff
  done

@[simp]
theorem differential_of_atomic₂_df₁ (f : X → Y → Z) [AtomicSmoothFun₂ f]
  : δ f = AtomicSmoothFun₂.df₁ f :=
by
  apply AtomicSmoothFun₂.is_df₁
  done

@[simp]
theorem differential_of_atomic₂_df₂ (f : X → Y → Z) [AtomicSmoothFun₂ f] (x : X)
  : δ (f x) = AtomicSmoothFun₂.df₂ f x :=
by
  apply AtomicSmoothFun₂.is_df₂
  done

class AtomicRSmoothFun (f : U → V) extends AtomicSmoothFun f where
  has_adjoint (x) : HasAdjoint (δ f x)
  adj : U → V → U
  is_adj (x) : (δ f x)† = adj x

class AtomicRSmoothFun₂ (f : U → V → W) extends AtomicSmoothFun₂ f where
  has_adjoint₁ (x y) : HasAdjoint (λ dx => δ f x dx y)
  has_adjoint₂ (x y) : HasAdjoint (λ dy => δ (f x) y dy)
  adj₁ : U → V → W → U
  adj₂ : U → V → W → V
  is_adj₁ (x y) : (λ dx => δ f x dx y)† = adj₁ x y
  is_adj₂ (x y) : (λ dy => δ (f x) y dy)† = adj₂ x y

attribute [reducible] AtomicRSmoothFun₂.adj₁
attribute [reducible] AtomicRSmoothFun₂.adj₂

instance : AtomicRSmoothFun₂ (HAdd.hAdd : U → U → U) where
  is_smooth₁ := by infer_instance
  is_smooth₂ := by infer_instance
  df₁ := λ x dx y => dx
  df₂ := λ x y dy => dy
  is_df₁ := by simp
  is_df₂ := by simp
  has_adjoint₁ := by simp infer_instance
  has_adjoint₂ := by simp infer_instance
  adj₁ := λ x y dz => dz
  adj₂ := λ x y dz => dz
  is_adj₁ := by simp
  is_adj₂ := by simp

instance (f : U → V) [AtomicRSmoothFun f] (x : U) : HasAdjoint (δ f x) :=
by
  apply AtomicRSmoothFun.has_adjoint 
  done

class AtomicLinearFun (f : X → Y) where
  is_lin : IsLin f

class AtomicAdjointFun (f : U → V) extends AtomicLinearFun f where
  has_adjoint : HasAdjoint f
  adj : V → U
  is_adj : f† = adj
