import SciLean.Operators.Calculus.AtomicSmoothFun

namespace SciLean

variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]

class AtomicRSmoothFun (f : X → Y) where -- `extends AtomicSmoothFun f` is causing some performance issues :(
  atomic_smooth : AtomicSmoothFun f := by infer_instance
  has_adjoint (x) : HasAdjoint (δ f x)
  adj : X → Y → X
  is_adj (x) : (δ f x)† = adj x

class AtomicRSmoothFun₂ (f : X → Y → Z) where -- `extends AtomicSmoothFun₂ f` is causing some performance issues :(
  atomic_smooth : AtomicSmoothFun₂ f := by infer_instance
  has_adjoint₁ (x y) : HasAdjoint (λ dx => δ f x dx y)
  has_adjoint₂ (x y) : HasAdjoint (λ dy => δ (f x) y dy)
  adj₁ : X → Y → Z → X
  adj₂ : X → Y → Z → Y
  is_adj₁ (x y) : (λ dx => δ f x dx y)† = adj₁ x y
  is_adj₂ (x y) : (λ dy => δ (f x) y dy)† = adj₂ x y

attribute [reducible] AtomicRSmoothFun.adj
attribute [reducible] AtomicRSmoothFun₂.adj₁
attribute [reducible] AtomicRSmoothFun₂.adj₂

instance (f : X → Y) [AtomicRSmoothFun f] (x : X) : HasAdjoint (δ f x) :=
by
  apply AtomicRSmoothFun.has_adjoint 
  done

@[simp]
theorem adjoint_of_atomic_df (f : X → Y) [AtomicRSmoothFun f] (x : X)
  : (δ f x)† = AtomicRSmoothFun.adj f x :=
by
  apply AtomicRSmoothFun.is_adj
  done

@[simp]
theorem adjoint_of_atomic₂_df₁ (f : X → Y → Z) [AtomicRSmoothFun₂ f] (x : X) (y : Y)
  : (λ dx => δ f x dx y)† = AtomicRSmoothFun₂.adj₁ f x y :=
by
  apply AtomicRSmoothFun₂.is_adj₁
  done

@[simp]
theorem adjoint_of_atomic₂_df₂ (f : X → Y → Z) [AtomicRSmoothFun₂ f] (x : X) (y : Y)
  : (λ dy => δ (f x) y dy)† = AtomicRSmoothFun₂.adj₂ f x y :=
by
  apply AtomicRSmoothFun₂.is_adj₂
  done

instance (f : X → Y) [AtomicRSmoothFun f] (x) : HasAdjoint (δ f x) := AtomicRSmoothFun.has_adjoint x
instance (f : X → Y → Z) [AtomicRSmoothFun₂ f] (x y) : HasAdjoint (λ dx => δ f x dx y) := AtomicRSmoothFun₂.has_adjoint₁ x y
instance (f : X → Y → Z) [AtomicRSmoothFun₂ f] (x y) : HasAdjoint (λ dy => δ (f x) y dy) := AtomicRSmoothFun₂.has_adjoint₂ x y

@[simp]
theorem reverse_diff_of_atomic (f : X → Y) [AtomicRSmoothFun f]
  : 𝓑 f = λ x => (f x, AtomicRSmoothFun.adj f x) :=
by
  simp [reverse_diff]
  done
