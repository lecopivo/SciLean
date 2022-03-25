import SciLean.Operators.Adjoint.Basic

namespace SciLean


variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]

class AtomicAdjointFun (f : X → Y) where
  is_lin : IsLin f := by infer_instance
  has_adjoint : HasAdjoint f
  adj : Y → X
  is_adj : f† = adj

class AtomicAdjointFun₂ (f : X → Y → Z) where
  is_lin₁ : IsLin f := by infer_instance
  is_lin₂ x : IsLin (f x) := by infer_instance
  has_adjoint₁ (y) : HasAdjoint (λ x => f x y)
  has_adjoint₂ (x) : HasAdjoint (λ y => f x y)
  adj₁ : Y → Z → X
  adj₂ : X → Z → Y
  is_adj₁ (y) : (λ x => f x y)† = adj₁ y
  is_adj₂ (x) : (λ y => f x y)† = adj₂ x

attribute [reducible] AtomicAdjointFun.adj
attribute [reducible] AtomicAdjointFun₂.adj₁
attribute [reducible] AtomicAdjointFun₂.adj₂

@[simp high]
theorem adjoint_of_atomic (f : X → Y) [AtomicAdjointFun f]
  : f† = AtomicAdjointFun.adj f :=
by
  apply AtomicAdjointFun.is_adj
  done

@[simp high]
theorem adjoint_of_atomic₂_adj₁ (f : X → Y → Z) [AtomicAdjointFun₂ f] (y)
  : (λ x => f x y)† = AtomicAdjointFun₂.adj₁ f y :=
by
  apply AtomicAdjointFun₂.is_adj₁
  done

@[simp high]
theorem adjoint_of_atomic₂_adj₂ (f : X → Y → Z) [AtomicAdjointFun₂ f] (x)
  : (λ y => f x y)† = AtomicAdjointFun₂.adj₂ f x :=
by
  apply AtomicAdjointFun₂.is_adj₂ (f := f) x
  done

instance (priority := high) (f : X → Y) [AtomicAdjointFun f] : HasAdjoint f := AtomicAdjointFun.has_adjoint
instance (priority := high) (f : X → Y → Z) [AtomicAdjointFun₂ f] (y) : HasAdjoint (λ x => f x y) := AtomicAdjointFun₂.has_adjoint₁ y
instance (priority := high) (f : X → Y → Z) (x : X) [AtomicAdjointFun₂ f] : HasAdjoint (λ y => f x y) := AtomicAdjointFun₂.has_adjoint₂ (f := f) x

--------------------------------------------------------------------------
-- Help higher order unification
variable {ι κ δ} [Enumtype ι] [Enumtype κ] [Enumtype δ]

@[simp high]
theorem adjoint_of_atomic₂_adj₁_at_point1 (f : X → Y → α → Z) (a) [AtomicAdjointFun₂ (λ x y => f x y a)] (y)
  : (λ x => f x y a)† = AtomicAdjointFun₂.adj₁ (λ x y => f x y a) y :=
by 
  apply AtomicAdjointFun₂.is_adj₁ (f := (λ x y => f x y a))
  done

@[simp high]
theorem adjoint_of_atomic₂_adj₂_at_point1 (f : X → Y → α → Z) (a) [AtomicAdjointFun₂ (λ x y => f x y a)] (x)
  : (λ y => f x y a)† = AtomicAdjointFun₂.adj₂ (λ x y => f x y a) x :=
by
  apply AtomicAdjointFun₂.is_adj₂ (f := (λ x y => f x y a)) x
  done

@[simp high]
theorem adjoint_of_atomic₂_adj₁_parm1 (f : X → Y → ι → Z) [AtomicAdjointFun₂ f] (y)
  : (λ x i => f x y i)† = AtomicAdjointFun₂.adj₁ f y :=
by 
  apply AtomicAdjointFun₂.is_adj₁ (f := f)
  done

@[simp high]
theorem adjoint_of_atomic₂_adj₂_parm1 (f : X → Y → ι → Z) [AtomicAdjointFun₂ f] (x)
  : (λ y i => f x y i)† = AtomicAdjointFun₂.adj₂ f x :=
by 
  apply AtomicAdjointFun₂.is_adj₂ (f := f)
  done

instance (priority := high) (f : X → Y → α → Z) (a y) [AtomicAdjointFun₂ (λ x y => f x y a)] : HasAdjoint (λ x => f x y a) := AtomicAdjointFun₂.has_adjoint₁ (f := (λ x y => f x y a)) y

instance (priority := high) (f : X → Y → α → Z) (a x) [AtomicAdjointFun₂ (λ x y => f x y a)] : HasAdjoint (λ y => f x y a) := AtomicAdjointFun₂.has_adjoint₂ (f := (λ x y => f x y a)) x

instance (priority := high) (f : X → Y → ι → Z) (y) [AtomicAdjointFun₂ f] : HasAdjoint (λ x a => f x y a) := AtomicAdjointFun₂.has_adjoint₁ (f := f) y
instance (priority := high) (f : X → Y → ι → κ → Z) (y) [AtomicAdjointFun₂ f] : HasAdjoint (λ x a b => f x y a b) := AtomicAdjointFun₂.has_adjoint₁ (f := f) y
instance (priority := high) (f : X → Y → ι → κ → δ → Z) (y) [AtomicAdjointFun₂ f] : HasAdjoint (λ x a b c => f x y a b c) := AtomicAdjointFun₂.has_adjoint₁ (f := f) y

instance (priority := high) (f : X → Y → ι → Z) (x) [AtomicAdjointFun₂ f] : HasAdjoint (λ y a => f x y a) := AtomicAdjointFun₂.has_adjoint₂ (f := f) x
instance (priority := high) (f : X → Y → ι → κ → Z) (x) [AtomicAdjointFun₂ f] : HasAdjoint (λ y a b => f x y a b) := AtomicAdjointFun₂.has_adjoint₂ (f := f) x
instance (priority := high) (f : X → Y → ι → κ → δ → Z) (x) [AtomicAdjointFun₂ f] : HasAdjoint (λ y a b c => f x y a b c) := AtomicAdjointFun₂.has_adjoint₂ (f := f) x
