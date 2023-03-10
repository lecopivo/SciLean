import SciLean.Core.Hilbert

namespace SciLean

class Basis (X : Type u) (ι : outParam $ Type v) (K : outParam $ Type w) where
  basis : ι → X
  proj  : ι → X → K

class DualBasis (X : Type u) (ι : outParam $ Type v) (K : outParam $ Type w) where
  dualBasis : ι → X
  dualProj  : ι → X → K

class BasisDuality (X : Type u) where
  toDual   : X → X  -- transforms basis vectors to dual basis vectors
  fromDual : X → X  -- transforma dual basis vectors to basis vectors

section Basis

  instance : Basis ℝ Unit ℝ := 
  {
    basis := λ _ => 1
    proj  := λ _ x => x
  }

  instance : DualBasis ℝ Unit ℝ := 
  {
    dualBasis := λ _ => 1
    dualProj  := λ _ x => x
  }

  instance : BasisDuality ℝ := 
  {
    toDual := λ x => x
    fromDual  := λ x => x
  }

  /-- `𝕖 i` is the i-th basis vector -/
  prefix:max "𝕖" => Basis.basis
  /-- `𝕖[X] i` is the i-th basis vector of type `X` -/
  macro:max "𝕖[" X:term "]" i:term : term => `(Basis.basis (X:=$X) $i)

  /-- `𝕖' i` is the i-th dual basis vector -/
  prefix:max "𝕖'" => DualBasis.dualBasis
  /-- `𝕖'[X] i` is the i-th dual basis vector of type `X` -/
  macro:max "𝕖'[" X:term "]" i:term : term => `(DualBasis.dualBasis (X:=$X) $i)

  /-- `𝕡 i x` is projection of `x` onto i-th basis vector `𝕖 i` -/
  prefix:max "𝕡" => Basis.proj
  /-- `𝕡' i x` is projection of `x` onto i-th dual basis vector `𝕖' i` -/
  prefix:max "𝕡'" => DualBasis.dualProj

  instance {X Y ι κ K} [Basis X ι K] [Basis Y κ K] [Zero X] [Zero Y] : Basis (X × Y) (ι ⊕ κ) K where
    basis := λ i =>
      match i with
      | Sum.inl ix => (𝕖 ix, 0)
      | Sum.inr iy => (0, 𝕖 iy)
    proj := λ i x =>
      match i with
      | Sum.inl ix => 𝕡 ix x.1
      | Sum.inr iy => 𝕡 iy x.2

  instance {X Y ι κ K} [DualBasis X ι K] [DualBasis Y κ K] [Zero X] [Zero Y] : DualBasis (X × Y) (ι ⊕ κ) K where
    dualBasis := λ i =>
      match i with
      | Sum.inl ix => (𝕖' ix, 0)
      | Sum.inr iy => (0, 𝕖' iy)
    dualProj := λ i x =>
      match i with
      | Sum.inl ix => 𝕡' ix x.1
      | Sum.inr iy => 𝕡' iy x.2

  instance {X Y} [BasisDuality X] [BasisDuality Y] : BasisDuality (X×Y) where
    toDual := λ (x,y) => (BasisDuality.toDual x, BasisDuality.toDual y)
    fromDual := λ (x,y) => (BasisDuality.fromDual x, BasisDuality.fromDual y)

end Basis

/--
 -/
class FinVec (X : Type) (ι : outParam Type) [outParam $ Enumtype ι] extends Hilbert X, Basis X ι ℝ, DualBasis X ι ℝ, BasisDuality X where
  is_basis : ∀ x : X, x = ∑ i : ι, 𝕡 i x * 𝕖[X] i
  duality : ∀ i j, ⟪𝕖[X] i, 𝕖'[X] j⟫ = [[i=j]]
  to_dual   : toDual   x = ∑ i,  𝕡 i x * 𝕖'[X] i
  from_dual : fromDual x = ∑ i, 𝕡' i x *  𝕖[X] i

theorem basis_ext {X ι} [Enumtype ι] [FinVec X ι] (x y : X)
  : (∀ i, ⟪x, 𝕖 i⟫ = ⟪y, 𝕖 i⟫) → (x = y) := sorry_proof

theorem dualBasis_ext {X ι} [Enumtype ι] [FinVec X ι] (x y : X)
  : (∀ i, ⟪x, 𝕖' i⟫ = ⟪y, 𝕖' i⟫) → (x = y) := sorry_proof

theorem inner_proj_dualProj {X ι} [Enumtype ι] [FinVec X ι] (x y : X)
  : ⟪x, y⟫ = ∑ i, 𝕡 i x * 𝕡' i y :=
by sorry_proof

@[simp]
theorem inner_basis_dualBasis {X ι} [Enumtype ι] [FinVec X ι] (i j : ι)
  : ⟪𝕖[X] i, 𝕖' j⟫ = [[i=j]] :=
by apply FinVec.duality

@[simp]
theorem inner_dualBasis_proj {X ι} [Enumtype ι] [FinVec X ι] (i : ι) (x : X)
  : ⟪x, 𝕖' i⟫ = 𝕡 i x :=
by sorry_proof

@[simp]
theorem proj_basis {X ι} [Enumtype ι] [FinVec X ι] (i j : ι)
  : 𝕡 i (𝕖[X] j) = [[i=j]] :=
by simp only [←inner_dualBasis_proj, inner_basis_dualBasis, eq_comm]; done

@[simp]
theorem inner_dualBasis_basis {X ι} [Enumtype ι] [FinVec X ι] (i j : ι)
  : ⟪𝕖'[X] i, 𝕖 j⟫ = [[i=j]] :=
by 
  sorry_proof

@[simp]
theorem inner_basis_dualProj {X ι} [Enumtype ι] [FinVec X ι] (i : ι) (x : X)
  : ⟪𝕖[X] i, x⟫ = 𝕡' i x :=
by sorry_proof

instance : FinVec ℝ Unit where
  is_basis := by simp[Basis.proj, Basis.basis]; sorry_proof
  duality := by simp[Basis.proj, Basis.basis, DualBasis.dualProj, DualBasis.dualBasis, Inner.inner]; done
  to_dual := by sorry_proof
  from_dual := by sorry_proof
  
-- @[infer_tc_goals_rl]
-- instance {X Y ι κ} [Enumtype ι] [Enumtype κ] [FinVec X ι] [FinVec Y κ]
--   : FinVec (X×Y) (ι⊕κ) where
--   is_basis := sorry_proof
--   duality := sorry_proof

opaque foo {X} {ι : Type} [Enumtype ι] [FinVec X ι] (x : X) : X

set_option pp.all true in
#check foo (1 : ℝ)
