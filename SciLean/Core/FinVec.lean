import SciLean.Core.Hilbert

namespace SciLean

class Basis (X : Type u) (ι : outParam $ Type v) (K : outParam $ Type w) where
  basis : ι → X
  proj  : ι → X → K

class DualBasis (X : Type u) (ι : outParam $ Type v) (K : outParam $ Type w) where
  dualBasis : ι → X
  dualProj  : ι → X → K

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

  instance {X Y ι κ K} [Basis X ι K] [Basis Y κ K] [Zero X] [Zero Y] : Basis (X × Y) (ι ⊕ κ) K := 
  {
    basis := λ i =>
      match i with
      | Sum.inl ix => (𝕖 ix, 0)
      | Sum.inr iy => (0, 𝕖 iy)
    proj := λ i x =>
      match i with
      | Sum.inl ix => 𝕡 ix x.1
      | Sum.inr iy => 𝕡 iy x.2
  }

  instance {X Y ι κ K} [DualBasis X ι K] [DualBasis Y κ K] [Zero X] [Zero Y] : DualBasis (X × Y) (ι ⊕ κ) K := 
  {
    dualBasis := λ i =>
      match i with
      | Sum.inl ix => (𝕖' ix, 0)
      | Sum.inr iy => (0, 𝕖' iy)
    dualProj := λ i x =>
      match i with
      | Sum.inl ix => 𝕡' ix x.1
      | Sum.inr iy => 𝕡' iy x.2
  }


end Basis

/--
 -/
class FinVec (X : Type) (ι : outParam Type) [outParam $ Enumtype ι] extends Hilbert X, Basis X ι ℝ, DualBasis X ι ℝ where
  is_basis : ∀ x : X, x = ∑ i : ι, 𝕡 i x * 𝕖[X] i
  duality : ∀ i j, ⟪𝕖[X] i, 𝕖'[X] j⟫ = [[i=j]]

@[simp]
theorem inner_dual_basis {X ι} [Enumtype ι] [FinVec X ι] (i j : ι)
  : ⟪𝕖[X] i, 𝕖' j⟫ = [[i=j]] :=
by apply FinVec.duality

@[simp]
theorem inner_dual_basis_alt {X ι} [Enumtype ι] [FinVec X ι] (i j : ι)
  : ⟪𝕖'[X] i, 𝕖 j⟫ = [[i=j]] :=
by 
  sorry_proof


instance : FinVec ℝ Unit where
  is_basis := by simp[Basis.proj, Basis.basis]; sorry_proof
  duality := by simp[Basis.proj, Basis.basis, DualBasis.dualProj, DualBasis.dualBasis, Inner.inner]; done
  
-- @[infer_tc_goals_rl]
-- instance {X Y ι κ} [Enumtype ι] [Enumtype κ] [FinVec X ι] [FinVec Y κ]
--   : FinVec (X×Y) (ι⊕κ) where
--   is_basis := sorry_proof
--   duality := sorry_proof

opaque foo {X} {ι : Type} [Enumtype ι] [FinVec X ι] (x : X) : X

set_option pp.all true in
#check foo (1 : ℝ)
