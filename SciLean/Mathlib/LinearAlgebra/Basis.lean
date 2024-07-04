import Mathlib.Algebra.Module.Defs
import Mathlib.LinearAlgebra.Basis

import SciLean.Util.SorryProof

variable (ι R M : Type*)
variable [Semiring R]
variable [AddCommMonoid M] [Module R M]

/-- A `Basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.

Unlike mathlib's `Basis` this is computable version i.e. for `b : Basis' ι R M` getting the i-th
basis bector `b i` is computable function. -/
structure Basis' extends Basis ι R M where
  vec : ι → M
  vec_is_basis_vec : ∀ i, vec i = toBasis i

class CanonicalBasis (ι : outParam Type*) (R : Type*) (M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
  extends Basis' ι R M

variable {ι R M}


instance : Coe (Basis' ι R M) (Basis ι R M) := ⟨fun b => b.toBasis⟩
instance : Coe (CanonicalBasis ι R M) (Basis' ι R M) := ⟨fun b => b.toBasis'⟩
instance : Coe (CanonicalBasis ι R M) (Basis ι R M) := ⟨fun b => b.toBasis'.toBasis⟩

namespace Basis'

open Function in
theorem repr_injective : Injective (Basis'.toBasis : Basis' ι R M → _root_.Basis ι R M) := fun f g h => by
  cases f; cases g;
  simp_all only [mk.injEq, true_and]
  subst h
  ext1 x
  simp_all only

/-- `b i` is the `i`th basis vector.

This function is computable unlike mathlib's `b i` for `b : Basis ι R M`. -/
instance instFunLike : FunLike (Basis' ι R M) ι M where
  coe b i := b.vec i
  coe_injective' f g h := by
    apply repr_injective
    ext i;
    rw[← f.vec_is_basis_vec, ← g.vec_is_basis_vec]
    apply (congr_fun h)

-- It gives trouble to noncomputable checker if not marked as inlined
@[inline]
def coord (b : Basis' ι R M) (i : ι) (x : M) : R := b.repr x i

end Basis'

def canonicalBasis [b : CanonicalBasis ι R M] : Basis' ι R M := b

namespace CanonicalBasis

instance instFunLike' : FunLike (CanonicalBasis ι R M) ι M where
  coe b i := b.toBasis' i
  coe_injective' f g h := by
    cases f; cases g; congr
    apply Basis'.repr_injective
    ext i;
    simp only [← Basis'.vec_is_basis_vec]
    apply (congr_fun h)


instance [DecidableEq R] : CanonicalBasis Unit R R where
  toBasis' := {
    toBasis := {
      repr := {
        toFun := fun x => {
          toFun := fun _ => x
          support := if x ≠ 0 then ⊤ else ⊥
          mem_support_toFun := by aesop
        }
        invFun := fun x => x ()
        map_add' := by intros; ext; simp
        map_smul' := by intros; ext; simp
        left_inv := by intros _; simp
        right_inv := by intros _; ext; simp
      }
    }
    vec := fun _ => 1
    vec_is_basis_vec := by simp
    }


instance (priority:=high)
  {I} [DecidableEq I]
  {J} [DecidableEq J]
  [AddCommMonoid X] [Module R X]
  [AddCommMonoid Y] [Module R Y]
  [p : CanonicalBasis I R X] [q : CanonicalBasis J R Y] : CanonicalBasis (I⊕J) R (X×Y) where
  toBasis' := {
    toBasis := {
      repr := {
        toFun := fun (x,y) => {
          toFun := fun ij =>
            match ij with
            | .inl i => p.repr x i
            | .inr j => q.repr y j
          support :=
            let I' := ((p.repr x).support.map
              ⟨fun i : I => Sum.inl (β:=J) i, by intros _; simp only [Sum.inl.injEq, imp_self, implies_true]⟩)
            let J' := ((q.repr y).support.map
              ⟨fun j : J => Sum.inr (α:=I) j, by intros _; simp only [Sum.inr.injEq, imp_self, implies_true]⟩)
            I' ∪ J'
          mem_support_toFun := by
            intro a
            simp_all only [Finset.mem_union, Finset.mem_map, Finsupp.mem_support_iff, ne_eq, Function.Embedding.coeFn_mk]
            rcases a with ⟨val⟩ | ⟨val_1⟩
            · simp_all only [Sum.inl.injEq, exists_eq_right, and_false, exists_false, or_false]
            · simp_all only [and_false, exists_false, Sum.inr.injEq, exists_eq_right, false_or]
        }
        invFun :=
          fun xy =>
            -- the support is not correct but to preserve computability we can't assign sorry there
            let x : I →₀ R := ⟨∅, fun i => xy.toFun (.inl i), sorry_proof⟩
            let y : J →₀ R := ⟨∅, fun j => xy.toFun (.inr j), sorry_proof⟩
            (p.repr.symm x, q.repr.symm y)
        map_add'  := sorry_proof
        map_smul' := sorry_proof
        left_inv  := sorry_proof
        right_inv := sorry_proof
      }
    }
    vec := fun ij =>
      match ij with
      | .inl i => (p.vec i, 0)
      | .inr j => (0, q.vec j)
    vec_is_basis_vec := sorry_proof
    }



end CanonicalBasis
