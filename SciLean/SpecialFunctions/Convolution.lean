module

public import SciLean.Core
public import SciLean.Data.GenericArray

@[expose] public section


set_option synthInstance.maxSize 2048

def Fin.shift {n} (y : Int) (x : Fin n) : Fin n := ⟨(((x.1 + y) % n + n) % n).toNat, by
  have hn : (0 : Int) < n := by have := x.2; omega
  have h1 := Int.emod_lt_of_pos ((x.1 + y) % n + n) hn
  omega⟩

instance Fin.shift.arg_x.isInv (y : Int) : SciLean.IsInv (λ x : Fin n => x.shift y) := sorry_proof
@[simp]
theorem Fin.shift.arg_x.inv_simp {n} [Nonempty (Fin n)] (y : Int)
  : (λ x : Fin n => x.shift y)⁻¹ = (λ x : Fin n => x.shift (-y)) := by sorry_proof

def Fin.scale {n} (x : Fin n) (y : Nat) : Fin (y*n) := ⟨x.1*y, sorry_proof⟩
def Fin.scaleUp {N n : Nat} (x : Fin (N/n)) : Fin N := ⟨x.1*n, by
  have h := x.2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h
  · have h1 := Nat.div_mul_le_self N n
    have h2 : (x.1 + 1) * n ≤ N / n * n := Nat.mul_le_mul_right n h
    rw [Nat.add_mul, Nat.one_mul] at h2
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hn) (Nat.le_trans h2 h1)⟩

namespace SciLean

  instance {n} [Fact (n≠0)] : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero Fact.out⟩⟩

  def conv1d {N n} (x : Fin N → ℝ) (w : Fin n → ℝ) (b : ℝ) : Fin N → ℝ :=
     λ i => ∑ i', w i' * x (i.shift i') + b
  argument x [Fact (N≠0)] [Fact (n≠0)]
    isSmooth,
    hasAdjDiff,
    adjDiff by
      simp only [adjointDifferential, conv1d]
      simp[hold, sum_into_lambda]
      enter[x]
      rw [sum_swap]
      simp only [kron_smul_assoc, sum_of_kron_2]
      simp
  argument w [Fact (N≠0)] [Fact (n≠0)]
    isSmooth,
    hasAdjDiff,
    adjDiff by
      simp only [adjointDifferential, conv1d]
      simp[hold, sum_into_lambda]
      simp only [kron_smul_assoc, sum_of_kron_2]
      simp
  argument b [Fact (N≠0)] [Fact (n≠0)]
    isSmooth,
    hasAdjDiff,
    adjDiff by
      simp only [adjointDifferential]
      unfold conv1d; simp


  def conv2d {N M n m} (x : Fin N → Fin M → ℝ) (w : Fin n → Fin m → ℝ) (b : ℝ) : Fin N → Fin M → ℝ :=
     λ i j => ∑ i' j', w i' j' * x (i.shift i') (j.shift j') + b
  argument x [Fact (N≠0)] [Fact (M≠0)]
    isSmooth,
    hasAdjDiff,
    adjDiff by
      simp only [adjointDifferential, conv2d]
      simp[sum_into_lambda]
      enter[i,j]
      conv =>
        rw [sum_swap]; enter[1]; ext
        rw [sum_swap]; enter[1]; ext
        rw [sum_swap]; enter[1]; ext
        simp only [kron_smul_assoc, sum_of_kron_2]
        simp
      conv =>
        rw [sum_swap]; enter[1]; ext
        rw [sum_swap]; enter[1]; ext
        simp only [kron_smul_assoc, sum_of_kron_2]
        simp
      simp
  argument w [Fact (n≠0)] [Fact (m≠0)]
    isSmooth,
    hasAdjDiff,
    adjDiff by
      simp only [adjointDifferential, conv2d]
      simp[hold, sum_into_lambda]
      enter [i',j']
      conv =>
        enter [1]; ext; enter [1]; ext
        rw[sum_swap]
        simp only [kron_smul_assoc, sum_of_kron_2]
        simp
        simp only [kron_smul_assoc, sum_of_kron_2]
      simp
  argument b [Fact (N≠0)] [Fact (n≠0)]
    isSmooth,
    hasAdjDiff,
    adjDiff by
      simp only [adjointDifferential,conv2d]
      simp




  -- argument w [Fact (N≠0)] [Fact (n≠0)]
  --   hasAdjDiff,
  --   adjDiff by
  --     simp only [adjointDifferential, conv1d]
  --     simp[hold, sum_into_lambda]
  --     simp only [kron_smul_assoc, sum_of_kron_2]
  --     simp
  -- argument b [Fact (N≠0)] [Fact (n≠0)]
  --   hasAdjDiff,
  --   adjDiff by
  --     simp only [adjointDifferential]
  --     unfold conv1d; simp
