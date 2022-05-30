import SciLean.Mechanics
import SciLean.Operators.ODE
import SciLean.Solver 
import SciLean.Tactic.LiftLimit
import SciLean.Tactic.FinishImpl
import SciLean.Data.PowType
import SciLean.Core.Extra
import SciLean.Functions

open SciLean

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 500000

def LennardJones (ε minEnergy : ℝ) (radius : ℝ) (x : ℝ^(3:ℕ)) : ℝ :=
  let x' := ∥1/radius * x∥^{-6, ε}
  4 * minEnergy * x' * (x' - 1)
argument x [Fact (ε≠0)]
  isSmooth, diff, hasAdjDiff, adjDiff

def Coloumb (ε strength mass : ℝ) (x : ℝ^(3:ℕ)) : ℝ := - strength * mass * ∥x∥^{-1,ε}
argument x [Fact (ε≠0)]
  isSmooth, diff, hasAdjDiff, adjDiff

example (n : ℕ) (ε : ℝ) [Fact (n≠0)] [Fact (ε≠0)] (C LJ : ℝ) (r m : Idx n → ℝ)
  : (δ† λ (x : (ℝ^(3:ℕ))^n) => 
  ∑ i j, Coloumb ε C (m i * m j) (x[i] - x[j])
         +
         LennardJones ε LJ (r i + r j) (x[i] - x[j]))
   = 
   λ x dx' => PowType.intro λ i =>
     ∑ j,   Coloumb.arg_x.adjDiff ε C (m i * m j) (x[i] - x[j]) dx'
          - Coloumb.arg_x.adjDiff ε C (m j * m i) (x[j] - x[i]) dx'
          + (  LennardJones.arg_x.adjDiff ε LJ (r i + r j) (x[i] - x[j]) dx'
             - LennardJones.arg_x.adjDiff ε LJ (r j + r i) (x[j] - x[i]) dx') :=
by
  simp; unfold hold; simp;
  simp [sum_into_lambda]
  simp [← sum_of_add]
  done


def H (n : ℕ) (ε : ℝ) (C LJ : ℝ) (r m : Idx n → ℝ) (x p : (ℝ^(3:ℕ))^n) : ℝ :=
  (∑ i, (1/(2*m i)) * ∥p[i]∥²)
  +
  ∑ i j,   Coloumb ε C (m i * m j) (x[i] - x[j])
         + LennardJones ε LJ (r i + r j) (x[i] - x[j])
argument p [Fact (n≠0)] [Fact (ε≠0)]
  isSmooth, diff, hasAdjDiff, adjDiff
argument x [Fact (n≠0)] [Fact (ε≠0)]
  isSmooth, diff, hasAdjDiff, 
  adjDiff by
    simp[H]; unfold hold; simp; unfold hold; simp;
    simp [sum_into_lambda]
    simp [← sum_of_add]
