import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import SciLean.Meta.SimpAttr
import SciLean.Util.SorryProof

abbrev MetricSpaceP (X : Type _) (p) := MetricSpace (WithLp p X)

abbrev Metric.ballP (p) [MetricSpace (WithLp p α)] (x : α) (ε : ℝ) : Set α :=
  (WithLp.equiv p _) '' Metric.ball ((WithLp.equiv p _).symm x) ε

abbrev Metric.closedBallP (p) [MetricSpace (WithLp p α)] (x : α) (ε : ℝ) : Set α :=
  (WithLp.equiv p _) '' Metric.closedBall ((WithLp.equiv p _).symm x) ε


/-- Distance in Lp norm.

Function `dist` usually returns distance in maximum norm but often we need euclidean distance
i.e. L2 norm. -/
abbrev distP {X} (p) [Dist (WithLp p X)] (x y : X) :=
  dist ((WithLp.equiv p _).symm x) ((WithLp.equiv p _).symm y)


-- This is incorrect for `p = ∞` and `p = 0` !!!
noncomputable
instance [Dist (WithLp p α)] [Dist (WithLp p β)] : Dist (WithLp p (α×β)) where
  dist := fun (x,y) (x',y') => ((distP p x x')^p.toReal +
                                (distP p y y')^p.toReal)^(1/p.toReal)


noncomputable
instance {X} {Y} [a : MetricSpace (WithLp p X)] [b : MetricSpace (WithLp p Y)] :
    MetricSpace (WithLp p (X×Y)) where
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  edist_dist := sorry_proof
  eq_of_dist_eq_zero := sorry_proof


@[simp, simp_core]
theorem dist_sqrt (x y : ℝ) : (x^2 + y^2).sqrt^2 = x^2 + y^2 := sorry_proof
