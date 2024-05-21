import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.NormedSpace.WithLp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import SciLean.Util.SorryProof

abbrev MetricSpaceP (X : Type _) (p) := MetricSpace (WithLp p X)

abbrev Metric.pball (p) [MetricSpace (WithLp p α)] (x : α) (ε : ℝ) : Set α :=
  (WithLp.equiv p _) '' Metric.ball ((WithLp.equiv p _).symm x) ε

abbrev Metric.pclosedBall (p) [MetricSpace (WithLp p α)] (x : α) (ε : ℝ) : Set α :=
  (WithLp.equiv p _) '' Metric.closedBall ((WithLp.equiv p _).symm x) ε


abbrev pdist {X} (p) [Dist (WithLp p X)] (x y : X) :=
  dist ((WithLp.equiv p _).symm x) ((WithLp.equiv p _).symm y)


-- This is incorrect for `p = ∞` and `p = 0` !!!
noncomputable
instance [Dist (WithLp p α)] [Dist (WithLp p β)] : Dist (WithLp p (α×β)) where
  dist := fun (x,y) (x',y') => ((pdist p x x')^p.toReal +
                                (pdist p y y')^p.toReal)^(1/p.toReal)


noncomputable
instance {X} {Y} [a : MetricSpace (WithLp p X)] [b : MetricSpace (WithLp p Y)] :
    MetricSpace (WithLp p (X×Y)) where
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  edist_dist := sorry_proof
  eq_of_dist_eq_zero := sorry_proof
