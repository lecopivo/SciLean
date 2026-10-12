module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.MeanInequalities

public import SciLean.Meta.SimpAttr
public import SciLean.Util.SorryProof

@[expose] public section


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
  dist x y :=
    let x := x.ofLp; let y := y.ofLp
    ((distP p x.1 y.1)^p.toReal +
     (distP p x.2 y.2)^p.toReal)^(1/p.toReal)


/-- Monotonicity of `(a^t + b^t)^(1/t)` in both arguments. -/
private theorem lp2_mono {t : ℝ} (ht : 0 < t) {a b a' b' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haa : a ≤ a') (hbb : b ≤ b') :
    (a^t + b^t)^(1/t) ≤ (a'^t + b'^t)^(1/t) :=
  Real.rpow_le_rpow (by positivity)
    (add_le_add (Real.rpow_le_rpow ha haa ht.le) (Real.rpow_le_rpow hb hbb ht.le)) (by positivity)

/-- Minkowski inequality for two summands. -/
private theorem lp2_add_le {t : ℝ} (ht : 1 ≤ t) {a b a' b' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b') :
    ((a+a')^t + (b+b')^t)^(1/t) ≤ (a^t + b^t)^(1/t) + (a'^t + b'^t)^(1/t) := by
  have h := Real.Lp_add_le_of_nonneg (s := (Finset.univ : Finset (Fin 2)))
    (f := ![a,b]) (g := ![a',b']) ht (by intro i _; fin_cases i <;> simpa)
    (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

private theorem one_le_toReal {p : ENNReal} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) : 1 ≤ p.toReal := by
  simpa using ENNReal.toReal_mono hpt hp1

/-- The `Lp` metric on a product.

Note: as the comment on the `Dist` instance above says, the formula is incorrect for `p = 0` and
`p = ∞`, where it does not define a metric at all (e.g. `dist x x = 1` there). The two `Fact`
assumptions `1 ≤ p` and `p ≠ ∞` were therefore added to the original statement; with them all the
metric space laws are proved. -/
noncomputable
instance {X} {Y} [Fact (1 ≤ p)] [Fact (p ≠ ⊤)]
    [a : MetricSpace (WithLp p X)] [b : MetricSpace (WithLp p Y)] :
    MetricSpace (WithLp p (X×Y)) where
  dist_self := by
    have ht : 1 ≤ p.toReal := one_le_toReal Fact.out Fact.out
    intro x
    show ((distP p x.ofLp.1 x.ofLp.1)^p.toReal + (distP p x.ofLp.2 x.ofLp.2)^p.toReal)^(1/p.toReal)
         = 0
    simp only [distP, dist_self]
    rw [Real.zero_rpow (by linarith), add_zero, Real.zero_rpow (by positivity)]
  dist_comm := by intro x y; show (_ + _)^_ = (_ + _)^_; simp only [distP, dist_comm]
  dist_triangle := by
    have ht : 1 ≤ p.toReal := one_le_toReal Fact.out Fact.out
    intro x y z
    show ((distP p x.ofLp.1 z.ofLp.1)^p.toReal + (distP p x.ofLp.2 z.ofLp.2)^p.toReal)^(1/p.toReal)
         ≤ ((distP p x.ofLp.1 y.ofLp.1)^p.toReal + (distP p x.ofLp.2 y.ofLp.2)^p.toReal)^(1/p.toReal)
           + ((distP p y.ofLp.1 z.ofLp.1)^p.toReal
              + (distP p y.ofLp.2 z.ofLp.2)^p.toReal)^(1/p.toReal)
    refine le_trans (lp2_mono (t := p.toReal) (by linarith) dist_nonneg dist_nonneg
      (dist_triangle ((WithLp.equiv p X).symm x.ofLp.1) ((WithLp.equiv p X).symm y.ofLp.1)
        ((WithLp.equiv p X).symm z.ofLp.1))
      (dist_triangle ((WithLp.equiv p Y).symm x.ofLp.2) ((WithLp.equiv p Y).symm y.ofLp.2)
        ((WithLp.equiv p Y).symm z.ofLp.2))) ?_
    exact lp2_add_le ht dist_nonneg dist_nonneg dist_nonneg dist_nonneg
  edist_dist := by intro x y; exact ENNReal.coe_nnreal_eq _
  eq_of_dist_eq_zero := by
    have ht : 1 ≤ p.toReal := one_le_toReal Fact.out Fact.out
    intro x y h
    have h' : ((distP p x.ofLp.1 y.ofLp.1)^p.toReal
               + (distP p x.ofLp.2 y.ofLp.2)^p.toReal)^(1/p.toReal) = 0 := h
    have hsum : (distP p x.ofLp.1 y.ofLp.1)^p.toReal
                + (distP p x.ofLp.2 y.ofLp.2)^p.toReal = 0 := by
      by_contra hne
      have hpos : 0 < (distP p x.ofLp.1 y.ofLp.1)^p.toReal
                      + (distP p x.ofLp.2 y.ofLp.2)^p.toReal :=
        lt_of_le_of_ne (by positivity) (Ne.symm hne)
      have hlt := Real.rpow_pos_of_pos hpos (1/p.toReal)
      rw [h'] at hlt
      exact lt_irrefl _ hlt
    have hz := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).1 hsum
    have e1 : distP p x.ofLp.1 y.ofLp.1 = 0 :=
      ((Real.rpow_eq_zero_iff_of_nonneg dist_nonneg).1 hz.1).1
    have e2 : distP p x.ofLp.2 y.ofLp.2 = 0 :=
      ((Real.rpow_eq_zero_iff_of_nonneg dist_nonneg).1 hz.2).1
    have p1 : x.ofLp.1 = y.ofLp.1 := by
      simpa using congrArg WithLp.ofLp (eq_of_dist_eq_zero e1)
    have p2 : x.ofLp.2 = y.ofLp.2 := by
      simpa using congrArg WithLp.ofLp (eq_of_dist_eq_zero e2)
    exact (WithLp.ext_iff p).mpr (Prod.ext p1 p2)


@[simp, simp_core]
theorem dist_sqrt (x y : ℝ) : (x^2 + y^2).sqrt^2 = x^2 + y^2 :=
  Real.sq_sqrt (by positivity)
