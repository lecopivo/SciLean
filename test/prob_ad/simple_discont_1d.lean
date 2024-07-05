import SciLean.Core.Transformations.HasParamDerivWithJumps.Common
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Tactic.Autodiff

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R]

set_default_scalar R


example (w : R) :
    (fderiv R (fun w' =>
      ∫ x in Icc (0:R) 1,
        if x ≤ w' then (1:R) else 0) w 1)
    =
    if w ∈ Set.Icc 0 1 then 1 else 0 := by

  conv =>
    lhs
    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=fun_prop)




example (w : R) :
    (fwdFDeriv R (fun w' =>
      ∫ x in Icc (0:R) 1,
        if x ≤ w' then (1:R) else 0) w 1)
    =
    let interior := ∫ (x : R) in Icc 0 1, if x ≤ w then (1, 0) else (0, 0);
    let s := if w ∈ Icc 0 1 then 1 else 0;
    (interior.1, interior.2 + s) := by

  conv =>
    lhs
    rw[fwdFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=fun_prop)
    -- rw[Rand.integral_as_uniform_E_in_set R]
    -- rand_pull_E


example (w : R) :
    (fgradient (fun w' =>
      ∫ x in Icc (0:R) 1,
        if x ≤ w' then (1:R) else 0) w)
    =
    if w ∈ Icc 0 1 then 1 else 0 := by

  conv =>
    lhs
    unfold fgradient
    rw[revFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=fun_prop) [frontierGrad]
