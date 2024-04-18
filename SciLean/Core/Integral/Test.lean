import SciLean.Tactic.RefinedSimp
import SciLean.Tactic.IfPull


import SciLean.Core.Integral.MovingDomain

open Lean Meta


namespace SciLean


-- private def argumentIndex (declName : Name) (argName : Name) : MetaM (Option Nat) := do

--   let info ← getConstInfo declName

--   forallTelescope info.type fun xs _ =>
--     xs.findIdxM? (fun x => do let name ← x.fvarId!.getUserName; return name == argName)


-- -- open Tactic.RefinedSimp in
-- #eval show MetaM Unit from do
--   let .some n ← argumentIndex ``cintegral.arg_fμ.cderiv_rule `A | throwError "invalid theorem"
--   addTheorem ``cintegral.arg_fμ.cderiv_rule .global 1000 false #[(n,.notConst)]

--   let .some n ← argumentIndex ``cintegral.arg_fμ.fwdDeriv_rule `A | throwError "invalid theorem"
--   addTheorem ``cintegral.arg_fμ.fwdDeriv_rule .global 1000 false #[(n,.notConst)]

-- attribute [rsimp ↓ guard A .notConst] cintegral.arg_fμ.cderiv_rule cintegral.arg_fμ.fwdDeriv_rule


open MeasureTheory

variable
  {R} [RealScalar R]
  {W} [Vec R W]
  {X} [SemiHilbert R X] [MeasureSpace X]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z] [Module ℝ Z]

set_default_scalar R

example (f : W → X → Y) (A : W → Set X)
    (hA : IsLipschitzDomain {wx : W×X | wx.2 ∈ A wx.1}) :
    (∂ w, ∫' x in A w, f w x)
    =
    fun w dw =>
      let ds := movingFrontierIntegral R A ⊤ (f w) w dw
      let di := ∂ (w':=w;dw), ∫' x in A w, f w' x
      ds + di := by

  conv =>
    lhs
    -- simp (disch:=sorry) only [cintegral.arg_fμ.cderiv_rule]
    simp (config:={zeta:=false}) (disch:=assumption) only [↓ refinedRewritePre, ↑ refinedRewritePost]


open Set
variable [MeasureSpace R]

#check (∂ w : R, ∫' x in Icc (0:R) 1, if x ≤ w then w*x else w + x)
  rewrite_by
    unfold scalarCDeriv
    fun_trans (config:={zeta:=false}) (disch:=assumption) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc]



#check (∂ t : R, ∫' x in Icc (0:R) 1, if x ≤ t then t*x else t + x)
  rewrite_by
    unfold scalarCDeriv
    fun_trans (config:={zeta:=false}) (disch:=assumption) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc]



#check (∂ t : R, ∫' (xy : R×R) in (Icc 0 1).prod (Icc 0 1), if xy.1 + xy.2 ≤ t then xy.1 * xy.2 * t else xy.1 + xy.2 + t)
  rewrite_by
    unfold scalarCDeriv
    fun_trans (config:={zeta:=false}) (disch:=assumption) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc]



#check (∂ t : R, ∫' (xy : R×R) in (Icc 0 1).prod (Icc 0 1), if xy.1 ≤ t then (-if xy.2 ≤ t then (1:R) else 0) else (if xy.1 + xy.2 ≤ t then t else t*t))
  rewrite_by
    unfold scalarCDeriv
    fun_trans (config:={zeta:=false}) (disch:=assumption) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc, Tactic.if_pull]
    fun_trans (config:={zeta:=false}) (disch:=assumption) only
      [↑ Tactic.if_pull]
