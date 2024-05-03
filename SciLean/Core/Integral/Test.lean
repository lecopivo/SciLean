import SciLean.Tactic.RefinedSimp
import SciLean.Tactic.IfPull
import SciLean.Core.FloatAsReal


import SciLean.Core.Integral.HasDerivUnderIntegral

open Lean Meta


namespace SciLean


open MeasureTheory

variable
  {R : Type} [RealScalar R]
  {W : Type} [Vec R W]
  {X : Type} [SemiHilbert R X] [MeasureSpace X]
  {Y : Type} [Vec R Y] [Module ℝ Y]
  {Z : Type} [Vec R Z] [Module ℝ Z]

set_default_scalar R

variable [MeasureSpace R]


variable (t : R)

example : (((HasDerivUnderIntegralAt R (fun w' x : R => w' + x)
            (volume.restrict (Set.Icc (0:R) 1)) t _ _)) rewrite_by gtrans; fun_trans)
          =
          True := by sorry


#check (HasDerivUnderIntegralAt R (fun w' x : R => if x ≤ w' then (1:R) else 0)
            (volume.restrict (Set.Icc (0:R) 1)) t _ _) rewrite_by gtrans; autodiff

#check Set.indicator

-- WARRNING: this is inconsistent as it is true only almost everywhere but we do not have good
--           automation to handle almost everywhere rewrites
open Classical in
@[ftrans_simp]
theorem rnDeriv_restrict {X} [MeasurableSpace X] (μ ν : Measure X) (A : Set X) :
  (μ.restrict A).rnDeriv ν
  =
  fun x => (μ.rnDeriv ν x) * (if x ∈ A then 1 else 0) := sorry_proof

-- WARRNING: this is inconsistent as it is true only almost everywhere but we do not have good
--           automation to handle almost everywhere rewrites
-- This is pointwise version of: MeasureTheorey.Measure.rnDeriv_self
open Classical in
@[ftrans_simp]
theorem rnDeriv_self {X} [MeasurableSpace X] (μ : Measure X) :
  μ.rnDeriv μ
  =
  fun _ => 1 := sorry_proof


open BigOperators in
@[ftrans_simp]
theorem cintegral_surfaceMeasure_zero (A : Set X) (f : X → Y) :
  ∫' x in A, f x ∂(surfaceMeasure (no_index 0)) = ∑' x, f x := sorry



attribute [ftrans_simp] Measure.restrict_singleton

@[ftrans_simp]
theorem surfaceMeasure_zero_singleton (x : X) :
  surfaceMeasure 0 {x} = 1 := sorry_proof

@[ftrans_simp]
theorem ite_same (c : Prop) [Decidable c] (a : α) : (if c then a else a) = a := by if h : c then simp[h] else simp[h]


set_option trace.Meta.Tactic.fun_trans true
set_option trace.Meta.Tactic.fun_trans.unify true
set_option trace.Meta.Tactic.fun_trans.step true
set_option trace.Meta.Tactic.fun_trans.discharge true
set_option trace.Meta.Tactic.simp.rewrite true



#check (movingFrontierIntegral R (fun x => x * t - (x + t)) (fun w => {x | x ≤ w}) (volume.restrict (Set.Icc 0 1)) t 1) rewrite_by
  autodiff
  unfold scalarGradient
  autodiff


#check (HasDerivUnderIntegralAt R (fun w' x : R => if x ≤ w' then x*w' else x+w')
            (volume.restrict (Set.Icc (0:R) 1)) t _ _) rewrite_by gtrans; autodiff; autodiff


open Set

set_option trace.Meta.Tactic.gtrans true
set_option trace.Meta.Tactic.fun_prop true
-- set_option trace.Meta.Tactic.gtrans.candidates true
-- set_option trace.Meta.Tactic.gtrans.normalize true


-- open Qq Lean Meta in
-- #eval show MetaM Unit from do

--   let f' ← mkFreshExprMVarQ q(Float → Float → Float)
--   let sf ← mkFreshExprMVarQ q(Float → Float)
--   let e := q(HasDerivUnderIntegralAt Float (fun w' x : Float => if x ≤ w' then (1:Float) else 0) (volume.restrict (Icc 0 1)) (1:Float) $f' $sf)

--   let .some prf ← Tactic.GTrans.gtrans 100 e
--     | throwError "failed"


--   if (← instantiateMVars prf).hasMVar then
--     let mvars := (← instantiateMVars prf).collectMVars {} |>.result
--     throwError "resulting proof has mvars: {← mvars.mapM (fun m => m.getType >>= ppExpr)}!"
--   else
--     IO.println "proof ok"

--   pure ()


#check (∂ (w:=(1:R)), ∫' x in Icc (0:R) 1, if x ≤ w then (1:R) else 0)
  rewrite_by
    fun_trans (config:={zeta:=false}) (disch:=first | assumption | gtrans) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc]
    autodiff



#check (∂ (w:=(1:R)), ∫' x in Icc (0:R) 1, if x ≤ w then w*x else w + x)
  rewrite_by
    fun_trans (config:={zeta:=false}) (disch:=first | assumption | gtrans) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc]
    autodiff


#check (∂ (w:=(1:R)), ∫' x in Icc (0:R) 1, if x ≤ w then if 2*w + 3*x ≤ 0 then 5*w*x else 2*w*w*x else w + x)
  rewrite_by
    fun_trans (config:={zeta:=false}) (disch:=first | assumption | gtrans) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc]
    autodiff


set_option pp.funBinderTypes true

#check (∂ (w:=(1:R)), ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1, if y ≤ w then (1:R) else 0)
  rewrite_by
    fun_trans (config:={zeta:=false}) (disch:=first | assumption | gtrans) only
      [↓ refinedRewritePre, ↑ refinedRewritePost, ftrans_simp, Tactic.lift_lets_simproc]
    autodiff



#exit


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
