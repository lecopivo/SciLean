import SciLean.AD.HasFwdFDeriv
import SciLean.Util.RewriteBy

open SciLean

set_default_scalar Float

opaque foo (x : ℝ) : ℝ × (ℝ → ℝ)

/--
error: failed to transform fwdFDeriv ℝ fun x =>
  let y := foo x;
  let y1 := y.1;
  y1, potential issues are:
failed to synthesize argument NormedAddCommGroup (ℝ → ℝ) when applying Prod.fst.arg_self.HasFwdFDeriv_proj_rule
---
error: failed to transform fwdFDeriv ℝ fun x =>
  let y := foo x;
  let y1 := y.1;
  y1, potential issues are:
failed to synthesize argument NormedAddCommGroup (ℝ → ℝ) when applying Prod.fst.arg_self.HasFwdFDeriv_proj_rule
---
info: fwdFDeriv ℝ fun x =>
  let y := foo x;
  let y1 := y.1;
  y1 : ℝ → ℝ → ℝ × ℝ
-/
#guard_msgs in
#check (fwdFDeriv ℝ fun x : ℝ => let y := foo x; let y1 := y.1; y1)
  rewrite_by
    simp -zeta only [fwdFDeriv_simproc]
