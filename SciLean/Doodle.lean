import SciLean
open SciLean

def shift {X} [Add X] (u : X) (f : X → Y) (x : X) := f (x + u)

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W]

set_option trace.Meta.Tactic.fun_trans true in
set_option trace.Meta.Tactic.simp.rewrite true in
theorem shift_fwdFDeriv (t : W → ℝ) (f : W → ℝ → ℝ) (x : W → ℝ)
    (ht : Differentiable ℝ t) (hf : Differentiable ℝ (fun (w,r) => f w r))
    (hx : Differentiable ℝ x) :
    fwdFDeriv ℝ (fun w => shift (t w) (f w) (x w))
    =
    fun w dw =>
      let df := fun x dx => fwdFDeriv ℝ (fun (w',x') => f w' x') (w,x) (dw,dx)
      let (tw,dt) := fwdFDeriv ℝ t w dw
      let (xw,dx) := fwdFDeriv ℝ x w dw
      shift tw (df · (dx + dt)) xw := by
  funext w dw
  unfold shift
  conv => lhs; lautodiff
  simp


#check Prod.fst_add


#print axioms shift_fwdFDeriv



#print axioms SciLean.FwdFDeriv.apply_rule


#print axioms SciLean.FwdFDeriv.Prod.mk.arg_fstsnd.fwdFDeriv_rule_at

#print axioms SciLean.FwdFDeriv.comp_rule_at

#print axioms SciLean.FwdFDeriv.HAdd.hAdd.arg_a0a1.fwdFDeriv_rule_at
#print axioms SciLean.FwdFDeriv.id_rule
