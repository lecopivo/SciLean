import SciLean.FTrans.FwdDeriv.Basic

import SciLean.Tactic.LSimp.Notation
import SciLean.Tactic.LetEnter
import SciLean.Tactic.Basic


open SciLean

variable
  {K : Type _} [NontriviallyNormedField K] 

example
  : fwdDeriv K `normal Unit (fun x : K => x + x + x + x + x)
    =
    fun x dx => 
     (x + x + x + x + x, dx + dx + dx + dx + dx):= 
by
  conv =>
    lhs
    ftrans only
    enter [x,dx]
    simp (config := { zeta := false}) only [Prod.add_def]
    ftrans only
  
#exit

example
  : fwdDeriv K `normal Unit (fun x : K => x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x)
    =
    fun x dx => 
     (x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x, 
      dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx):= 
by
  ftrans
