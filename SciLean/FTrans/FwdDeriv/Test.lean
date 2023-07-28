import SciLean.FTrans.FwdDeriv.Basic

open SciLean

variable
  {K : Type _} [NontriviallyNormedField K] 

example
  : fwdDeriv K (fun x : K => x + x + x + x + x)
    =
    fun x dx => 
     (x + x + x + x + x, dx + dx + dx + dx + dx):= 
by
  conv =>
    lhs
    ftrans only
    enter [x,dx]
    simp (config := { zeta := false}) only [Prod.add_def]

#exit  

example
  : fwdDeriv K (fun x : K => x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x)
    =
    fun x dx => 
     (x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x, 
      dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx):= 
by
  ftrans
