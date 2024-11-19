import SciLean

open SciLean

variable
  {K} [RCLike K]
  {X Y} [Vec K X] [Vec K Y]
  (f : X → Y) (x dx : X)

set_default_scalar K

/-- info: (fwdCDeriv K (fun x' => f x') x dx).2 : Y -/
#guard_msgs in
#check
  (fwdCDeriv K (fun x' => f x') x dx).snd
  rewrite_by let_normalize
