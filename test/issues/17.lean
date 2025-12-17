import SciLean

open SciLean

variable
  {K} [RCLike K]
  {X} [NormedAddCommGroup X] [NormedSpace K X]
  {Y} [NormedAddCommGroup Y] [NormedSpace K Y]
  (f : X → Y) (x dx : X)

set_default_scalar K

/-- info: (∂> (x':=x;dx), f x').2 : Y -/
#guard_msgs in
#check
  (fwdFDeriv K (fun x' => f x') x dx).snd
  rewrite_by let_normalize
