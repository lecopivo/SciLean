import SciLean

open SciLean

variable 
  {K} [IsROrC K]
  {X Y} [Vec K X] [Vec K Y]
  (f : X → Y) (x dx : X)

set_default_scalar K

/--
info: (∂> (x':=x;dx), f x').snd : Y
-/
#guard_msgs in
#check 
  (∂> (x':=x;dx), f x').snd
  rewrite_by autodiff; let_normalize
