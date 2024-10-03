import SciLean

open SciLean

variable
  (K : Type _) [RCLike K]
  {W : Type _} [Vec K W]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]


-- This works
example (f : W → X → Y) (hf : Continuous (fun (w,x) => f w x)) (w : W) :
    Continuous (fun x => f w x) := by fun_prop

-- This works
example (f : W → X → Y) (hf : Continuous (fun wx : W×X => f wx.1 wx.2)) (w : W) :
    Continuous (fun x => f w x) := by fun_prop

-- This works
example (f : W → X → Y) (hf : Continuous (fun (w,x) => f w x)) (w : W) :
    Continuous (fun x => f w x) := by fun_prop
