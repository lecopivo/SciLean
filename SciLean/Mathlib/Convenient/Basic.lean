import SciLean.Core.Vec

namespace SciLean.Mathlib.Convenient

  variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

  opaque is_smooth (f : X → Y) : Prop

  noncomputable 
  opaque derivative (f : X → Y) (h : is_smooth f) (x dx : X) : Y

  opaque is_smooth_at (f : X → Y) (x : X) : Prop

  opaque integrate [Vec X] (a b : ℝ) (f : ℝ → X) (h : is_smooth f) : X
  
end SciLean.Mathlib.Convenient
