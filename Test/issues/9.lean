import SciLean

open SciLean

set_option deprecated.oldSectionVars true

variable
  {K} [RCLike K]
  {X} [Vec K X] [Vec K Y] [Vec K Z] [Vec K W]

opaque inv1 [Inhabited X] (f : X → Y) (y : Y) : X
opaque inv2 [Inhabited X] (f : X → Y) (y : Y) : X

variable (f : X → Y → Z) (z : Z)

@[fun_prop]
theorem inv1.arg_f.CDifferentiable_rule
  : CDifferentiable K (fun x => inv1 (f x)) := sorry_proof

@[fun_trans]
theorem inv1.arg_f.cderiv_rule
  : cderiv K (fun x => inv1 (f x))
    =
    fun x dx z =>
      let y := inv1 (f x) z
      let dfdx_y := cderiv K f x dx y
      let df'dy := cderiv K (inv1 (f x)) (f x y) (dfdx_y)
      (-df'dy) := sorry_proof

@[fun_prop]
theorem inv2.arg_f.CDifferentiable_rule
  : CDifferentiable K (fun w => inv2 (f w) y) := sorry_proof

@[fun_trans]
theorem inv2.arg_f.cderiv_rule
  : cderiv K (fun x => inv2 (f x) z)
    =
    fun x dx =>
      let y := inv2 (f x) z
      let dfdx_y := cderiv K f x dx y
      let df'dy := cderiv K (inv2 (f x)) (f x y) (dfdx_y)
      (-df'dy) := sorry_proof


-- works
example : CDifferentiable K (fun w => inv1 (f w)) := by fun_prop
example : CDifferentiable K (fun w => inv2 (f w) y) := by fun_prop

example : cderiv K (fun x => inv1 (f x))
          =
          fun x dx z =>
            let y := inv1 (f x) z
            let dfdx_y := cderiv K f x dx y
            let df'dy := cderiv K (inv1 (f x)) (f x y) (dfdx_y)
            (-df'dy) := by autodiff; simp


example : cderiv K (fun x => inv2 (f x) z)
          =
          fun x dx =>
            let y := inv2 (f x) z
            let dfdx_y := cderiv K f x dx y
            let df'dy := cderiv K (inv2 (f x)) (f x y) (dfdx_y)
            (-df'dy) := by autodiff; simp


example : CDifferentiable K (fun w => inv1 (f w) y) := by fun_prop
example : CDifferentiable K (fun w => inv2 (f w)) := by fun_prop

example : cderiv K (fun x => inv2 (f x))
          =
          fun x dx z =>
            let y := inv2 (f x) z
            let dfdx_y := cderiv K f x dx y
            let df'dy := cderiv K (inv2 (f x)) (f x y) (dfdx_y)
            (-df'dy) := by autodiff; simp

-- does not work
example : cderiv K (fun x => inv1 (f x) z)
          =
          fun x dx =>
            let y := inv1 (f x) z
            let dfdx_y := cderiv K f x dx y
            let df'dy := cderiv K (inv1 (f x)) (f x y) (dfdx_y)
            (-df'dy) := by autodiff; simp; sorry_proof -- fix this
