import SciLean.Core

open SciLean

variable
  {K} [IsROrC K]
  {X Y Z W} [Vec K X] [Vec K Y] [Vec K Z] [Vec K W]

def inv1 (f : X → Y) (y : Y) : X := sorry
def inv2 (f : X → Y) (y : Y) : X := sorry

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
            (-df'dy) := by autodiff

example : cderiv K (fun x => inv2 (f x) z)
          =
          fun x dx =>
            let y := inv2 (f x) z
            let dfdx_y := cderiv K f x dx y
            let df'dy := cderiv K (inv2 (f x)) (f x y) (dfdx_y)
            (-df'dy) := by autodiff


-- does not work
example : CDifferentiable K (fun w => inv1 (f w) y) := by fun_prop
example : CDifferentiable K (fun w => inv2 (f w)) := by fun_prop

set_option trace.Meta.Tactic.fun_trans true in
example : cderiv K (fun x => inv1 (f x) z)
          =
          fun x dx =>
            let y := inv1 (f x) z
            let dfdx_y := cderiv K f x dx y
            let df'dy := cderiv K (inv1 (f x)) (f x y) (dfdx_y)
            (-df'dy) := by fun_trans

example : cderiv K (fun x => inv2 (f x))
          =
          fun x dx z =>
            let y := inv2 (f x) z
            let dfdx_y := cderiv K f x dx y
            let df'dy := cderiv K (inv2 (f x)) (f x y) (dfdx_y)
            (-df'dy) := by autodiff
