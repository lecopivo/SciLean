import SciLean.Core
import SciLean.Tactic.GTrans
import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.PlaneDecomposition

open SciLean


variable
  {R} [RealScalar R]

set_default_scalar R


set_option trace.Meta.Tactic.gtrans true


example (s y : R) :
  (gtrans_output (ParametricInverseAt (fun x : R => x - s) y _ _ _) by
    gtrans (disch:=fun_prop); fun_trans)
  =
  (Unit, fun _ => Unit, fun _ => R,
   fun _ _ x => x,
   fun _ _ => y + s,
   fun _ => ⊤) := by rfl


example (s y : R) :
  (gtrans_output (ParametricInverseAt (fun x : R => x + s) y _ _ _) by
    gtrans (disch:=fun_prop); fun_trans)
  =
  (Unit, fun _ => Unit, fun _ => R,
   fun _ _ x => x,
   fun _ _ => y - s,
   fun _ => ⊤) := by rfl

set_option trace.Meta.Tactic.gtrans.arg true in

example (a b c : R) (ha : a ≠ 0) :
  (gtrans_output (ParametricInverseAt (fun x => a * x + b - c * w) y _ _ _) by
    gtrans (disch:=fun_prop (disch:=assumption)); fun_trans (disch:=assumption))
  =
  (Unit, fun _ => Unit, fun _ => R,
   fun _ _ x => x,
   fun _ _ => a⁻¹ * (y + c * w - b),
   fun _ => ⊤) := by rfl



variable [PlainDataType R]

example (s y : R) :
  (gtrans_output (ParametricInverseAt (fun (x : R × R) => x.2 - s) y _ _ _) by
    gtrans (disch := fun_prop); autodiff; autodiff)
  =
  (Unit, fun _ => DataArrayN R (Fin 1), fun _ => R,
   fun _ (y : R^[1]) t => (planeDecomposition (0,1) (by simp)) (t, y),
   fun _ _ => y + s,
   fun x => ⊤) := by simp


example (s y : R) :
  (gtrans_output (ParametricInverseAt (fun (x : R × R) => 2 * x.1 + 3 * x.2 - s) y _ _ _) by
    gtrans (disch:=fun_prop); autodiff; autodiff)
  =
  (Unit, fun _ => DataArrayN R (Fin 1), fun _ => R,
   fun _ (y : R^[1]) t => (planeDecomposition (2,3) (by simp)) (t, y),
   fun _ _ => (y + s) / Scalar.sqrt (2^2 + 3^2),
   fun x => ⊤) := by simp
