import SciLean.Core
import SciLean.Tactic.GTrans
import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.PlaneDecomposition

open SciLean


variable
  {R} [RealScalar R]

set_default_scalar R


example (s y : R) :
  (gtrans_output (ParametricInverseAt (fun x : R => x - s) y _ _ _) by gtrans; fun_trans)
  =
  (Unit, fun _ => Unit, fun _ => R,
   fun _ _ x => x,
   fun _ _ => y + s,
   fun _ => ⊤) := by rfl


example (s y : R) :
  (gtrans_output (ParametricInverseAt (fun x : R => x + s) y _ _ _) by gtrans; fun_trans)
  =
  (Unit, fun _ => Unit, fun _ => R,
   fun _ _ x => x,
   fun _ _ => y - s,
   fun _ => ⊤) := by rfl


variable [PlainDataType R]

example (s y : R) :
  (gtrans_output (ParametricInverseAt (fun (x : R × R) => x.2 - s) y _ _ _) by gtrans; autodiff; autodiff)
  =
  (Unit, fun _ => DataArrayN R (Fin 1), fun _ => R,
   fun _ (y : R^[1]) t => (planeDecomposition (0,1) (by simp)) (t, y),
   fun _ _ => y + s,
   fun x => ⊤) := by simp


example (s y : R) :
  (gtrans_output (ParametricInverseAt (fun (x : R × R) => 2 * x.1 + 3 * x.2 - s) y _ _ _) by gtrans; autodiff; autodiff)
  =
  (Unit, fun _ => DataArrayN R (Fin 1), fun _ => R,
   fun _ (y : R^[1]) t => (planeDecomposition (2,3) (by simp)) (t, y),
   fun _ _ => (y + s) / Scalar.sqrt (2^2 + 3^2),
   fun x => ⊤) := by simp
