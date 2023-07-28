import SciLean.FTrans.Broadcast.Basic

open SciLean

variable   
  {R : Type _} [Ring R]
  {X : Type _} [AddCommGroup X] [Module R X]
  {Y : Type _} [AddCommGroup Y] [Module R Y]


example (r : R)
  : broadcast `Prod R (Fin 3) (fun x : X => r • x)
    =
    fun ((x,y,z) : X×X×X) => (r•x, r•y, r•z) :=
by
  ftrans; funext (x,y,z); simp


example (r : R)
  : broadcast `Prod R (Fin 3) (fun s : R => r * s)
    =
    fun ((x,y,z) : R×R×R) => (r*x, r*y, r*z) :=
by
  ftrans; funext (x,y,z); simp


