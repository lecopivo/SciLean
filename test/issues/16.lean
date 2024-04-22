import SciLean

open SciLean

example : CDifferentiable ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z) := by fun_prop

example
  : (cderiv ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z))
    =
    fun (_,_,_) (_,_,dz) => dz := by fun_trans only

example
  : CDifferentiable Float (fun x : Float => ⊞ (_ : Fin 10) => x) :=
by
  fun_prop [SciLean.introElemNotation]

example
  : cderiv Float (fun x : Float => ⊞ (_ : Fin 10) => x)
    =
    fun x dx => ⊞ (_ : Fin 10) => dx :=
by
  fun_trans[Function.HasUncurry.uncurry]
  sorry -- fix this!!!

example (f : Nat ≃ Nat)
  : Function.Bijective (fun x => f x) := by fun_prop

example (f : Nat ≃ Nat)
  : Function.invFun (fun x => f x)
    =
    fun x => f.symm x := by fun_trans

example (f : Nat ≃ Nat)
  : Function.Bijective (fun x => f.symm x) := by fun_prop

example (f : Nat ≃ Nat)
  : Function.invFun (fun x => f.symm x)
    =
    fun x => f x := by fun_trans
