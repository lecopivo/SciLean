import SciLean

open SciLean

example : Differentiable ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z) := by fun_prop

example
  : (fderiv ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z))
    =
    fun (_,_,_) => fun dx =>L[ℝ] dx.2.2 := by fun_trans

example
  : Differentiable Float (fun x : Float => ⊞ (_ : Idx 10) => x) :=
by
  fun_prop

example
  : fderiv Float (fun x : Float => ⊞ (_ : Idx 10) => x)
    =
    (fun _ => fun dx : Float =>L[Float] ⊞ (_ : Idx 10) => dx) :=
by
  fun_trans

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
