-- import SciLean.Core.FunctionTransformations.CDeriv
-- import SciLean.Core.FunctionTransformations.InvFun
import SciLean

open SciLean

-- should unfold match statement and see through projections
example : IsDifferentiable ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z) := by fprop

-- should unfold match statement and see through projections
example 
  : (cderiv ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z))
    =
    fun (_,_,_) (_,_,dz) => dz := by ftrans only

-- should unfold introElemNotation to introElem
example 
  : IsDifferentiable Float (fun x : Float => ⊞ _ : Idx 10 => x) := 
by
  fprop

-- should unfold introElemNotation to introElem
example
  : cderiv Float (fun x : Float => ⊞ _ : Idx 10 => x)
    =
    fun x dx => ⊞ _ : Idx 10 => dx := 
by
  ftrans
  
-- should unfold FunLike.coe to Equiv.toFun
example (f : Nat ≃ Nat)
  : Function.Bijective (fun x => f x) := by fprop

-- should unfold FunLike.coe to Equiv.toFun
example (f : Nat ≃ Nat)
  : Function.invFun (fun x => f x)
    =
    fun x => f.symm x := by ftrans

-- should unfold FunLike.coe to Equiv.toFun
example (f : Nat ≃ Nat)
  : Function.Bijective (fun x => f.symm x) := by fprop

-- should unfold FunLike.coe to Equiv.toFun
example (f : Nat ≃ Nat)
  : Function.invFun (fun x => f.symm x)
    =
    fun x => f x := by ftrans; ftrans
