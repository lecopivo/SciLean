import SciLean.Tactic.StructuralInverse
import SciLean.Data.Idx

open SciLean 

open Lean Meta Qq

/--
info: fun ij1 y =>
  let ij0' := fun ij1 => Function.invFun (fun ij0 => ij0 + ij1.1) y;
  let ij0'' := ij0' ij1;
  (ij0'', ij1)
-/
#guard_msgs in
#eval show MetaM Unit from do

  let f := q(fun ij : Idx 10 × Idx 5 => ij.1 + ij.2.1)
  -- let f := q(fun ij : Int × Int × Int => (ij.1 + ij.2.2, ij.2.1 + ij.1 + ij.2.2))
  -- let f := q(fun ij : Int × Int × Int => (ij.2.2, ij.1))
  let .some (.right f', _) ← structuralInverse f
    | throwError "failed to invert"
  IO.println (← ppExpr f'.invFun)  

/--
info: fun ij1 y =>
  let ij0' := fun ij2 => Function.invFun (fun ij0 => ij0 + ij2) y.fst;
  let ij2' := fun ij1 => Function.invFun (fun ij2 => ij1 + ij0' ij2 + ij2) y.snd;
  let ij2'' := ij2' ij1;
  let ij0'' := ij0' ij2'';
  (ij0'', ij1, ij2'')
-/
#guard_msgs in
#eval show MetaM Unit from do

  let f := q(fun ij : Int × Int × Int => (ij.1 + ij.2.2, ij.2.1 + ij.1 + ij.2.2))
  let .some (.right f', _) ← structuralInverse f
    | throwError "failed to invert"
  IO.println (← ppExpr f'.invFun)  

/-- 
info: fun ij1 y => (y.snd, ij1, y.fst)
-/
#guard_msgs in
#eval show MetaM Unit from do
  let f := q(fun ij : Int × Int × Int => (ij.2.2, ij.1))
  let .some (.right f', _) ← structuralInverse f
    | throwError "failed to invert"
  IO.println (← ppExpr f'.invFun)  


/-- 
info: fun y => (y.snd.fst, y.snd.snd, y.fst)
-/
#guard_msgs in
#eval show MetaM Unit from do
  let f := q(fun ij : Int × Int × Int => (ij.2.2, ij.1, ij.2.1))
  let .some (.full f', _) ← structuralInverse f
    | throwError "failed to invert"
  IO.println (← ppExpr f'.invFun)  
