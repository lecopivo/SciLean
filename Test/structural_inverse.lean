import SciLean.Tactic.StructuralInverse
-- import SciLean.Data.Idx

open SciLean

open Lean Meta Qq

/--
info: fun ij1 y =>
  let ij0' := fun ij1 => Function.invFun (fun ij0 => ij0 + ↑ij1.1) y;
  let ij0'' := ij0' ij1;
  (ij0'', ij1)
-/
#guard_msgs in
#eval show MetaM Unit from do

  let f := q(fun ij : Fin 10 × Fin 5 => ij.1 + ij.2.1)
  -- let f := q(fun ij : Int × Int × Int => (ij.1 + ij.2.2, ij.2.1 + ij.1 + ij.2.2))
  -- let f := q(fun ij : Int × Int × Int => (ij.2.2, ij.1))
  let .some (.right f', _) ← structuralInverse f
    | throwError "failed to invert"
  IO.println (← ppExpr f'.invFun)

/--
info: fun ij2 y =>
  let ij0' := fun ij2 => Function.invFun (fun ij0 => ij0 + ij2) y.1;
  let ij1' := fun ij2 => Function.invFun (fun ij1 => ij1 + ij0' ij2 + ij2) y.2;
  let ij1'' := ij1' ij2;
  let ij0'' := ij0' ij2;
  (ij0'', ij1'', ij2)
-/
#guard_msgs in
#eval show MetaM Unit from do

  let f := q(fun ij : Int × Int × Int => (ij.1 + ij.2.2, ij.2.1 + ij.1 + ij.2.2))
  let .some (.right f', _) ← structuralInverse f
    | throwError "failed to invert"
  IO.println (← ppExpr f'.invFun)

/--
info: fun ij1 y => (y.2, ij1, y.1)
-/
#guard_msgs in
#eval show MetaM Unit from do
  let f := q(fun ij : Int × Int × Int => (ij.2.2, ij.1))
  let .some (.right f', _) ← structuralInverse f
    | throwError "failed to invert"
  IO.println (← ppExpr f'.invFun)

/--
info: fun y => (y.2.1, y.2.2, y.1)
-/
#guard_msgs in
#eval show MetaM Unit from do
  let f := q(fun ij : Int × Int × Int => (ij.2.2, ij.1, ij.2.1))
  let .some (.full f', _) ← structuralInverse f
    | throwError "failed to invert"
  IO.println (← ppExpr f'.invFun)


/--
info: fun x0 y =>
  let x1' := fun x0 => Function.invFun (fun x1 => x0 + x1) y.2;
  let x2' := fun x0 => Function.invFun (fun x2 => x0 + x1' x0 + x2) y.1;
  let x2'' := x2' x0;
  let x1'' := x1' x0;
  (x0, x1'', x2'')
-/
#guard_msgs in
#eval show MetaM Unit from do

  -- let e := q(fun ((x,y,z) : Int × Int × Int) => (x+y+z,x+y))
  let e := q(fun (x : Int × Int × Int) => (x.1+x.2.1+x.2.2,x.1+x.2.1))

  let .some (.right inv, _) ← structuralInverse e
    | return ()

  IO.println (← ppExpr inv.invFun)


/--
info: fun x1 y => (y.2, x1, y.1)
-/
#guard_msgs in
#eval show MetaM Unit from do

  -- let e := q(fun ((x,_y,z) : Int × Int × Int) => (z,x))
  let e := q(fun (x : Int × Int × Int) => (x.2.2,x.1))

  let .some (.right inv,_goals) ← structuralInverse e
    | return ()

  IO.println (← ppExpr inv.invFun)
