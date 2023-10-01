import Std.Tactic.GuardMsgs
import SciLean.Util.RewriteBy
import SciLean.Tactic.LSimp2.Elab
import SciLean.Tactic.LetNormalize

open SciLean


/--
info: fun i =>
  let foo0 := i * 42;
  let foo1 := i + 42;
  (foo0, foo1) : Nat → Nat × Nat
-/
#guard_msgs in
#check 
   (fun i : Nat =>
      let j := 42
      let foo := ((i * j, i+j), (i ^ j, i / j))
      foo.fst)
   rewrite_by
     lsimp (config := {zeta:=false}) only


/--
info: fun i =>
  let foo0 := i * 42;
  let foo1 := i + 42;
  (foo0, foo1) : Nat → Nat × Nat
-/
#guard_msgs in
#check 
   (fun i : Nat =>
      (let j := 42
       let foo := ((i * j, i+j), (i ^ j, i / j))
       foo).fst)
   rewrite_by
     lsimp (config := {zeta:=false}) only


/--
info: fun i =>
  let foo0 := i * 42;
  let foo1 := i + 42;
  let foo2 := i ^ 42;
  let foo3 := i / 42;
  ((foo0, foo1), foo2, foo3).fst.snd : Nat → Nat
-/
#guard_msgs in
#check 
   (fun i : Nat =>
      (let j := 42
       let foo := ((i * j, i+j), (i ^ j, i / j))
       foo.fst).snd)
   rewrite_by
     lsimp (config := {zeta:=false, proj:=false}) only


/--
info: fun i =>
  let foo1 := i + 42;
  foo1 : Nat → Nat
-/
#guard_msgs in
#check 
   (fun i : Nat =>
      let j := 42
      let foo := ((i * j, i+j), (i ^ j, i / j))
      foo.fst.snd)
   rewrite_by
     lsimp (config := {zeta:=false}) only


/--
info: let a := hold 42;
a : Nat
-/
#guard_msgs in
#check 
  (let a := hold 42
   let b := hold 7
   (a,b)).1
  rewrite_by
    lsimp (config := {zeta:=false}) only

