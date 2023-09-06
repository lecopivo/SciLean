import Std.Tactic.GuardMsgs
import SciLean.Util.RewriteBy
import SciLean.Tactic.LSimp.Elab
import SciLean.Tactic.LetNormalize

open SciLean


/--
info: fun i =>
  let j := 42;
  let foo := ((i * j, i + j), i ^ j, i / j);
  foo.fst : Nat → Nat × Nat
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
  (let j := 42;
    let foo := ((i * j, i + j), i ^ j, i / j);
    foo).fst : Nat → Nat × Nat
-/
#guard_msgs in
#check 
   (fun i : Nat =>
      (let j := 42
       let foo := ((i * j, i+j), (i ^ j, i / j))
       foo).fst)
   rewrite_by
     ldsimp (config := {zeta:=false}) only


/--
info: fun i =>
  (let j := 42;
    let foo := ((i * j, i + j), i ^ j, i / j);
    foo.fst).snd : Nat → Nat
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
  let j := 42;
  let foo := ((i * j, i + j), i ^ j, i / j);
  foo.fst.snd : Nat → Nat
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
info: let a := 42;
a : Nat
-/
#guard_msgs in
#check 
  (let a := 42
   let b := 7
   (a,b)).1
  rewrite_by
    lsimp (config := {zeta:=false}) only

