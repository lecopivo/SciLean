import SciLean

open SciLean


/--
info: fun i =>
  let foo0 := i * 42;
  let foo1 := i + 42;
  (foo0, foo1) : ℕ → ℕ × ℕ
-/
#guard_msgs in
#check
   (fun i : Nat =>
      let j := 42
      let foo := ((i * j, i+j), (i ^ j, i / j))
      foo.fst)
   rewrite_by
     simp (config:={zeta:=false,singlePass:=true}) [Tactic.lift_lets_simproc]

#exit

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
     simp (config:={zeta:=false,singlePass:=true}) [Tactic.lift_lets_simproc]


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
     simp (config:={zeta:=false,singlePass:=true}) [Tactic.lift_lets_simproc]



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
     simp (config:={zeta:=false,singlePass:=true}) [Tactic.lift_lets_simproc]
