import SciLean

open SciLean


/--
info: fun i =>
  let foo := i * 42;
  let foo_1 := i + 42;
  (foo, foo_1) : ℕ → ℕ × ℕ
-/
#guard_msgs in
#check
   (fun i : Nat =>
      let j := 42
      let foo := ((i * j, i+j), (i ^ j, i / j))
      foo.fst)
   rewrite_by
     lsimp

/--
info: fun i =>
  let foo := i * 42;
  let foo_1 := i + 42;
  (foo, foo_1) : ℕ → ℕ × ℕ
-/
#guard_msgs in
#check
   (fun i : Nat =>
      (let j := 42
       let foo := ((i * j, i+j), (i ^ j, i / j))
       foo).fst)
   rewrite_by
     lsimp


/--
info: fun i =>
  let j := 42 * i;
  let foo := i + j;
  foo : ℕ → ℕ
-/
#guard_msgs in
#check
   (fun i : Nat =>
      (let j := 42*i
       let foo := ((i * j, i+j), (i ^ j, i / j))
       foo.fst).snd)
   rewrite_by
     lsimp



/--
info: fun i =>
  let foo := i + 42;
  foo : ℕ → ℕ
-/
#guard_msgs in
#check
   (fun i : Nat =>
      let j := 42
      let foo := ((i * j, i+j), (i ^ j, i / j))
      foo.fst.snd)
   rewrite_by
     lsimp
