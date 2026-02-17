import SciLean

open SciLean


/--
info: fun i => (i * 42, i + 42) : ℕ → ℕ × ℕ
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
info: fun i => (i * 42, i + 42) : ℕ → ℕ × ℕ
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
  i + j : ℕ → ℕ
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
info: fun i => i + 42 : ℕ → ℕ
-/
#guard_msgs in
#check
   (fun i : Nat =>
      let j := 42
      let foo := ((i * j, i+j), (i ^ j, i / j))
      foo.fst.snd)
   rewrite_by
     lsimp
