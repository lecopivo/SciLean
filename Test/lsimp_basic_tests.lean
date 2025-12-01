import SciLean

open SciLean


example (n : Nat) :
  n
  =
  n := by (conv => lhs; lsimp)

example (n : Nat) :
  (let a := 1; a + n)
  =
  (1 + n) := by (conv => lhs; lsimp)

example (n : Nat) :
  (0 + n)
  =
  n := by (conv => lhs; lsimp)

example (n : Nat) :
  (0 + 1 * n)
  =
  n := by (conv => lhs; lsimp)

example (n : Nat) :
  (let a := (0 + 1 * n); a)
  =
  n := by (conv => lhs; lsimp)

example (n : Nat) :
    (let a :=
       let c := 0 + n
       let d := c + 0 + 3
       c + d + 1 * n + 2
     let b := a + 5
     a + b)
    =
    n + (n + 3) + n + 2 + (n + (n + 3) + n + 2 + 5) := by
  (conv => lhs; lsimp)

example (n : Nat) (i : Fin n) :
    (let j := 2*i.1
     let hj : j < 2*n := by omega
     let j : Fin (2*n) := ⟨j, hj⟩
     let k :=
       let a := j + j
       a + j
     j + k)
    =
    let j := 2*i.1
    let hj : j < 2*n := by omega
    let j : Fin (2*n) := ⟨j, hj⟩
    (j + (j + j + j)) := by
  (conv => lhs; lsimp)

-- tests under lambda binder

example :
  (fun n : Nat => n)
  =
  (fun n : Nat => n) := by (conv => lhs; lsimp)

example :
  (fun n => let a := 1; a + n)
  =
  (fun n => 1 + n) := by (conv => lhs; lsimp)


example :
  (fun n => let a := (0 + 1 * n * 1 * 2); a)
  =
  (fun n => n * 2) := by (conv => lhs; lsimp)


example :
    (fun n : Nat=>
     let c := n
     let a := c + 1 * n
     a)
    =
    (fun n => n + n) := by
  (conv => lhs; lsimp)


example :
    (fun (n : Nat) (i : Fin n) =>
     let j := 2*i.1
     let hj : j < 2*n := by omega
     let j : Fin (2*n) := ⟨j, hj⟩
     let k :=
       let a := j + j
       a + j
     j + k)
    =
    fun (n : Nat) (i : Fin n) =>
    let j := 2*i.1
    let hj : j < 2*n := by omega
    let j : Fin (2*n) := ⟨j, hj⟩
    (j + (j + j + j)) := by
  (conv => lhs; lsimp)


-- OLD COMMENT: test projection, simp does not preserve the let bindings even with `zeta:=false`
-- UPDATE: This is no longer the case! Yay!
section LetAndProjections
variable (a b c : Nat)
/--
info: let x := a * b;
x : ℕ
-/
#guard_msgs in
#check (let x := a * b
        let y := x * c
        (x,y)).1 rewrite_by lsimp

/--
info: (have x := a * b;
  have y := x * c;
  (x, y)).1 : ℕ
-/
#guard_msgs in
#check (let x := a * b
        let y := x * c
        (x,y)).1 rewrite_by simp (config:={zeta:=false}) only

end LetAndProjections
