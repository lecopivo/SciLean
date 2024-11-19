import SciLean.Tactic.InferVar

open SciLean

def foo {n : Nat} {m : Nat} (i : Fin n) (h : 2 * m = n := by infer_var) : Fin m := ⟨i/2, by omega⟩

/-- info: foo 8 ⋯ : Fin 5 -/
#guard_msgs in
#check foo (8 : Fin 10)

def foo2 {n : Nat} (i : Fin (2*n)) := foo i

/-- info: foo2 {n : ℕ} (i : Fin (2 * n)) : Fin n -/
#guard_msgs in
#check foo2
