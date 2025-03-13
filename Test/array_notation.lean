import SciLean

open SciLean

/-- info: ⊞[1.000000, 2.000000, 3.000000] -/
#guard_msgs in
#eval ⊞[1.0,2,3]

/-- info: 1.000000 -/
#guard_msgs in
#eval ⊞[1.0,2,3][0]


variable (A : Float^[2,2])

/-- info: A[(0, 1)] : Float -/
#guard_msgs in
#check A[0,1]

/-- info: fun i j => A[(i, j)] : Idx 2 → Idx 2 → Float -/
#guard_msgs in
#check fun i j => A[i,j]


/-- info: 2.000000 -/
#guard_msgs in
#eval ⊞[1.0,2;3,4][(0,1)]

variable (n m : Nat) (f : Idx n → Float) (g : Idx m → Idx n → Float)

/-- info: ⊞ i => f i : Float^[n] -/
#guard_msgs in
#check ⊞ i => f i

/-- info: ⊞ i j => g i j : Float^[m, n] -/
#guard_msgs in
#check ⊞ i j => g i j

/-- info: ⊞ i => ⊞ j => g i j : Float^[n]^[m] -/
#guard_msgs in
#check ⊞ i => ⊞ j => g i j
