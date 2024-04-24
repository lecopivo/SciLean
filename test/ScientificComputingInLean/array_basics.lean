import SciLean.Data.DataArray
import Mathlib

open SciLean LeanColls


def dot {n : Nat} (x y : Float^[n]) : Float := ∑ i, x[i] * y[i]

/--
info: ⊞[1.000000, 1.000000]
-/
#guard_msgs in
#eval ⊞[1.0,1.0]

/--
info: 2.000000
-/
#guard_msgs in
#eval dot ⊞[1.0,1.0] ⊞[1.0,1.0]

/--
warning: application type mismatch
  dot ⊞[1.0, 1.0] ⊞[1.0, 1.0, 1.0]
argument
  ⊞[1.0, 1.0, 1.0]
has type
  DataArrayN Float (Fin 3) : Type
but is expected to have type
  DataArrayN Float (Fin 2) : Type
-/
#guard_msgs in
#check_failure dot ⊞[1.0,1.0] ⊞[1.0,1.0,1.0]

def u :=  ⊞[1.0, 2.0]

/-- info: 1.000000 -/
#guard_msgs in
#eval u[0]

/-- info: 2.000000 -/
#guard_msgs in
#eval u[1]

/-- info: 3.000000 -/
#guard_msgs in
#eval ∑ i, u[i]

/-- info: ![1.000000, 2.000000] -/
#guard_msgs in
#eval fun i => u[i]

-- todo: support creating matrix literals
-- def A := ⊞[1.0, 2.0; 3.0, 4.0]

-- remove this once `A` is defined properly
variable (A : Float^[2,2])

-- switch to eval once `A` is defined properly
/-- info: A[0, 1] : Float -/
#guard_msgs in
#check A[0,1]

/-- info: A[0, 1] : Float -/
#guard_msgs in
#check A[(0,1)]

/-- info: fun i j => A[i, j] : Fin 2 → Fin 2 → Float -/
#guard_msgs in
#check fun i j => A[i,j]


variable {Cont Idx Elem} [DecidableEq Idx] [ArrayType Cont Idx Elem] [ArrayTypeNotation Cont Idx Elem]
         (f : Idx → Elem)

/-- info: ⊞ i => f i : Cont -/
#guard_msgs in
#check ⊞ i => f i


def outerProduct1 {n m : Nat} (x : Float^[n]) (y : Float^[m]) : Float^[n,m] :=
  ⊞ i j => x[i]*y[j]


def outerProduct2 {n m : Nat} (x : Float^[n]) (y : Float^[m]) := Id.run do
  let mut A : Float^[n,m] := 0
  for i in IndexType.univ (Fin n) do
    for j in IndexType.univ (Fin m) do
      A[i,j] := x[i]*y[j]
  return A


def outerProduct3 {n m : Nat} (x : Float^[n]) (y : Float^[m]) := Id.run do
  let mut A : Float^[n,m] := 0
  for (i,j) in (IndexType.univ (Fin n × Fin m)) do
    A[i,j] := x[i]*y[j]
  return A


def outerProduct4 {n m : Nat} (x : Float^[n]) (y : Float^[m]) : Float^[n,m] := Id.run do
  let mut A : DataArray Float := .mkEmpty (n*m) -- empty array with capacity `n*m`
  for (i,j) in (IndexType.univ (Fin n × Fin m)) do
    A := A.push (x[i]*y[j])
  return { data:= A, h_size:= sorry }


/-- info: ⊞[3.000000, 4.000000, 6.000000, 8.000000] -/
#guard_msgs in
#eval outerProduct1 ⊞[(1.0 : Float), 2.0] ⊞[(3.0 : Float), 4.0]

/-- info: ⊞[3.000000, 4.000000, 6.000000, 8.000000] -/
#guard_msgs in
#eval outerProduct2 ⊞[(1.0 : Float), 2.0] ⊞[(3.0 : Float), 4.0]

/-- info: ⊞[3.000000, 4.000000, 6.000000, 8.000000] -/
#guard_msgs in
#eval outerProduct3 ⊞[(1.0 : Float), 2.0] ⊞[(3.0 : Float), 4.0]

/-- info: ⊞[3.000000, 4.000000, 6.000000, 8.000000] -/
#guard_msgs in
#eval outerProduct4 ⊞[(1.0 : Float), 2.0] ⊞[(3.0 : Float), 4.0]


open IndexType
def naturalEquiv'
    (I J : Type) [IndexType I] [IndexType J] [LawfulIndexType I] [LawfulIndexType J]
    (h : card I = card J) : I ≃ J := {
  toFun := fun i => fromFin (h ▸ toFin i)
  invFun := fun j => fromFin (h ▸ toFin j)
  left_inv := sorry
  right_inv := sorry
}
