import SciLean

open SciLean

#exit

def dot {n : Nat} (x y : Float^[n]) : Float := ∑ i, x[i] * y[i]

-- todo: make this working!!!s
#eval ⊞[1.0,1.0]

#eval dot ⊞[1.0,1.0] ⊞[1.0,1.0]

-- todo: fix error message
#eval dot ⊞[1.0,1.0] ⊞[1.0,1.0,1.0]


def u :=  ⊞[(1.0 : Float), 2.0]

#eval u[0]
#eval u[1]
#eval ∑ i, u[i]
#eval fun i => u[i]

-- todo: support creating matrix literals
-- def A := ⊞[1.0, 2.0; 3.0, 4.0]

-- remove this once `A` is defined properly
variable (A : Float^[2,2])

-- switch to eval once `A` is defined properly
#check A[0,1]
#check A[(0,1)]


variable {Cont Idx Elem} [DecidableEq Idx] [ArrayType Cont Idx Elem] [ArrayTypeNotation Cont Idx Elem]
         (f : Idx → Elem)

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


#eval outerProduct1 ⊞[(1.0 : Float), 2.0] ⊞[(3.0 : Float), 4.0]
#eval outerProduct2 ⊞[(1.0 : Float), 2.0] ⊞[(3.0 : Float), 4.0]
#eval outerProduct3 ⊞[(1.0 : Float), 2.0] ⊞[(3.0 : Float), 4.0]
#eval outerProduct4 ⊞[(1.0 : Float), 2.0] ⊞[(3.0 : Float), 4.0]


-- This function already exists as `IndexType.naturalEquiv`
open IndexType
def naturalEquiv' (I J : Type) [IndexType I] [IndexType J] (h : card I = card J) : I ≃ J := {
  toFun := fun i => fromFin (h ▸ toFin i)
  invFun := fun j => fromFin (h ▸ toFin j)
  left_inv := sorry
  right_inv := sorry
}
