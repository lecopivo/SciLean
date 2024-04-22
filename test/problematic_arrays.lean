import SciLean


#exit
def dot {n : Nat} (x y : Float^[n]) : Float := ∑ i, x[i] * y[i]

-- terrible error message
#eval dot ⊞[1.0,1.0] ⊞[1.0,1.0,1.0]


-- terrible type
#check ⊞[1.0,2.0]

-- terrible type
#check ⊞[⊞[(1.0:Float), 2.0],⊞[(3.0:Float), 4.0]]

#check 1.0

-- creating matrices not supported
#check ⊞[1.0,2.0; 3.0, 4.0]


variable {n m : Nat} (x : Float^[n])

-- terrible error message
#check ⊞ i (j : Fin m) => x[i]^j

open Lean Meta Elab Term Qq
elab "type_of" x:term : term => do
  let x ← elabTerm x q(Float)
  let X ← instantiateMVars (← inferType x)
  IO.println s!"type of {← ppExpr x} is {← ppExpr X}"
  return x


#check type_of 1.0
