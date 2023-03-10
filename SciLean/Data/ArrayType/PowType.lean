import SciLean.Data.ArrayType.Basic
import SciLean.Data.ArrayType.Notation
import SciLean.Data.ArrayType.MatrixOperations


namespace SciLean

/-- This class says that `T` is the canonical type to store `numOf I` element of `X`. 

This class allows for the notation `X^I` and `T = X^I`. -/
class PowType (T : outParam Type) (I X : Type) extends ArrayType T I X

/-- Obtains the type of `X^I` by providing `X` and `I` -/
abbrev PowTypeCarrier (X I : Type) {T : outParam Type} [PowType T I X] := T

/-- This class says that `T n` is the canonical type to store `n` elements of `X`.

This class allows for the notation `X^{n}` and `T n = X^{n}`. -/
class LinearPowType (T : outParam (Nat → Type)) (X : Type) extends LinearArrayType T X

instance (T : Nat → Type) (X : Type) [LinearPowType T X] (n : Nat) : PowType (T n) (Fin n) X := PowType.mk

/-- Type that behaves like and array with values in `X` and indices in `I`.

For `x : X^I` you can:
  1. get a value: `x[i] : X` for `i : I`
  2. set a value: `setElem x i xi : X^I` for `x : X^I`, `i : I`, `xi : X` 
     in do blocks: `x[i] := xi`, `x[i] += xi`, ...
  3. introduce new array: 
     `let x : X^I := λ [i] => f i`
     for `f : I → X`

The precise type of `X^I` depends on `X` and `I` and it is determined by the typeclass `PowType`. Often `X^I` is internally `Array` or `DataArray` bundled with a proposition about its size e.g. `array.size = numOf I` for `array : Array` and `[Enumtype I]`.
-/
notation X "^" I => PowTypeCarrier X I

-- instance (T : Nat → Type) [∀ n, PowType (T n) (Fin n) X] [DropElem T X] [PushElem T X] [ReserveElem T X] 
--   : LinearArrayType T X := LinearArrayType.mk (by infer_instance) sorry_proof sorry_proof sorry_proof


section CustomNotation

/-- Type that behaves like a multidimensional array with values in `X`.

For `x : X^{n₁,...,nₘ}` you can:
  1. get a value: `x[i₁,...,iₘ] : X` for `i₁ : Fin n₁`, ... , `iₘ : Fin nₘ`
  2. set a value in do blocks: `x[i₁,...,iₘ] := xi`, `x[i₁,...,iₘ] += xi`
     for `x : X^{n₁,...,nₘ}`, `i₁ : Fin n₁`, ... , `iₘ : Fin nₘ`, `xi : X` 
  3. introduce new array: 
     `let x : X^{n₁,...,nₘ} := λ [i₁,...,iₘ] => f i₁ ... iₘ`
     for `f : Fin n₁ → ... → Fin nₘ → X`

The type `X^{n₁,...,nₘ}` is just a notation for `X^(Fin n₁ × ... Fin nₘ)`
-/
syntax term "^{" term,* "}" : term
macro_rules 
| `($X:term ^{ $n }) => do
  `($X ^ (Fin $n))
| `($X:term ^{ $ns,* }) => do
  if 0 < ns.getElems.size then
    let last := ns.getElems[ns.getElems.size-1]!
    let ns' := ns.getElems[:ns.getElems.size-1]
    let I ← ns'.foldrM (λ x y => `(Fin $x × $y)) (← `(Fin $last))
    `($X ^ $I)
  else 
    `(Unit)


-- -- TODO: Generalize this
-- /-- `A[i,j]` is just a notation for `A[(i,j)]` -/
-- macro A:term  noWs "[" id1:term "," id2:term "]" : term => `($A[($id1, $id2)])
-- /-- `A[i,j,k]` is just a notation for `A[(i,j,k)]` -/
-- macro A:term  noWs "[" id1:term "," id2:term "," id3:term "]" : term => `($A[($id1, $id2, $id3)])
-- /-- `A[i,j,k,l]` is just a notation for `A[(i,j,k,l)]` -/
-- macro A:term  noWs "[" id1:term "," id2:term "," id3:term "," id4:term "]" : term => `($A[($id1, $id2, $id3, $id4)])

macro A:term  noWs "[" id:term "," ids:term,* "]" : term => `($A[($id,$ids:term,*)])

/-- `A[i,:]` is just a notation for `λ [j] => A[i,j]` -/
macro A:term  noWs "[" id1:term "," ":" "]" : term => `(λ [j] => $A[($id1, j)])
/-- `A[i,·]` is just a notation for `λ [j] => A[i,j]` -/
macro A:term  noWs "[" id1:term "," "·" "]" : term => `(λ j => $A[($id1, j)])
/-- `A[:,j]` is just a notation for `λ [i] => A[i,j]` -/
macro A:term  noWs "[" ":" "," id2:term "]" : term => `(λ [i] => $A[(i, $id2)])
/-- `A[·,j]` is just a notation for `λ i => A[i,j]` -/
macro A:term  noWs "[" "·" "," id2:term "]" : term => `(λ i => $A[(i, $id2)])


-- This should be improved such that we can specify the type of arguments
-- This clashes with typeclass arguments, but who in their right mind
-- starts a lambda arguments with a typeclass?
syntax (name:=powTypeIntroSyntax) "λ" Lean.Parser.Term.funBinder+  " ==> " term : term
syntax (name:=powTypeIntroSyntaxAlt) "⊞" Lean.Parser.Term.funBinder+  " , " term : term

-- Having this as an abbrev was causing some issues
def introPowElem {X I} {T : outParam Type} [Enumtype I] [PowType T I X] (f : I → X) : X^I := introElem λ i => f i

macro_rules (kind := powTypeIntroSyntax)
| `(λ $xs:funBinder* ==> $b:term) => `(introPowElem λ $xs* => $b)
macro_rules (kind := powTypeIntroSyntaxAlt)
| `(⊞ $xs:funBinder* , $b:term) => `(introPowElem λ $xs* => $b)

end CustomNotation

namespace PowTypeCarrier

section FixedSize

variable {X I} {T : outParam Type} [Enumtype I] [PowType T I X] -- [Inhabited X]

abbrev get (x : X^I) (i : I) : X := getElem x i True.intro
abbrev set (x : X^I) (i : I) (xi : X) : X^I := setElem x i xi
abbrev intro (f : I → X) : X^I := introElem f
abbrev modify (x : X^I) (i : I) (f : X → X) : X^I := ArrayType.modifyElem x i f
abbrev mapIdx (f : I → X → X) (x : X^I) : X^I := ArrayType.mapIdx f x
abbrev map (f : X → X) (x : X^I) : X^I := ArrayType.map f x

def toArray (v : X^I) : Array X := Id.run do
  let mut array : Array X := Array.mkEmpty (numOf I)
  for (i, _) in Enumtype.fullRange I do
    array := array.push v[i]
  return array

abbrev Index (_ : X^I) := I
abbrev Elem  (_ : X^I) := X

open Lean in
instance [ToJson X] : ToJson (X^I) where
  toJson v := toJson (v.toArray)

open Lean in
instance [FromJson X] : FromJson (X^I) where
  fromJson? json := 
    match fromJson? (α := Array X) json with
    | .error msg => .error msg
    | .ok array => 
      if h : (numOf I) = array.size then
        .ok (introElem λ i => array[h ▸ toFin i])
      else 
        .error "Failed to convert to json to PowType X^{n}, json size does not match `n`"

end FixedSize


section VariableSize
variable {X} {T : outParam (Nat → Type)} [LinearPowType T X]

abbrev empty : X^{0} := ArrayType.empty 
abbrev split {n m : Nat} (x : X^{n+m}) : X^{n} × X^{m} := ArrayType.split x
abbrev merge {n m : Nat} (x : X^{n}) (y : X^{m}) : X^{n+m} := ArrayType.append x y
abbrev append {n m : Nat} (x : X^{n}) (y : X^{m}) : X^{n+m} := ArrayType.append x y
abbrev drop (k : Nat := 1) (x : X^{n+k}) : X^{n} := dropElem k x
abbrev push (x : X^{n}) (xi : X) (k : Nat := 1) : X^{n+k} := pushElem k xi x

/-- Computes: `y[i] := a i * x[i] + b i * x[i+1]` 

Special case for `i=n-1`: `y[n-1] := a (n-1) * x[n-1]` -/
abbrev generateUpperTriangularArray (f : (n' : Nat) → X^{n'+1} → X^{n'}) (x : X^{n}) : X^{(n*(n+1))/2} := 
  ArrayType.generateUpperTriangularArray f x
abbrev upper2DiagonalUpdate [Vec X] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : X^{n}) : X^{n} :=
  ArrayType.upper2DiagonalUpdate a b x

/-- Computes: `y[i] := a i * x[i] + b (i-1) * x[i-1]` 

Special case for `i=0`: `y[0] := a 0 * x[0]` -/
abbrev lower2DiagonalUpdate [Vec X] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : X^{n}) : X^{n} :=
  ArrayType.lower2DiagonalUpdate a b x

/-- Computes: `y[i] := x[i+1] - x[i]` -/
abbrev differences [Vec X] (x : X^{n+1}) : X^{n} :=
  ArrayType.differences x

/-- Computes: `y[i] := (1-t) * x[i] + t * x[i+1]` -/
abbrev linearInterpolate [Vec X] (t : ℝ) (x : X^{n+1}) : X^{n} :=
  ArrayType.linearInterpolate t x

-- example [Vec X] : IsLin (λ x : X^{n} => x.upper2DiagonalUpdate (λ _ => 1) (λ _ => -1)) := by infer_instance
-- example [Vec X] : IsLin (λ x : X^{n+1} => x.drop) := by infer_instance
-- example [Vec X] (xi : X) : IsSmooth (λ x : X^{n} => x.push xi) := by infer_instance

-- example [Vec X] : IsSmooth (λ x : X^{n+1} => x.linearInterpolate) := by infer_instance
-- example [Vec X] (x : X^{n+1}) : IsSmooth (λ t => x.linearInterpolate t) := by infer_instance

end VariableSize


section Currying

variable {X I J}  [Enumtype I] [Enumtype J]
variable {T : outParam Type} [PowType T J X]
variable {T' : outParam Type} [PowType T' I (X^J)]
variable {T'' : outParam Type} [PowType T'' (I×J) X]

-- sometimes this should be effectivelly identity function
-- sometimes you have to reshuffle memory around, how to deal with this?
-- def curry : (X^(I×J)) → ((X^J)^I) := sorry
-- def uncurry : ((X^J)^I) → (X^(I×J)) := sorry

end Currying


end PowTypeCarrier
