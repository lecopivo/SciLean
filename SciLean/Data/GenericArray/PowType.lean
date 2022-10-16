import SciLean.Data.GenericArray.Basic
import SciLean.Data.GenericArray.Notation
import SciLean.Data.GenericArray.MatrixOperations


namespace SciLean

/-- This class says that `T` is the canonical type to store `numOf I` element of `X`. 

This class allows for the notation `X^I` and `T = X^I`. -/
class PowType (T : outParam Type) (I X : Type) extends GenericArray T I X

/-- Obtains the type of `X^I` by providing `X` and `I` -/
abbrev PowTypeCarrier (X I : Type) {T : outParam Type} [PowType T I X] := T

/-- This class says that `T n` is the canonical type to store `n` elements of `X`.

This class allows for the notation `X^{n}` and `T n = X^{n}`. -/
class LinearPowType (T : outParam (Nat → Type)) (X : Type) extends GenericLinearArray T X

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
--   : GenericLinearArray T X := GenericLinearArray.mk (by infer_instance) sorry_proof sorry_proof sorry_proof


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


-- TODO: Generalize this
/-- `A[i,j]` is just a notation for `A[(i,j)]` -/
macro A:term  noWs "[" id1:term "," id2:term "]" : term => `($A[($id1, $id2)])
/-- `A[i,j,k]` is just a notation for `A[(i,j,k)]` -/
macro A:term  noWs "[" id1:term "," id2:term "," id3:term "]" : term => `($A[($id1, $id2, $id3)])
/-- `A[i,j,k,l]` is just a notation for `A[(i,j,k,l)]` -/
macro A:term  noWs "[" id1:term "," id2:term "," id3:term "," id4:term "]" : term => `($A[($id1, $id2, $id3, $id4)])
/-- `A[i,:]` is just a notation for `λ [j] => A[i,j]` -/
macro A:term  noWs "[" id1:term "," ":" "]" : term => `(λ [j] => $A[($id1, j)])
/-- `A[i,·]` is just a notation for `λ [j] => A[i,j]` -/
macro A:term  noWs "[" id1:term "," "·" "]" : term => `(λ j => $A[($id1, j)])
/-- `A[:,j]` is just a notation for `λ [i] => A[i,j]` -/
macro A:term  noWs "[" ":" "," id2:term "]" : term => `(λ [i] => $A[(i, $id2)])
/-- `A[·,j]` is just a notation for `λ i => A[i,j]` -/
macro A:term  noWs "[" "·" "," id2:term "]" : term => `(λ i => $A[(i, $id2)])

end CustomNotation

namespace PowTypeCarrier

section FixedSize

variable {X I} {T : outParam Type} [Enumtype I] [PowType T I X] -- [Inhabited X]

abbrev get (x : X^I) (i : I) : X := getElem x i True.intro
abbrev set (x : X^I) (i : I) (xi : X) : X^I := setElem x i xi
abbrev intro (f : I → X) : X^I := introElem f
abbrev modify (x : X^I) (i : I) (f : X → X) : X^I := GenericArray.modifyElem x i f
abbrev mapIdx (f : I → X → X) (x : X^I) : X^I := GenericArray.mapIdx f x
abbrev map (f : X → X) (x : X^I) : X^I := GenericArray.map f x

abbrev Index (_ : X^I) := I
abbrev Elem  (_ : X^I) := X

end FixedSize


section VariableSize
variable {X} {T : outParam (Nat → Type)} [LinearPowType T X]

/-- Array of zero size. -/
def empty : X^{0} := λ [i] => 
  absurd (a := ∃ n : Nat, n < 0) 
         (Exists.intro i.1 i.2) 
         (by intro h; have h' := h.choose_spec; cases h'; done)

def split {n m : Nat} 
  (x : X^{n+m}) : X^{n} × X^{m} := 
  (λ [i] => x[⟨i.1,sorry_proof⟩], λ [i] => x[⟨i.1+n,sorry_proof⟩])

def merge {n m : Nat} 
  (x : X^{n}) (y : X^{m}) : X^{n+m} := 
  (λ [i] => if i.1 < n 
            then x[⟨i.1,sorry_proof⟩]
            else y[⟨i.1-n, sorry_proof⟩])

abbrev drop (k : Nat := 1) (x : X^{n+k}) : X^{n} := dropElem k x
abbrev push (x : X^{n}) (xi : X) (k : Nat := 1) : X^{n+k} := pushElem k xi x

-- TODO: prove properties of `drop'` and maybe replace `drop`
def drop' (x : X^{n}) (k : Nat := 1) : X^{n-k} := 
  let n' := n - k
  if h : n = n' + k then
    dropElem k (h ▸ x)
  else
    have h : n - k = 0 := sorry_proof
    cast (by rw[h]) (empty : X^{0})

/-- Computes: `y[i] := a i * x[i] + b i * x[i+1]` 

Special case for `i=n-1`: `y[n-1] := a (n-1) * x[n-1]` -/
abbrev upper2DiagonalUpdate [Vec X] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : X^{n}) : X^{n} :=
  GenericArray.upper2DiagonalUpdate a b x

/-- Computes: `y[i] := a i * x[i] + b (i-1) * x[i-1]` 

Special case for `i=0`: `y[0] := a 0 * x[0]` -/
abbrev lower2DiagonalUpdate [Vec X] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : X^{n}) : X^{n} :=
  GenericArray.lower2DiagonalUpdate a b x

/-- Computes: `y[i] := x[i+1] - x[i]` -/
abbrev differences [Vec X] (x : X^{n+1}) : X^{n} :=
  GenericArray.differences x

/-- Computes: `y[i] := (1-t) * x[i] + t * x[i+1]` -/
abbrev linearInterpolate [Vec X] (t : ℝ) (x : X^{n+1}) : X^{n} :=
  GenericArray.linearInterpolate t x

example [Vec X] : IsLin (λ x : X^{n} => x.upper2DiagonalUpdate (λ _ => 1) (λ _ => -1)) := by infer_instance
example [Vec X] : IsLin (λ x : X^{n+1} => x.drop) := by infer_instance
example [Vec X] (xi : X) : IsSmooth (λ x : X^{n} => x.push xi) := by infer_instance

example [Vec X] : IsSmooth (λ x : X^{n+1} => x.linearInterpolate) := by infer_instance
example [Vec X] (x : X^{n+1}) : IsSmooth (λ t => x.linearInterpolate t) := by infer_instance

end VariableSize


structure BezierCurve {T : Nat → Type} (X : Type) [Vec X] [LinearPowType T X] (deg : Nat) where
  points : X^{deg + 1}


variable {X} {T : outParam (Nat → Type)} [LinearPowType T X] [Vec X]

#check BezierCurve X 10

end PowTypeCarrier
