import SciLean.Data.ArrayType.Notation
import SciLean.Data.ArrayType.Properties

namespace SciLean
namespace GenericArrayType
section LinearGenericArrayType

variable {Cont : Nat → Type} {Elem : Type |> outParam}
variable [LinearGenericArrayType Cont Elem]


--------------------------------------------------------------------------------
-- dropElem
--------------------------------------------------------------------------------

function_properties SciLean.DropElem.dropElem 
  {Cont : Nat → Type} {Elem : Type |> outParam} [LinearGenericArrayType Cont Elem] [Vec Elem] 
  {n : Nat} (k : Nat) (cont : Cont (n+k)) 
argument cont
  IsLin := sorry_proof,
  IsSmooth := sorry_proof,  
  abbrev ∂ := λ dcont => dropElem k dcont by sorry_proof,
  abbrev 𝒯 := λ dcont => (dropElem k cont, dropElem k dcont) by sorry_proof

function_properties SciLean.DropElem.dropElem 
  {Cont : Nat → Type} {Elem : Type |> outParam} [LinearGenericArrayType Cont Elem] [SemiHilbert Elem] 
  {n : Nat} (k : Nat) (cont : Cont (n+k)) 
argument cont
  HasAdjoint := sorry_proof,
  abbrev † := λ cont' => pushElem k 0 cont' by sorry_proof,
  HasAdjDiff := by sorry_proof,
  abbrev ∂† := λ dcont' => pushElem k 0 dcont' by sorry_proof,
  abbrev ℛ := (dropElem k cont, λ dcont' => pushElem k 0 dcont') by sorry_proof


--------------------------------------------------------------------------------
-- pushElem
--------------------------------------------------------------------------------

function_properties SciLean.PushElem.pushElem 
  {Cont : Nat → Type} {Elem : Type |> outParam} [LinearGenericArrayType Cont Elem] [Vec Elem] 
  {n : Nat} (k : Nat) (elem : Elem) (cont : Cont n)
argument (elem, cont)
  IsLin := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ delem dcont => pushElem k delem dcont by sorry_proof,
  abbrev 𝒯 := λ delem dcont => (pushElem k elem cont, pushElem k delem dcont) by sorry_proof
argument cont
  IsLin [Fact (elem=0)] := sorry_proof,
  IsSmooth := sorry_proof, 
  abbrev ∂ := λ dcont => pushElem k 0 dcont by sorry_proof,
  abbrev 𝒯 := λ dcont => (pushElem k elem cont, pushElem k 0 dcont) by sorry_proof
argument elem
  IsLin [Fact (cont=0)] := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ delem => pushElem k delem 0 by sorry_proof,
  abbrev 𝒯 := λ delem => (pushElem k elem cont, pushElem k delem 0) by sorry_proof

function_properties SciLean.PushElem.pushElem 
  {Cont : Nat → Type} {Elem : Type |> outParam} [LinearGenericArrayType Cont Elem] [SemiHilbert Elem] 
  {n : Nat} (k : Nat) (elem : Elem) (cont : Cont n)
argument (elem, cont)
  HasAdjoint := sorry_proof,
  abbrev † := λ elemcont' => (∑ i : Fin k, elemcont'[⟨n+i.1, sorry_proof⟩], dropElem k elemcont') by sorry_proof,
  HasAdjDiff := sorry,
  abbrev ∂† := λ delemcont' => (∑ i : Fin k, delemcont'[⟨n+i.1, sorry_proof⟩], dropElem k delemcont') by sorry_proof
argument cont
  HasAdjoint [Fact (elem=0)] := sorry_proof,
  abbrev † [Fact (elem=0)] := λ cont' => dropElem k cont' by sorry_proof,
  HasAdjDiff := sorry,
  abbrev ∂† := λ dcont' => dropElem k dcont' by sorry_proof
argument elem
  HasAdjoint [Fact (cont=0)] := sorry_proof,
  abbrev † [Fact (cont=0)] := λ elem' => ∑ i : Fin k, elem'[⟨n+i.1, sorry_proof⟩] by sorry_proof,
  HasAdjDiff := sorry,
  abbrev ∂† := λ delem' => ∑ i : Fin k, delem'[⟨n+i.1, sorry_proof⟩] by sorry_proof


--------------------------------------------------------------------------------
-- reverse
--------------------------------------------------------------------------------

def reverse {n : Nat} (cont : Cont n) : Cont n := Id.run do
  let mut cont := cont
  for i in [0:n/2] do
    let i  : Fin n := ⟨i, sorry_proof⟩
    let i' : Fin n := ⟨n - i.1 - 1, sorry_proof⟩
    let tmp := cont[i]
    cont[i] := cont[i']
    cont[i'] := tmp
  cont


----------------------------------------------------------------------

/-- Generate UpperTriangularArray from and array of size `n`

UpperTriangularArray is an array that relates to lower triangular matrix as:
`[x[0,0], x[0,1], ..., x[0,n-1], 
         x[1,1], ..., x[1,n-1], 
                 ⋱,     ⁞  ,
                    , x[n-1,n-1]]`


TODO: Make tail recursive!
-/
def generateUpperTriangularArray (f : (n' : Nat) → Cont (n'+1) → Cont n') (x : Cont n) : Cont ((n*(n+1))/2) := 
  match n with
  | 0 => introElem λ _ => cast sorry_proof () -- you can't have i of type `Fin 0`
  | _+1 => 
    let x' := f _ x
    let c := generateUpperTriangularArray f x' 
    cast sorry_proof (append x c)



/-- Generate LowerTriangularArray from a single element

Example: generate Pascal's triangle:
  `generateLowerTriangularArray (λ n' x => λ [i] => i = 0 then x[i] else x[i] + x[i-1]) 1`

LowerTriangularArray is an array that relates to lower triangular matrix as:
`[x[0,0], 
 x[1,0], x[1,1], 
 x[2,0], x[2,1], x[2,2],
 ...]` 
-/
def generateLowerTriangularArray (f : (n' : Nat) → Cont n' → Cont (n'+1)) (x : Elem) (n : Nat) : Cont ((n*(n+1))/2) := sorry

/-- Access an element of UpperTriangularArray given `i : Fin n` and `j : Fin (n-i)` 

It corresponds to the `(i,i+j)` element of the triangular matrix.

UpperTriangularArray is an array that relates to lower triangular matrix as:
`[x[0,0], x[0,1], ..., x[0,n-1], 
         x[1,1], ..., x[1,n-1], 
                 ⋱,     ⁞  ,
                    , x[n-1,n-1]]`
-/
def upperTriangularArrayGet (upperTriangular : Cont ((n*(n+1))/2)) (i : Fin n) (j : Fin (n-i)) : Elem := sorry


/-- Access an element of LowerTriangularArray given `(i : Fin n)` and `(j : Fin i)`

It corresponds to the `(i,j)` element of the triangular matrix.

LowerTriangularArray is an array that relates to lower triangular matrix as:
`[x[0,0], 
 x[1,0], x[1,1], 
    ⁞            ⋱, 
 x[n-1,0], ...     , x[n-1,n-1]]`
-/
def lowerTriangularArrayGet (upperTriangular : Cont ((n*(n+1))/2)) (i : Fin n) (j : Fin (i+1)) : Elem := sorry


----------------------------------------------------------------------


-- Maybe switch to `(ab : (Fin n → ℝ) × (Fin (n-1) → ℝ))` then we have linearity in `ab`
-- However, this switch causes some issues in proving smoothenss of `linearInterpolate` for some reason
def upper2DiagonalUpdate [Vec Elem] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : Cont n) : Cont n := 
  if n = 0 then x
  else Id.run do
    let mut x := x
    for i in [0:n-1] do
      let i : Fin n := ⟨i,sorry_proof⟩
      x[i] := a i • x[i] + b ⟨i.1,sorry_proof⟩ • x[⟨i.1+1,sorry_proof⟩]
    let last : Fin n := ⟨n-1, sorry_proof⟩
    x[last] := a last • x[last]
    x

def lower2DiagonalUpdate [Vec Elem] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : Cont n) : Cont n := 
  if n = 0 then x
  else Id.run do
    let mut x := x
    for i in [1:n] do
      let i : Fin n := ⟨i,sorry_proof⟩
      x[i] := a i • x[i] + b ⟨i.1-1,sorry_proof⟩ • x[⟨i.1-1,sorry_proof⟩]
    let first : Fin n := ⟨0, sorry_proof⟩
    x[first] := a first • x[first]
    x


-- function_properties upper2DiagonalUpdate [Vec Elem] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : Cont n) : Cont n
-- argument a 
--   isLin [Fact (b=0)] := sorry_proof,
--   isSmooth  := sorry_proof,
--   diff_simp := mapIdx (λ i (xi : Elem) => da i * xi) x by sorry_proof
-- argument b
--   isLin [Fact (a=0)] := sorry_proof,
--   isSmooth  := sorry_proof,
--   diff_simp := upper2DiagonalUpdate 0 db x by sorry_proof
-- argument x
--   isLin := sorry_proof,
--   isSmooth, diff_simp

-- function_properties upper2DiagonalUpdate [SemiHilbert Elem] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : Cont n) : Cont n
-- argument x 
--   hasAdjoint := sorry_proof,
--   adj_simp   := lower2DiagonalUpdate a b x' by sorry_proof,
--   hasAdjDiff := by constructor; infer_instance; simp; infer_instance,
--   adjDiff_simp by simp[adjointDifferential]

-- function_properties lower2DiagonalUpdate [Vec Elem] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : Cont n) : Cont n
-- argument a 
--   isLin [Fact (b=0)] := sorry_proof,
--   isSmooth  := sorry_proof,
--   diff_simp := mapIdx (λ i (xi : Elem) => da i * xi) x by sorry_proof
-- argument b
--   isLin [Fact (a=0)] := sorry_proof,
--   isSmooth  := sorry_proof,
--   diff_simp := lower2DiagonalUpdate 0 db x by sorry_proof
-- argument x 
--   isLin := sorry_proof,
--   isSmooth, diff_simp

-- function_properties lower2DiagonalUpdate [SemiHilbert Elem] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : Cont n) : Cont n
-- argument x 
--   hasAdjoint := sorry_proof,
--   adj_simp   := upper2DiagonalUpdate a b x' by sorry_proof,
--   hasAdjDiff := by constructor; infer_instance; simp; infer_instance,
--   adjDiff_simp by simp[adjointDifferential]


-- These theorems are usefull when differentiating `upper2DiagonalUpdate` w.r.t to `a` and `b`
-- This happens for example in `linearInterpolate`
@[simp]
theorem mapIdx_add_upper2DiagonalUpdate_0_b [Vec Elem] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : Cont n)
  : mapIdx (λ i (xi : Elem) => a i • xi) x + upper2DiagonalUpdate 0 b x = upper2DiagonalUpdate a b x := sorry_proof

@[simp]
theorem mapIdx_add_lower2DiagonalUpdate_0_b [Vec Elem] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : Cont n)
  : mapIdx (λ i (xi : Elem) => a i • xi) x + lower2DiagonalUpdate 0 b x = lower2DiagonalUpdate a b x := sorry_proof



----------------------------------------------------------------------


def differences [Vec Elem] {n} (x : Cont (n+1)) : Cont n := 
  x |> upper2DiagonalUpdate (λ _ => 1) (λ _ => -1)
    |> dropElem 1

-- function_properties differences [Vec Elem] {n} (x : Cont (n+1)) : Cont n
-- argument x
--   isLin := sorry_proof,
--   isSmooth, diff_simp

-- function_properties differences [SemiHilbert Elem] {n} (x : Cont (n+1)) : Cont n
-- argument x
--   hasAdjoint,
--   hasAdjDiff,
--   adjDiff


-- Maybe custom implementation that does:
--   `y[i] := x[i] + t * (x[i+1] - x[i])`
-- instead of
--   `y[i] := (1-t) * x[i] + t * x[i+1]`
def linearInterpolate [Vec Elem] {n} (t : ℝ) (x : Cont (n+1)) : Cont n := 
  x |> upper2DiagonalUpdate (λ _ => (1-t)) (λ _ => t)
    |> dropElem 1


-- function_properties linearInterpolate [Vec Elem] {n} (t : ℝ) (x : Cont (n+1)) : Cont n
-- argument t
--   isSmooth, diff
-- argument x
--   isLin := sorry_proof,
--   isSmooth, diff_simp

-- function_properties linearInterpolate [SemiHilbert Elem] {n} (t : ℝ) (x : Cont (n+1)) : Cont n
-- argument x
--   hasAdjoint, adj,
--   hasAdjDiff, adjDiff
