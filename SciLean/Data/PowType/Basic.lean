import SciLean.Data.FunType

namespace SciLean

-- PowType is just like FunType where the type `T` is not important
-- The main example `ℝ^n`, it bahaves like `Fin n → ℝ` but we do not 
-- care too much about what exactly `T` is. 
-- PowType provides notation `ℝ^Fin n`, we also have short hand `ℝ^{n}`.
open FunType in
class PowType (T : outParam Type) (I X : Type) extends GenericArray T I X

abbrev PowTypeCarrier (X I : Type) {T : outParam Type} [PowType T I X] := T

notation X "^" I => PowTypeCarrier X I

-- Allow notation like ℝ^{n,m,k}
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

-- Allow notation like `A[x,y]` instead of `A[(x,y)]` and A[i,:] or A[:,j]
-- Maybe:
--   1. A[i,·]  : Fin m → ℝ
--   2. A[i,:]  : ℝ^{m}
-- TODO: Generalize this
macro A:term  noWs "[" id1:term "," id2:term "]" : term => `($A[($id1, $id2)])
macro A:term  noWs "[" id1:term "," id2:term "," id3:term "]" : term => `($A[($id1, $id2, $id3)])
macro A:term  noWs "[" id1:term "," id2:term "," id3:term "," id4:term "]" : term => `($A[($id1, $id2, $id3, $id4)])
macro A:term  noWs "[" id1:term "," ":" "]" : term => `(λ [j] => $A[($id1, j)])
macro A:term  noWs "[" ":" "," id2:term "]" : term => `(λ [i] => $A[(i, $id2)])

namespace PowTypeCarrier

  variable {X I} {T : outParam Type} [Enumtype I] [PowType T I X] -- [Inhabited X]

  @[defaultInstance]
  instance : FunType (X^I) I X := by infer_instance 
  @[defaultInstance]
  instance : FunType.HasSet (X^I) := by infer_instance 
  @[defaultInstance]
  instance : FunType.HasIntro (X^I) := by infer_instance 
  @[defaultInstance]
  instance : GenericArray (X^I) I X := by infer_instance 

  abbrev get (x : X^I) (i : I) : X := getElem x i True.intro
  abbrev set (x : X^I) (i : I) (xi : X) : X^I := setElem x i xi
  abbrev intro (f : I → X) : X^I := FunType.intro _ f
  abbrev modify [Inhabited X] (x : X^I) (i : I) (f : X → X) : X^I := FunType.modify x i f
  abbrev mapIdx (f : I → X → X) (x : X^I) : X^I := FunType.mapIdx f x
  abbrev map (f : X → X) (x : X^I) : X^I := FunType.map f x

  -- variable [∀ n, PowType T (Fin n) X]
  
  def split {n m : Nat} 
    {Tn : outParam Type} [PowType Tn (Fin n) X]  
    {Tm : outParam Type} [PowType Tm (Fin m) X]  
    {Tnm : outParam Type} [PowType Tnm (Fin (n+m)) X]  
    (x : X^{n+m}) : X^{n} × X^{m} := 
    (λ [i] => x[⟨i.1,sorry_proof⟩], λ [i] => x[⟨i.1+n,sorry_proof⟩])

  def split3 {n m k : Nat} 
    {Tn : outParam Type} [PowType Tn (Fin n) X]  
    {Tm : outParam Type} [PowType Tm (Fin m) X]  
    {Tk : outParam Type} [PowType Tk (Fin k) X]  
    {Tnmk : outParam Type} [PowType Tnmk (Fin (n+m+k)) X]  
    (x : X^{n+m+k}) : X^{n} × X^{m} × X^{k} := 
    (λ [i] => x[⟨i.1,sorry_proof⟩], 
     λ [i] => x[⟨i.1+n,sorry_proof⟩],
     λ [i] => x[⟨i.1+n+m,sorry_proof⟩])

  def merge {n m : Nat} 
    {Tn : outParam Type} [PowType Tn (Fin n) X]  
    {Tm : outParam Type} [PowType Tm (Fin m) X]  
    {Tnm : outParam Type} [PowType Tnm (Fin (n+m)) X]  
    (x : X^{n}) (y : X^{m})  : X^{n+m} := 
    (λ [i] => if i.1 < n 
              then x[⟨i.1,sorry_proof⟩]
              else y[⟨i.1-n, sorry_proof⟩])
  -- abbrev concat {n m : Nat} (x : X^{n}) (y : X^{m}) : X^{n+m} := x.merge y

  abbrev Index (_ : X^I) := I
  abbrev Value (_ : X^I) := X

  section Updates

  variable {n} [Vec X] {T : outParam Type} [PowType T (Fin n) X]
  def upper2DiagonalUpdate (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : X^{n}) : X^{n} := 
    if n = 0 then x
    else Id.run do
      let mut x := x
      for i in [0:n-1] do
        let i : Fin n := ⟨i,sorry_proof⟩
        x[i] := a i * x[i] + b ⟨i.1,sorry_proof⟩ * x[⟨i.1+1,sorry_proof⟩]
      let last : Fin n := ⟨n-1, sorry_proof⟩
      x[last] := a last * x[last]
      x

  def lower2DiagonalUpdate [Vec X] (a : Fin n → ℝ) (b : Fin (n-1) → ℝ) (x : X^{n}) : X^{n} := 
    if n = 0 then x
    else Id.run do
      let mut x := x
      for i in [1:n] do
        let i : Fin n := ⟨i,sorry_proof⟩
        x[i] := a i * x[i] + b ⟨i.1-1,sorry_proof⟩ * x[⟨i.1-1,sorry_proof⟩]
      let first : Fin n := ⟨0, sorry_proof⟩
      x[first] := a first * x[first]
      x

  variable {k} {Tnk : outParam Type} [PowType Tnk (Fin (n+k)) X]

  def drop (x : X^{n+k}) (k : Nat) : X^{n} := sorry
  def push (x : X^{n+k}) (k : Nat := 1) (val : X) : X^{n} := sorry

  end Updates

end PowTypeCarrier

-- namespace PowTypeCarrier

--   def reshape {I J} [Enumtype I] [Enumtype J] [PowType  (x : ℝ^I) (h : numOf I = numOf J) : ℝ^J :=
--     ⟨x.1, h ▸ x.2⟩

-- end PowTypeCarrier

instance {T I X} [PowType T I X] [Enumtype I] [ToString I] [ToString X] : ToString (X^I) :=
  ⟨λ x => Id.run do
    let mut s := ""
    for (i,li) in Enumtype.fullRange I do
      if li.1 = 0 then
        s := s.append s!"{i}: {x[i]}"
      else 
        s := s.append s!", {i}: {x[i]}"
    "{" ++ s ++ "}"⟩

-- variable (x : ℝ^{3,22,10})
-- #check λ (i,j,k) => x[(i,j,k)]

-- namespace PowType

--   @[simp]
--   theorem sum_intro {ι} [Enumtype ι]
--     [PowType α] [Add α] [Zero α] [Zero (Idx n → α)] [Add (Idx n → α)]
--     (f : ι → Idx n → α) 
--     : (∑ i, PowType.intro (f i)) = (PowType.intro (∑ i, f i))
--     := 
--   by
--     admit

--   @[simp]
--   theorem add_intro 
--     (f g : Idx n → α) [PowType α] [Add α]
--     : 
--       (PowType.intro f)  + (PowType.intro g)
--       = 
--       (PowType.intro λ i => f i + g i)
--     := 
--   by
--     admit

--   @[simp]
--   theorem sub_intro 
--     (f g : Idx n → α) [PowType α] [Sub α]
--     : 
--       (PowType.intro f)  - (PowType.intro g)
--       = 
--       (PowType.intro λ i => f i - g i)
--     := 
--   by
--     admit


--   @[simp]
--   theorem hmul_intro 
--     (f : Idx n → α) [PowType α] [HMul β α α] (b : β)
--     :
--       b * (PowType.intro f) = PowType.intro λ i => b * f i
--     := 
--   by 
--     admit
