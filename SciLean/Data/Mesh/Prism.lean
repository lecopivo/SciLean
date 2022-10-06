import SciLean.Prelude
import SciLean.Mathlib.Data.Enumtype
import SciLean.Algebra
import SciLean.Data.FinProd
import SciLean.Data.ArrayN
import SciLean.Data.DataArray
import SciLean.Data.Mesh.PrismRepr
import SciLean.Data.Quotient.GradedQuotient

namespace SciLean

structure Prism where
  repr : PrismRepr
  repr_IsCanonical : repr.IsCanonical
deriving DecidableEq

structure Face (P : Prism) (dim : Option Nat := none) where
  repr : FaceRepr
  repr_ofPrism : repr.ofPrism = P.repr
  repr_dim : repr.dim = dim.getD repr.dim
deriving DecidableEq

structure Inclusion (Q : Prism) (P : Prism) where
  repr : FaceRepr
  repr_ofPrism : repr.ofPrism = P.repr
  repr_toPrism : repr.toPrism.toCanonical = Q.repr
deriving DecidableEq

namespace Prism

def dim (P : Prism) : Nat := P.repr.dim
def faceCount (n : Nat) (P : Prism) : Nat := P.repr.faceCount n
abbrev pointCount (P : Prism) : Nat := P.faceCount 0
abbrev edgeCount  (P : Prism) : Nat := P.faceCount 1

def toString (P : Prism) : String := P.repr.toString
instance : ToString Prism := ⟨λ P => P.toString⟩

instance : One Prism := ⟨.point, by simp⟩
instance : Inhabited Prism := ⟨.point, by simp⟩

def cone (P : Prism) : Prism := ⟨P.repr.cone, by apply PrismRepr.IsCanonical.cone; apply P.2; done⟩
def prod (P Q : Prism) : Prism := ⟨P.repr.prod Q.repr |>.toCanonical, by simp⟩
instance : Mul Prism := ⟨λ P Q => P.prod Q⟩

abbrev Space (P : Prism) := ℝ^{P.dim}

def inPrism (P : Prism) (x : ℝ^{P.dim}) : Bool := 
  match P with
  | ⟨.point, _⟩ => x = 0
  | ⟨.cone Q, _⟩ => 
    let Q : Prism := ⟨Q, sorry_proof⟩
    let x : ℝ^{Q.dim + 1} := x 
    let t : ℝ := x[⟨Q.dim, by simp⟩]
    let y : ℝ^{Q.dim} := λ [i] => x[⟨i.1, sorry_proof⟩]
    if t = 1 then
      x = 0
    else 
      Q.inPrism (1/(1-t) * y)
  | ⟨.prod P₁ P₂, _⟩ =>
    let P₁ : Prism := ⟨P₁, sorry_proof⟩
    let P₂ : Prism := ⟨P₂, sorry_proof⟩
    let x₁ : ℝ^{P₁.dim} := λ [i] => x[⟨i.1, sorry_proof⟩]
    let x₂ : ℝ^{P₂.dim} := λ [i] => x[⟨P₁.dim + i.1, sorry_proof⟩]
    (P₁.inPrism x₁) ∧ (P₂.inPrism x₂)

def InPrism (P : Prism) (x : ℝ^{P.dim}) : Prop := (P.inPrism x = true)

def point : Prism := 1
def segment := point.cone

def triangle := segment.cone
def square   := segment*segment

def tet     := triangle.cone
def pyramid := square.cone
def prism   := segment*triangle
def cube    := segment*square

-- def Foo (P : Prism) : Type :=
--   match P.repr with
--   | .point => Int
--   | .cone .point => Int
--   | .prod (.cone .point) (.cone .point) => Float
--   | _ => Empty

-- example : Foo point = Int   := by rfl
-- example : Foo segment = Int := by rfl
-- example : Foo square = Float  := by rfl 
-- example : Foo cube = Empty  := by rfl

-- def a : Foo point   := (5 : Int)
-- def b : Foo segment := (5 : Int)
-- def c : Foo square  := (5 : Float) -- This does not work :( -- The PrismRepr.toCanonical needs better implementation

/-- Number of prism in dimension `dim`

I'm fairly confident that prisms in dimension `d` are the same as unlabeled rooted trees on `d` vertices
https://oeis.org/A000081

-/
def prismCount : (dim : Nat) → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 9
  | 5 => 20 
  | 6 => 48
  | 7 => 115
  | _ => panic! "Number of prism for dim>4 is currently unknown! Implement this!"


/-- Number of prisms of dimension at most `dim` -/
def prismCumCount : (dim : Nat) → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 17
  | 5 => 37 
  | 6 => 85
  | 7 => 200
  | _ => panic! "Number of prism for dim>4 is currently unknown! Implement this!"

/-- Number of prime prisms in dimension `dim`

Prism is prime if it cannot be written as a produce of two non-trivial prism.
-/
def primePrismCount : (dim : Nat) → Nat
  | 0 => 0
  | n+1 => prismCount n

/-- Number of prime prisms of dimension at most `dim` -/
def primePrismCumCount : (dim : Nat) → Nat
  | 0 => 0
  | n+1 => prismCumCount n

def prismFromFin : (dim : Nat) → (Fin (prismCount dim)) → Prism
  | 0, ⟨0,_⟩ => point
  | 1, ⟨0,_⟩ => segment
  | 2, ⟨0,_⟩ => triangle
  | 2, ⟨1,_⟩ => square
  | 3, ⟨0,_⟩ => tet
  | 3, ⟨1,_⟩ => pyramid
  | 3, ⟨2,_⟩ => prism
  | 3, ⟨3,_⟩ => cube
  | 4, ⟨0,_⟩ => tet.cone
  | 4, ⟨1,_⟩ => pyramid.cone
  | 4, ⟨2,_⟩ => prism.cone
  | 4, ⟨3,_⟩ => cube.cone
  | 4, ⟨4,_⟩ => Prism.prod segment tet
  | 4, ⟨5,_⟩ => Prism.prod segment pyramid
  | 4, ⟨6,_⟩ => Prism.prod segment prism
  | 4, ⟨7,_⟩ => Prism.prod segment cube
  | 4, ⟨8,_⟩ => Prism.prod triangle triangle
  | _, _ => panic! "Getting prism from Fin n is not implemented for dim > 4!"

def prismFromNat : Nat → Prism
  | 0 => point
  | 1 => segment
  | 2 => triangle
  | 3 => square
  | 4 => tet
  | 5 => pyramid
  | 6 => prism
  | 7 => cube
  | 8 => tet.cone
  | 9 => pyramid.cone
  | 10 => prism.cone
  | 11 => cube.cone
  | 12 => Prism.prod segment tet
  | 13 => Prism.prod segment pyramid
  | 14 => Prism.prod segment prism
  | 15 => Prism.prod segment cube
  | 16 => Prism.prod triangle triangle
  | _ => panic! "Getting prism from Nat is not implemented for dim > 4!"

def primePrismFromNat : Nat → Prism
  | 0 => segment
  | 1 => triangle
  | 2 => tet
  | 3 => pyramid
  | 4 => tet.cone
  | 5 => pyramid.cone
  | 6 => prism.cone
  | 7 => cube.cone
  | _ => panic! "Getting prime prism from Nat is not implemented for dim > 4!"

def prismToFin (P : Prism) : Fin (prismCount P.dim) :=
  match P with
  -- 0D
  | ⟨.point, _⟩ => ⟨0, sorry_proof⟩
  -- 1D
  | ⟨.cone .point, _⟩ => ⟨0, sorry_proof⟩
  -- 2D
  | ⟨.cone (.cone .point), _⟩ => ⟨0, sorry_proof⟩
  | ⟨.prod (.cone .point) (.cone .point), _⟩ => ⟨1, sorry_proof⟩
  -- 3D
  | ⟨.cone (.cone (.cone .point)), _⟩ => ⟨0, sorry_proof⟩
  | ⟨.cone (.prod (.cone .point) (.cone .point)), _⟩ => ⟨1, sorry_proof⟩
  | ⟨.prod (.cone .point) (.cone (.cone .point)), _⟩ => ⟨2, sorry_proof⟩
  | ⟨.prod (.cone .point) (.prod (.cone .point) (.cone .point)), _⟩ => ⟨3, sorry_proof⟩
  -- 4D
  | ⟨.cone (.cone (.cone (.cone .point))), _⟩ => ⟨0, sorry_proof⟩
  | ⟨.cone (.cone (.prod (.cone .point) (.cone .point))), _⟩ => ⟨1, sorry_proof⟩
  | ⟨.cone (.prod (.cone .point) (.cone (.cone .point))), _⟩ => ⟨2, sorry_proof⟩
  | ⟨.cone (.prod (.cone .point) (.prod (.cone .point) (.cone .point))), _⟩ => ⟨3, sorry_proof⟩
  | ⟨.prod (.cone .point) (.cone (.cone (.cone .point))), _⟩ => ⟨4, sorry_proof⟩
  | ⟨.prod (.cone .point) (.cone (.prod (.cone .point) (.cone .point))), _⟩ => ⟨5, sorry_proof⟩
  | ⟨.prod (.cone .point) (.prod (.cone .point) (.cone (.cone .point))), _⟩ => ⟨6, sorry_proof⟩
  | ⟨.prod (.cone .point) (.prod (.cone .point) (.prod (.cone .point) (.cone .point))), _⟩ => ⟨7, sorry_proof⟩
  | ⟨.prod (.cone (.cone .point)) (.cone (.cone .point)), _⟩ => ⟨8, sorry_proof⟩

  | P => 
    have : Inhabited (Fin (prismCount P.dim)) := cast sorry_proof (⟨0, sorry_proof⟩ : Fin 1)
    panic! "Getting prism from Fin n is not implemented for dim > 4!"


def firstFace (P : Prism) (n : Option Nat := none) : Option (Face P n) :=
  match n with
  | none => match P.1.first 0 with
    | some f => ⟨f, sorry_proof, sorry_proof⟩ |> some
    | none => none
  | some n =>
  match P.1.first n with
  | some f => ⟨f, sorry_proof, sorry_proof⟩ |> some
  | none => none

/-- For prism `P = P₁ × ... × Pₘ` return `[P₁, ..., Pₘ]` i.e. list of all product factors. -/
def prodSplit (P : Prism) : List (Prism) := 
  if P.1 = .point 
  then []
  else P.1.prodSplit.map (λ Pi => ⟨Pi, sorry_proof⟩) 


opaque prodTally (P : Prism) : List (Prism × Nat) := 
  -- This implementation exploits the fact that P.prodSplit is ordered!
  let prod := P.prodSplit
  match prod.head? with
  | some head =>
    let (last, tally) : (Prism × Nat) × List (Prism × Nat) :=
      prod.tail.foldl (λ ((current,count), tally') P => 
        if P = current then
          ((current, count + 1), tally')
        else
          ((P,1), (current, count) :: tally')
        ) ((head,1), [])
    (last :: tally).reverse
  | none => []

/-- For a list `[(P₁,n₁), ... , (Pₘ,nₘ)]` construct `P = P₁^n₁ × ... × Pₘ^nₘ` -/
def listProd (Ps : List (Prism × Nat)) : Prism := 
  let rec prod (Qs : List (Prism × Nat)) : PrismRepr :=
    match Qs with
    | [] => .point
    | [(P,1)] => P.1
    | (_, 0) :: Ps => prod Ps
    | (P, n+1) :: Ps => P.1 * prod ((P,n) :: Ps)
  ⟨prod Ps |>.toCanonical, by simp⟩

def primePowers (P : Prism) : ArrayN Nat (primePrismCumCount P.dim) := 
  match P with
  -- 0D
  | ⟨.point, _⟩ => ⟨#[], by simp[dim]⟩
  -- 1D
  | ⟨.cone .point, _⟩ => ⟨#[1], by simp[dim]⟩
  -- 2D
  | ⟨.cone (.cone .point), _⟩ => ⟨#[0,1], by simp[dim]⟩
  | ⟨.prod (.cone .point) (.cone .point), _⟩ => ⟨#[2,0], by simp[dim]⟩
  -- 3D
  | ⟨.cone (.cone (.cone .point)), _⟩ => ⟨#[0,0,1,0], by simp[dim]⟩
  | ⟨.cone (.prod (.cone .point) (.cone .point)), _⟩ => ⟨#[0,0,0,1], sorry_proof⟩
  | ⟨.prod (.cone .point) (.cone (.cone .point)), _⟩ => ⟨#[1,1,0,0], sorry_proof⟩
  | ⟨.prod (.cone .point) (.prod (.cone .point) (.cone .point)), _⟩ => ⟨#[3,0,0,0], sorry_proof⟩
  -- 4D
  | ⟨.cone (.cone (.cone (.cone .point))), _⟩ => ⟨#[0,0,0,0,1,0,0,0], sorry_proof⟩
  | ⟨.cone (.cone (.prod (.cone .point) (.cone .point))), _⟩ => ⟨#[0,0,0,0,0,1,0,0], sorry_proof⟩
  | ⟨.cone (.prod (.cone .point) (.cone (.cone .point))), _⟩ => ⟨#[0,0,0,0,0,0,1,0], sorry_proof⟩
  | ⟨.cone (.prod (.cone .point) (.prod (.cone .point) (.cone .point))), _⟩ => ⟨#[0,0,0,0,0,0,0,1], sorry_proof⟩
  | ⟨.prod (.cone .point) (.cone (.cone (.cone .point))), _⟩ => ⟨#[1,0,1,0,0,0,0,0], sorry_proof⟩
  | ⟨.prod (.cone .point) (.cone (.prod (.cone .point) (.cone .point))), _⟩ => ⟨#[1,0,0,1,0,0,0,0], sorry_proof⟩
  | ⟨.prod (.cone .point) (.prod (.cone .point) (.cone (.cone .point))), _⟩ => ⟨#[2,1,0,0,0,0,0,0], sorry_proof⟩
  | ⟨.prod (.cone .point) (.prod (.cone .point) (.prod (.cone .point) (.cone .point))), _⟩ => ⟨#[4,0,0,0,0,0,0,0], sorry_proof⟩
  | ⟨.prod (.cone (.cone .point)) (.cone (.cone .point)), _⟩ => ⟨#[0,2,0,0,0,0,0,0], sorry_proof⟩
  | _ => panic! "PrimePowers is not implemented for prisms of dimension larger then four!"


end Prism

namespace Face

def dim (f : Face P n) : Nat := n.getD f.repr.dim
def toPrism (f : Face P n) : Prism := ⟨f.1.toPrism.toCanonical, by simp⟩
def ofPrism (_ : Face P n) : Prism := P

def comp (f : Face P n) (g : Face f.toPrism m) : Face P m := 
  ⟨f.repr.comp (g.repr.fromCanonical f.repr.toPrism (by simp[g.2,toPrism] done)) 
   (by simp[g.2, toPrism,f.2]; done), 
   by simp[f.repr_ofPrism], 
   by simp; cases m; simp; simp; rw[g.repr_dim]; simp done⟩

@[simp]
theorem comp_toPrism (f : Face P n) (g : Face f.toPrism m) 
  : (f.comp g).toPrism = g.toPrism := by simp[comp,toPrism]

@[simp]
theorem comp_dim (f : Face P n) (g : Face f.toPrism m) 
  : (f.comp g).dim = g.dim := by simp[comp,dim]

def tip (P : Prism) : Face (P.cone) (some 0) := ⟨.tip P.repr, by simp[FaceRepr.ofPrism,Prism.cone], by simp[FaceRepr.dim, FaceRepr.toPrism]⟩
def cone (f : Face P n) : Face (P.cone) (n.map (·+1)) := ⟨.cone f.repr, by simp[FaceRepr.ofPrism,Prism.cone, f.2], sorry_proof⟩
def base (f : Face P n) : Face (P.cone) n := ⟨.base f.repr, sorry_proof, sorry_proof⟩

instance : Add (Option Nat) := ⟨λ n m => match n, m with | some n, some m => n+m | _, _ => none⟩
def prod (f : Face P n) (g : Face Q m) : Face (P.prod Q) (n+m) := ⟨f.repr.prod g.repr |>.toCanonical, sorry_proof, sorry_proof⟩

def next (f : Face P n) : Option (Face P n) := 
  match f.repr.next with
  | some f' => ⟨f', sorry_proof, sorry_proof⟩ |> some
  | none => 
    match n with
    | some _ => none
    | none => 
      match f.ofPrism.firstFace (some (f.dim+1)) with
      | some f' => ⟨f'.1, f'.2, by simp⟩ |> some
      | none => none

instance (P : Prism) (n)
  : Iterable (Face P n) :=
{
  first := P.firstFace n
  next := λ f => f.next
  decEq := by infer_instance
}

def faces {P : Prism} {n} (f : Face P n) (m : Option Nat := none)  := Iterable.fullRange (Face f.toPrism m)

end Face

namespace Prism

def faces (P : Prism) (n : Option Nat := none)  := Iterable.fullRange (Face P n)

end Prism

namespace Inclusion

def toFace (f : Inclusion Q P) : Face P Q.dim := ⟨f.1, f.2, by simp[Prism.dim, FaceRepr.dim]; rw[← f.3]; simp⟩

def comp (f : Inclusion Q P) (g : Inclusion S Q) : Inclusion S P := 
  ⟨f.repr.comp (g.repr.fromCanonical f.repr.toPrism (by simp[g.2, f.3]; done)) 
   (by simp[g.2, f.2]; done), 
   by simp[f.2] done, 
   by simp[g.3] done⟩

instance : Compose (Inclusion Q P) (Inclusion S Q) (Inclusion S P) where
  compose f g := f.comp g
 
end Inclusion


/-- Decomposition of a prism `P = P₁ * P₂`.

The internal representation of a decomposition is just `Fin n₁ × ... × Fin nₘ` for a prism `P = P₁^n₁ × ... × Pₘ^nₘ`.

When we have and element `(i₁, ..., iₘ) : PrismDecomposition P` we can construct the decomposition of `P` as:

    fst := P₁^i₁ × ... × Pₘ^iₘ
    snd := P₁^(n₁-i₁) × ... × Pₘ^(nₘ-iₘ)
 -/
def PrismDecomposition (P : Prism) := FinProd (P.prodTally.map (·.2+1))

-- with
--   @[computedField]
--   fst : (PrismDecomposition P) → Prism
--   | .powers ns => Prism.listProd <| P.prodTally.map (·.1) |>.zip ns.toList

  -- @[computedField]
  -- snd : (PrismDecomposition P) → Prism
  -- | .powers ns => (Prism.listProd <| P.prodTally.map (·.1) |>.zip ns.toListComplement

--------- PrismDecomposition -----------------------------------------
namespace PrismDecomposition 

variable {l} {P : Prism}

def prisms (dec : PrismDecomposition P) : Prism × Prism :=
  let factors := P.prodTally.map (·.1)
  (Prism.listProd (factors |>.zip dec.toList),
   Prism.listProd (factors |>.zip dec.toListComplement))

/-- Given a prism decomposition `P = P₁ × P₂`, return `P₁` -/
def fst (dec : PrismDecomposition P) : Prism := dec.prisms.1
/-- Given a prism decomposition `P = P₁ × P₂`, return `P₂` -/
def snd (dec : PrismDecomposition P) : Prism := dec.prisms.2

/-- `PrismDecomposition P` truly represents a decomposition of a prism `P` -/
@[simp]
theorem mul_fst_snd (dec : PrismDecomposition P) : dec.fst * dec.snd = P := sorry_proof

instance : Enumtype (PrismDecomposition P) := by simp[PrismDecomposition]; infer_instance

end PrismDecomposition
----------------------------------------------------------------------


--------- Prism ------------------------------------------------------
namespace Prism

/-- Tries to find decomposition of `P` such that `P = P₁ * ??` 
This is of course not possible in general and any excess powers ignored.

TODO: The implementation is really bad!!! Improve it!!
-/
def decomposeBy (P P₁ : Prism) : PrismDecomposition P :=
  let pt  := P.prodTally
  let pt₁ := P₁.prodTally
  
  let pt' := pt.map (λ (Pi, a) =>
    let find := pt₁.find (λ ((Qi, _) : Prism × Nat) => Pi = Qi)
    match find with
    | some (_, b) => (Pi, b % (a+1))
    | none => (Pi, 0))

  let rec fromList {ns} (vals : List Nat) : FinProd ns :=
    match ns, vals with
    | [],  _ => Unit.unit
    | [n], [i] => ⟨i % n, sorry_proof⟩
    | n :: _ :: _, i :: j :: is => (⟨i % n, sorry_proof⟩, fromList (j :: is))
    | _, _ => absurd (a:=True) sorry_proof sorry_proof

  fromList (pt'.map (·.2))

end Prism

--------- Inclusion --------------------------------------------------
namespace Inclusion 

def faceInclusion {P Q} (ι : Inclusion Q P) (x : ℝ^{Q.dim}) : ℝ^{P.dim} := sorry

variable {P Q : Prism}

/-- Splits `Inclusiton Q P` based on the decomposition `P = P₁ * P₂` into two inclusions `Inclusion Q₁ P₁` and `Inclusion Q₂ P₂`. 

TODO: Reinspect this implementation, it was originally written for quotient implementation of Prism and might be problematic
-/
def split (ι : Inclusion Q P) (Pdec : PrismDecomposition P) 
  : (Qdec : PrismDecomposition Q) × Inclusion Qdec.fst Pdec.fst × Inclusion Qdec.snd Pdec.snd 
  := 
  let P₁ := Pdec.fst
  let P₂ := Pdec.snd
  match ι.repr.fromCanonical (P₁.repr.prod P₂.repr) sorry_proof with
  | .prod f g => 
    let Qdec : PrismDecomposition Q := Q.decomposeBy ⟨f.toPrism.toCanonical, sorry_proof⟩
    let ι₁ : Inclusion Qdec.fst Pdec.fst := ⟨f, sorry_proof, sorry_proof⟩
    let ι₂ : Inclusion Qdec.snd Pdec.snd := ⟨g, sorry_proof, sorry_proof⟩
    Sigma.mk Qdec (ι₁,ι₂) --, ι₂)
  | _ =>
    absurd (a := True) sorry_proof sorry_proof /- fromCanonical (P * Q) has to be always a face of type .prod f g -/

end Inclusion
----------------------------------------------------------------------

#check Enumtype.fullRange (PrismDecomposition Prism.cube) 

#eval show IO Unit from do
  for (dec, li) in Enumtype.fullRange (PrismDecomposition (Prism.cube*Prism.triangle*Prism.triangle)) do
    let d : FinProd _ := dec
    IO.println s!"{dec.fst} | {dec.snd} | {d.toList} {d.toListComplement}"

#eval show IO Unit from do
  for (dec, li) in Enumtype.fullRange (PrismDecomposition (Prism.square)) do
    let d : FinProd _ := dec
    IO.println s!"{dec.fst} | {dec.snd} | {d.toList} {d.toListComplement}"

    for e in Prism.square.faces (some 1) do
      let i : Inclusion Prism.segment Prism.square := ⟨e.1, sorry_proof, sorry_proof⟩
      let split := i.split dec
      IO.println s!"{split.2.1.repr} | {split.2.2.repr}"


#eval show IO Unit from do
  for (dec, li) in Enumtype.fullRange (PrismDecomposition (Prism.segment)) do
    let d : FinProd _ := dec
    IO.println s!"{dec.fst} | {dec.snd} | {d.toList} {d.toListComplement}"

    for e in Prism.segment.faces (some 0) do
      let i : Inclusion Prism.point Prism.segment := ⟨e.1, sorry_proof, sorry_proof⟩
      let split := i.split dec
      IO.println s!"{split.2.1.repr} | {split.2.2.repr}"
