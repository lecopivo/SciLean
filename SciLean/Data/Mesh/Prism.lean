import SciLean.Prelude
import SciLean.Mathlib.Data.Enumtype
import SciLean.Algebra
import SciLean.Data.FinProd
import SciLean.Data.ArrayN
import SciLean.Data.Mesh.PrismRepr
import SciLean.Data.Quotient.GradedQuotient
-- import SciLean.Tactic.RemoveLambdaLet

namespace SciLean


macro "quot_lift" : conv => `(simp[Setoid.quotient_of_map])

instance : GradedSetoid PrismRepr TwoLevel where
  r P Q := P.toCanonical = Q.toCanonical
  iseqv := sorry_proof

  OfLevel P lvl := 
    match lvl with
    | .any => True
    | .canonical => P.toCanonical = P

  lvl_order x l l' hl ho := (by cases l; simp; induction l'; simp; cases ho; cases l'; simp; apply hl;)
  every_top _ := by simp
  unique_bottom x y h hx hy := by simp at hx hy; rw [← hx, ← hy]; apply h; done

-- instance Prism.instSetoid : Setoid PrismRepr where
--   r P Q := P.toCanonical = Q.toCanonical
--   iseqv := sorry_proof

def Prism (maxLvl := TwoLevel.any) := GradedQuotient PrismRepr maxLvl

namespace Prism

variable {l : TwoLevel}

instance : Setoid.Map (λ x : PrismRepr => x.toCanonical) := sorry_proof
instance : Setoid.Morphism (λ x : PrismRepr => x.toCanonical) := sorry_proof

def nrepr (P : Prism l) : PrismRepr := P.liftOn (λ P => 
  match P.lvl with
  | .any => P.1.toCanonical 
  | .canonical => P.1
  ) sorry_proof
  -- match P.repr.lvl with
  -- | .any       => P.repr.1.toCanonical
  -- | .canonical => P.repr.1
  -- rewrite_by simp

instance : DecidableEq (Prism l) := λ P Q => if P.nrepr = Q.nrepr then isTrue sorry_proof else isFalse sorry_proof

instance : Setoid.Map (λ P : PrismRepr => P.dim) := sorry_proof
def dim (P : Prism l) : Nat := P.repr.dim rewrite_by quot_lift

instance (n) : Setoid.Map (λ P : PrismRepr => P.faceCount n) := sorry_proof
def faceCount (n : Nat) (P : Prism l) : Nat := P.repr.faceCount n rewrite_by quot_lift

abbrev pointCount (P : Prism l) : Nat := P.faceCount 0
abbrev edgeCount  (P : Prism l) : Nat := P.faceCount 1

def toString (P : Prism l) : String := P.nrepr.toString
instance : ToString (Prism l) := ⟨λ P => P.toString⟩
partial def toDbgString (P : Prism) : String := P.liftOn (λ P => P.1.toString) sorry_proof

instance (lvl : TwoLevel) : GradedSetoid.Reduce PrismRepr lvl where
  reduce P := match lvl with | .any => P | .canonical => P.toCanonical
  reduce_sound := sorry_proof
  reduce_lvl   := sorry_proof


-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.unify true in

@[simp high]
theorem lift_graded_morphism   
  {Lvl : Type u'} [BoundedLattice Lvl] {lvl : Lvl}
  {α : Type u} [GradedSetoid α Lvl] [GradedSetoid.Reduce α lvl]
  {β : Type v} [GradedSetoid β Lvl] [GradedSetoid.Reduce β lvl]
  (f : α → β) [GradedSetoid.Morphism f] 
  (x : α)
  : ⟦lvl| f x⟧ = Quotient.lift (λ (a : GradedSetoid.Repr α lvl) => ⟦GradedSetoid.Repr.mk (f a.1) a.2 sorry_proof sorry_proof⟧) sorry_proof ⟦lvl| x⟧
  := sorry_proof

@[simp]
theorem lift_graded_morphism₂  
  {Lvl : Type u'} {lvl : Lvl} [BoundedLattice Lvl] 
  {α : Type u} [GradedSetoid α Lvl] [GradedSetoid.Reduce α lvl]
  {β : Type v} [GradedSetoid β Lvl] [GradedSetoid.Reduce β lvl]
  {γ : Type v} [GradedSetoid γ Lvl] [GradedSetoid.Reduce γ lvl]
  (f : α → β → γ) [GradedSetoid.Morphism₂ f] 
  (x : α) (y : β)
  : ⟦lvl| f x y⟧ = Quotient.lift₂ (λ (x : GradedSetoid.Repr α lvl) (y : GradedSetoid.Repr β lvl) => ⟦GradedSetoid.Repr.mk (f x.1 y.1) x.2 sorry_proof x.4⟧) sorry_proof ⟦lvl| x⟧ ⟦lvl| y⟧
  := sorry_proof

instance : One (Prism l) := ⟨⟦l| .point⟧⟩
instance : Inhabited (Prism l) := ⟨⟦l| .point⟧⟩

instance : GradedSetoid.Morphism (λ P : PrismRepr => P.cone) := sorry_proof
def cone (P : Prism l) : Prism l := ⟦l| P.repr.cone⟧ rewrite_by quot_lift

instance : Setoid.Morphism₂ (λ P Q : PrismRepr => P.prod Q) := sorry_proof
def prod (P Q : Prism l) : Prism l := ⟦l| P.repr.prod Q.repr⟧ rewrite_by quot_lift
instance : Mul (Prism l) := ⟨λ P Q => P.prod Q⟩

def point : Prism .canonical := 1

def segment := point.cone

def triangle := segment.cone
def square   := segment*segment

def tet     := triangle.cone
def pyramid := square.cone
def prism   := segment*triangle
def cube    := segment*square

instance (l) : Coe (Prism .canonical) (Prism l) := ⟨λ P => ⟦⟨P.nrepr, .canonical, sorry_proof, sorry_proof⟩⟧⟩

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

def prismToFin (P : Prism l) : Fin (prismCount P.dim) :=
  match P.nrepr with
  -- 0D
  | .point => ⟨0, sorry_proof⟩
  -- 1D
  | .cone .point => ⟨0, sorry_proof⟩
  -- 2D
  | .cone (.cone .point) => ⟨0, sorry_proof⟩
  | .prod (.cone .point) (.cone .point) => ⟨1, sorry_proof⟩
  -- 3D
  | .cone (.cone (.cone .point)) => ⟨0, sorry_proof⟩
  | .cone (.prod (.cone .point) (.cone .point)) => ⟨1, sorry_proof⟩
  | .prod (.cone .point) (.cone (.cone .point)) => ⟨2, sorry_proof⟩
  | .prod (.cone .point) (.prod (.cone .point) (.cone .point)) => ⟨3, sorry_proof⟩
  -- 4D
  | .cone (.cone (.cone (.cone .point))) => ⟨0, sorry_proof⟩
  | .cone (.cone (.prod (.cone .point) (.cone .point))) => ⟨1, sorry_proof⟩
  | .cone (.prod (.cone .point) (.cone (.cone .point))) => ⟨2, sorry_proof⟩
  | .cone (.prod (.cone .point) (.prod (.cone .point) (.cone .point))) => ⟨3, sorry_proof⟩
  | .prod (.cone .point) (.cone (.cone (.cone .point))) => ⟨4, sorry_proof⟩
  | .prod (.cone .point) (.cone (.prod (.cone .point) (.cone .point))) => ⟨5, sorry_proof⟩
  | .prod (.cone .point) (.prod (.cone .point) (.cone (.cone .point))) => ⟨6, sorry_proof⟩
  | .prod (.cone .point) (.prod (.cone .point) (.prod (.cone .point) (.cone .point))) => ⟨7, sorry_proof⟩
  | .prod (.cone (.cone .point)) (.cone (.cone .point)) => ⟨8, sorry_proof⟩

  | _ => 
    have : Inhabited (Fin (prismCount P.dim)) := cast sorry_proof (⟨0, sorry_proof⟩ : Fin 1)
    panic! "Getting prism from Fin n is not implemented for dim > 4!"


end Prism


instance : GradedSetoid FaceRepr TwoLevel where
  r f g := f.toCanonical = g.toCanonical
  iseqv := sorry_proof

  OfLevel f lvl := 
    match lvl with
    | .any => True
    | .canonical => f.toCanonical = f

  lvl_order x l l' hl ho := (by cases l; simp; induction l'; simp; cases ho; cases l'; simp; apply hl;)
  every_top _ := by simp
  unique_bottom x y h hx hy := by simp at hx hy; rw [← hx, ← hy]; apply h; done

instance (lvl : TwoLevel) : GradedSetoid.Reduce FaceRepr lvl where
  reduce f := match lvl with | .any => f | .canonical => f.toCanonical
  reduce_sound := sorry_proof
  reduce_lvl   := sorry_proof

def FaceBase (lvl := TwoLevel.any) := GradedQuotient FaceRepr lvl

instance {lvl} : DecidableEq (FaceBase lvl) := λ f g => if (f.nrepr = g.nrepr) then isTrue sorry else isFalse sorry

instance : GradedSetoid.Morphism (λ f : FaceRepr => f.ofPrism) := sorry_proof
def FaceBase.ofPrism (f : FaceBase l) : Prism l := ⟦l| f.repr.ofPrism⟧ rewrite_by simp

instance : Setoid.Map (λ f : FaceRepr => f.dim) := sorry_proof
def FaceBase.dim (f : FaceBase l) : Nat := f.repr.dim rewrite_by simp[Setoid.quotient_of_map]

instance (n) : OfNat (Option ℕ) n := ⟨some n⟩

structure Face (P : Prism lvl) (dim : Option Nat := none) where
  f : FaceBase lvl
  hp : f.ofPrism = P
  hd : f.dim = dim.getD f.dim
deriving DecidableEq

--------- FaceBase ---------------------------------------------------
namespace FaceBase

variable {l}

-- Not a GradedSetoid.Morphism!!!
instance : Setoid.Morphism (λ f : FaceRepr => f.toPrism) := sorry_proof
def toPrism (f : FaceBase l) : Prism l := ⟦l| f.repr.toPrism⟧ rewrite_by simp

def comp (f g : FaceBase l) (h : f.toPrism = g.ofPrism) : FaceBase l :=
  f.liftOn₂ g (λ f g => ⟦⟨f.1.comp (g.normalize.1.fromCanonical f.1.toPrism sorry_proof) sorry_proof, f.2, sorry_proof, f.4⟩⟧) sorry_proof

instance : GradedSetoid.Morphism (λ P : PrismRepr => FaceRepr.tip P) := sorry_proof
def tip (P : Prism l) : FaceBase l := ⟦l| FaceRepr.tip P.repr⟧ rewrite_by simp

instance : GradedSetoid.Morphism (λ f : FaceRepr => f.cone) := sorry_proof
def cone (f : FaceBase l) : FaceBase l := ⟦l| f.repr.cone⟧ rewrite_by simp

instance : GradedSetoid.Morphism (λ f : FaceRepr => f.base) := sorry_proof
def base (f : FaceBase l) : FaceBase l := ⟦l| f.repr.base⟧ rewrite_by simp

instance : Setoid.Morphism₂ (λ f g: FaceRepr => f.prod g) := sorry_proof
def prod (f g : FaceBase l) : FaceBase l := ⟦l| f.repr.prod g.repr⟧ rewrite_by simp

instance : Mul (FaceBase l) := ⟨λ f g => f.prod g⟩

def liftOnP (f : FaceBase l) (P : Prism l) (n : Nat) {α : Type}
       (F : (f : GradedSetoid.Repr FaceRepr l) → 
            (hp : f.1.ofPrism.toCanonical = P.nrepr) → 
            (hd : f.1.dim = n) → α)
       (hf : ∀ f f' hp hp' hd hd', f ≈ f' → F f hp hd = F f' hp' hd')
       (hp : f.ofPrism = P) (hd : f.dim = n) : α 
       :=  
       f.recOn (motive := λ (f' : FaceBase l) => (f'.ofPrism = P) → (f'.dim = n) → α)
           (λ f hp hd => F f sorry_proof sorry_proof) sorry_proof hp hd


end FaceBase
----------------------------------------------------------------------


--------- Face -------------------------------------------------------
namespace Face 

variable {l} {P : Prism l} {n : Option Nat}

abbrev nrepr (f : Face P n) : FaceRepr := f.1.nrepr

noncomputable
abbrev grepr (f : Face P n) : GradedSetoid.Repr FaceRepr l := f.1.grepr

noncomputable
abbrev repr (f : Face P n) : FaceRepr := f.1.repr

def lift (f : Face P n)
       (F : (f : GradedSetoid.Repr FaceRepr l) → 
            (hp : f.1.ofPrism.toCanonical = P.nrepr) → 
            (hd : (match n with | some n => (f.1.dim = n) | none => True)) → α) 
       (hf : ∀ f f' hp hp' hd hd', f ≈ f' → F f hp hd = F f' hp' hd')
       (f : Face P n) : α 
       :=
       f.1.liftOnP P (match n with | some n => n | none => f.1.dim) (λ f hp hd => F f hp sorry_proof) sorry_proof f.2 sorry_proof

-- Not a GradedSetoid.Morphism!!!
instance : Setoid.Morphism (λ f : FaceRepr => f.toPrism) := sorry_proof
def toPrism (f : Face P n) : Prism l := ⟦l| f.repr.toPrism⟧ rewrite_by simp

abbrev ofPrism (_ : Face P n) : Prism l := P

def dim (f : Face P n) : Nat :=
  match n with
  | some n => n
  | none => f.1.dim

def comp (f : Face P n) (g : Face f.toPrism m) : Face P m := 
  ⟨f.1.comp g.1 sorry_proof, sorry_proof, sorry_proof⟩

@[simp]
theorem comp_toPrism (f : Face P n) (g : Face f.toPrism m) 
  : (f.comp g).toPrism = g.toPrism := sorry_proof

@[simp]
theorem comp_dim (f : Face P n) (g : Face f.toPrism m) 
  : (f.comp g).dim = g.dim := sorry_proof

def tip (P : Prism l) : Face (P.cone) (P.dim) := ⟨FaceBase.tip P, sorry_proof, sorry_proof⟩
def cone (f : Face P n) : Face (P.cone) (n.map (·+1)) := ⟨f.1.cone, sorry_proof, sorry_proof⟩
def base (f : Face P n) : Face (P.cone) n := ⟨f.1.base, sorry_proof, sorry_proof⟩
def prod (f : Face P n) (g : Face Q m) : Face (P*Q) (match n, m with | some n, some m => n+m | _, _ => none) := ⟨f.1*g.1, sorry_proof, sorry_proof⟩

instance {n m : Nat} : HMul (Face P n) (Face Q m) (Face (P*Q) (n+m)) := ⟨λ f g => f.prod g⟩

end Face
----------------------------------------------------------------------

-- Inclusion of Q's `n`-faces to P
-- Can we remove `n`? The problem is that without explicit `n` the `CoeFun` is not synthesized properly
-- If the dimension a face `g` does not match the dimension of the inclusion `f`
-- 
structure Inclusion (Q P : Prism l) where
  face : FaceBase l
  source : Q = face.toPrism
  target : P = face.ofPrism

--------- Inclusion --------------------------------------------------
namespace Inclusion 

def toFace {Q P : Prism l} (ι : Inclusion Q P) : Face P := ⟨ι.1, sorry_proof /- ι.3 -/, by simp⟩

def comp {S Q P : Prism l} (f : Inclusion Q P) (g : Inclusion S Q) : Inclusion S P := ⟨f.1.comp g.1 sorry_proof, sorry_proof, sorry_proof⟩

instance : Compose (Inclusion Q P) (Inclusion S Q) (Inclusion S P) where
  compose f g := f.comp g

-- instance (P Q : Prism l) : CoeFun (Inclusion P Q n) (λ _ => Face Q n → Face P n) := ⟨λ f g => f.val.comp (f.domain ▸ g)⟩
-- def cast (f : Inclusion P Q n) {m} : Inclusion P Q m := ⟨f.1,f.2⟩

-- variable (P Q : Prism l) (n m) (f : Inclusion P Q n) (g : Face Q n) (h : Face Q m)

-- #check f g
-- #check f.cast h

-- #check f.cast
  
end Inclusion
----------------------------------------------------------------------

--------- Prism ------------------------------------------------------
namespace Prism

variable {l : TwoLevel}

def first (P : Prism l) (n : Option Nat := none) : Option (Face P n) := 
  P.liftOn (λ P => 
  match n with
  | none => match P.1.first 0 with
    | some f => some ⟨⟦⟨f, l, sorry_proof, sorry_proof⟩⟧, sorry_proof, sorry_proof⟩
    | none => none
  | some n =>
  match P.1.first n with
  | some f => some ⟨⟦⟨f, l, sorry_proof, sorry_proof⟩⟧, sorry_proof, sorry_proof⟩
  | none => none) sorry_proof

end Prism
----------------------------------------------------------------------

--------- Face -------------------------------------------------------
namespace Face

variable {l : TwoLevel}

def next {P : Prism l} {n} (f : Face P n) : Option (Face P n) :=
  f.1.liftOn (λ f' => 
    match f'.1.next with
    | some f => some ⟨⟦⟨f, l, sorry_proof, sorry_proof⟩⟧, sorry_proof, sorry_proof⟩
    | none => 
      match n with
      | some _ => none
      | none => 
        match f'.1.ofPrism.first (f'.1.dim+1) with
        | some f => some ⟨⟦⟨f, l, sorry_proof, sorry_proof⟩⟧, sorry_proof, sorry_proof⟩
        | none => none
    ) sorry_proof

instance : ToString (Face P n) := ⟨λ P => P.1.liftOn (λ P => P.normalize.1.toString) sorry_proof⟩

instance (P : Prism l) (n)
  : Iterable (Face P n) :=
{
  first := P.first n
  next := λ f => f.next
  decEq := by infer_instance
}

def faces {P : Prism l} {n} (f : Face P n) (m : Option Nat := none)  := Iterable.fullRange (Face f.toPrism m)

end Face
----------------------------------------------------------------------

--------- Prism ------------------------------------------------------
namespace Prism

def faces (P : Prism l) (n : Option Nat := none) := Iterable.fullRange (Face P n)

def test (P : Prism l) : IO Unit := do
  for f in P.faces do
    IO.println s!"dim: {f.dim} | {f}"
    IO.print "       "
    for g in f.faces do
      IO.print s!"| {g} | {f.comp g} "
    IO.println ""
  pure ()

#eval test (point*prism*point)
#eval triangle*segment = prism


/-- For prism `P = P₁ × ... × Pₘ` return `[P₁, ..., Pₘ]` i.e. list of all product factors. -/
def prodSplit (P : Prism l) : List (Prism l) := 
  P.nrepr.prodSplit.map (λ P => ⟦l| P⟧)

/-- For prism `P = P₁^n₁ × ... × Pₘ^nₘ` return `[(P₁,n₁), ..., (Pₘ,nₘ)]` i.e. list of all unique product factors with their powers. 

TODO: This function is causing deterministic timeout of whnf. Thus it is marked as opaque to prevent reduction throught it.
-/
opaque prodTally (P : Prism l) : List (Prism l × Nat) := 
  -- This implementation exploits the fact that P.prodSplit is ordered!
  let prod := P.prodSplit
  match prod.head? with
  | some head =>
    let (last, tally) : (Prism l × Nat) × List (Prism l × Nat) :=
      prod.tail.foldl (λ ((current,count), tally') P => 
        if P = current then 
          ((current, count + 1), tally')
        else
          ((P,1), (current, count) :: tally')
        ) ((head,1), [])
    (last :: tally).reverse
  | none => []

def primePowers (P : Prism l) : ArrayN Nat (primePrismCumCount P.dim) := sorry

/-- For a list `[(P₁,n₁), ... , (Pₘ,nₘ)]` construct `P = P₁^n₁ × ... × Pₘ^nₘ` -/
def listProd : (Ps : List (Prism l × Nat)) → Prism l
  | [] => Prism.point
  | [(P,1)] => P
  | (_, 0) :: Ps => listProd Ps
  | (P, n+1) :: Ps => P * listProd ((P,n) :: Ps)
  
end Prism
----------------------------------------------------------------------

/-- Decomposition of a prism `P = P₁ * P₂`.

The internal representation of a decomposition is just `Fin n₁ × ... × Fin nₘ` for a prism `P = P₁^n₁ × ... × Pₘ^nₘ`.

When we have and element `(i₁, ..., iₘ) : PrismDecomposition P` we can construct the decomposition of `P` as:

    fst := P₁^i₁ × ... × Pₘ^iₘ
    snd := P₁^(n₁-i₁) × ... × Pₘ^(nₘ-iₘ)
 -/
def PrismDecomposition (P : Prism l) := FinProd (P.prodTally.map (·.2+1))

--------- PrismDecomposition -----------------------------------------
namespace PrismDecomposition 

variable {l} {P : Prism l}

def prisms (dec : PrismDecomposition P) : Prism l × Prism l :=
  let factors := P.prodTally.map (·.1)
  (Prism.listProd (factors |>.zip dec.toList),
   Prism.listProd (factors |>.zip dec.toListComplement))

/-- Given a prism decomposition `P = P₁ × P₂`, return `P₁` -/
def fst (dec : PrismDecomposition P) : Prism l := dec.prisms.1
/-- Given a prism decomposition `P = P₁ × P₂`, return `P₂` -/
def snd (dec : PrismDecomposition P) : Prism l := dec.prisms.2

/-- `PrismDecomposition P` truly represents a decomposition of a prism `P` -/
@[simp]
theorem mul_fst_snd (dec : PrismDecomposition P) : dec.fst * dec.snd = P := sorry_proof

instance : Enumtype (PrismDecomposition P) := by simp[PrismDecomposition]; infer_instance

end PrismDecomposition 
----------------------------------------------------------------------

-- Alternative definition for decomposition
structure PrismDecomposition' (P : Prism l) where 
  power : ArrayN Nat (Prism.primePrismCumCount P.dim)
  bound : ∀ i, power[i] ≤ P.primePowers[i]

namespace PrismDecomposition'

-- def fst (dec : PrismDecomposition P) : Prism l × Prism l := 
--   Π i, (primePrismFromNat i.1)^dec.power[i]
-- def snd (dec : PrismDecomposition P) : Prism l × Prism l := 
--   let pPower := P.primePowers
--   Π i, (primePrismFromNat i.1)^(pPower[i] - dec.power[i])

end PrismDecomposition'


--------- Prism ------------------------------------------------------
namespace Prism

/-- Tries to find decomposition of `P` such that `P = P₁ * ??` 
This is of course not possible in general and any excess powers ignored.

TODO: The implementation is really bad!!! Improve it!!
-/
def decomposeBy (P P₁ : Prism l) : PrismDecomposition P :=
  let pt  := P.prodTally
  let pt₁ := P₁.prodTally
  
  let pt' := pt.map (λ (Pi, a) =>
    let find := pt₁.find (λ ((Qi, _) : Prism l × Nat) => Pi = Qi)
    match find with
    | some (Qi, b) => (Pi, b % (a+1))
    | none => (Pi, 0))

  let rec fromList {ns} (vals : List Nat) : FinProd ns :=
    match ns, vals with
    | [],  _ => Unit.unit
    | [n], [i] => ⟨i % n, sorry⟩
    | n :: m :: ns, i :: j :: is => (⟨i % n, sorry⟩, fromList (j :: is))
    | _, _ => absurd (a:=True) sorry_proof sorry_proof

  fromList (pt'.map (·.2))

end Prism

--------- Inclusion --------------------------------------------------
namespace Inclusion 

variable {l} {P Q : Prism l}

/-- Splits `Inclusiton Q P` based on the decomposition `P = P₁ * P₂` into two inclusions `Inclusion Q₁ P₁` and `Inclusion Q₂ P₂`. -/
def split (ι : Inclusion Q P) (Pdec : PrismDecomposition P) 
  : (Qdec : PrismDecomposition Q) × Inclusion Qdec.fst Pdec.fst × Inclusion Qdec.snd Pdec.snd := 
  let P₁ := Pdec.fst
  let P₂ := Pdec.snd
  match ι.1.nrepr.fromCanonical (P₁.nrepr.prod P₂.nrepr) sorry_proof with
  | .prod f g => 
    let f₁ : FaceBase l := ⟦l| f⟧
    let f₂ : FaceBase l := ⟦l| g⟧
    let Qdec : PrismDecomposition Q := Q.decomposeBy f₁.toPrism
    let ι₁ : Inclusion Qdec.fst Pdec.fst := ⟨f₁, sorry_proof, sorry_proof⟩
    let ι₂ : Inclusion Qdec.snd Pdec.snd := ⟨f₂, sorry_proof, sorry_proof⟩
    Sigma.mk Qdec (ι₁,ι₂) --, ι₂)
  | _ => absurd (a := True) sorry_proof sorry_proof /- fromCanonical (P * Q) has to be always a face of type .prod f g -/

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


-- #eval list3'
-- set_option trace.Meta.whnf true in
-- set_option maxHeartbeats 100 in
-- def t1 : FinProd list3 := fromFin ⟨3,sorry⟩
-- #eval t1

-- #eval show IO Unit from do
--   for (i,_) in Enumtype.fullRange (FinProd list3) do
--     IO.println s!"{i}"

-- example : (fromFin 2 : PrismDecomposition Prism.cube) = (fromFin 2 : PrismDecomposition Prism.cube) := by rfl

-- #eval ((fromFin ⟨2,sorry⟩) : PrismDecomposition Prism.cube)

-- #eval (fromFin 2 : PrismDecomposition Prism.cube)



-- def PrismRepr.Space' (P : PrismRepr) : Type := 
--   match P.toCanonical with
--   | .point => Unit
--   | .cone .point => ℝ
--   | .cone Q => ℝ × Q.Space'
--   | .prod Q₁ Q₂ => Q₁.Space' × Q₂.Space'
