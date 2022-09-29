import SciLean.Prelude
import SciLean.Mathlib.Data.Enumtype
import SciLean.Algebra
import SciLean.Data.Mesh.PrismRepr
import SciLean.Data.Quotient.GradedQuotient
import SciLean.Tactic.RemoveLambdaLet

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

def PrismBase (maxLvl := TwoLevel.any) := GradedQuotient PrismRepr maxLvl

instance : Setoid.Map (λ P : PrismRepr => P.dim) := sorry_proof
def PrismBase.dim (P : PrismBase l) : Nat := P.repr.dim rewrite_by quot_lift

structure Prism (n : Option Nat := none) (maxLvl := TwoLevel.any) where
  val : PrismBase maxLvl
  dim_property : match n with | some n => val.dim = n | none => True
                       
namespace Prism

  variable {n : Option Nat} {l : TwoLevel}

  instance (lvl : TwoLevel) : GradedSetoid.Reduce PrismRepr lvl where
    reduce P := match lvl with | .any => P | .canonical => P.toCanonical
    reduce_sound := sorry_proof
    reduce_lvl   := sorry_proof

  instance : Setoid.Map (λ x : PrismRepr => x.toCanonical) := sorry_proof
  instance : Setoid.Morphism (λ x : PrismRepr => x.toCanonical) := sorry_proof

  noncomputable
  def repr (P : Prism n l) : PrismRepr := P.1.repr

  @[simp high]
  theorem repr_quotient (P : Prism n l) 
    : ⟦l| P.repr⟧ = P.1
    := sorry_proof

  @[simp] 
  theorem repr_ungraded (P : Prism n l) :  ⟦P.repr⟧ = P.1.ungraded := sorry_proof

  noncomputable
  def grepr (P : Prism n l) : GradedSetoid.Repr PrismRepr l := Quotient.repr P.1

  @[simp high]
  theorem grepr_quotient (P : Prism n l)
    : ⟦P.grepr⟧ = P.1
    := sorry_proof

  def nrepr (P : Prism n l) : PrismRepr := P.1.liftOn (λ P => 
    match P.lvl with
    | .any => P.1.toCanonical 
    | .canonical => P.1
    ) sorry_proof
    -- match P.repr.lvl with
    -- | .any       => P.repr.1.toCanonical
    -- | .canonical => P.repr.1
    -- rewrite_by simp

  instance : DecidableEq (Prism n l) := λ P Q => if P.nrepr = Q.nrepr then isTrue sorry_proof else isFalse sorry_proof

  instance : Setoid.Map (λ P : PrismRepr => P.dim) := sorry_proof
  def dim (P : Prism n l) : Nat := 
    match n with
    | some n' => n'
    | none => P.repr.dim rewrite_by quot_lift

  instance (n) : Setoid.Map (λ P : PrismRepr => P.faceCount n) := sorry_proof
  def faceCount (d : Nat) (P : Prism n l) : Nat := P.repr.faceCount d rewrite_by quot_lift

  abbrev pointCount (P : Prism n l) : Nat := P.faceCount 0
  abbrev edgeCount  (P : Prism n l) : Nat := P.faceCount 1

  def toString (P : Prism n l) : String := P.nrepr.toString
  instance : ToString (Prism n l) := ⟨λ P => P.toString⟩
  partial def toDbgString (P : Prism n l) : String := P.1.liftOn (λ P => P.1.toString) sorry_proof


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

  instance {n : Nat} : OfNat (Option Nat) n := ⟨some n⟩
  instance : Add (Option Nat) := ⟨λ n m => match n, m with | some n', some m' => n' + m' | _, _ => none⟩

  instance : One (Prism none l) := ⟨⟨⟦l| .point⟧, sorry_proof⟩⟩
  instance : One (Prism 0 l) := ⟨⟨⟦l| .point⟧, sorry_proof⟩⟩

  instance : GradedSetoid.Morphism (λ P : PrismRepr => P.cone) := sorry_proof
  def cone (P : Prism n l) : Prism (n + 1) l := ⟨⟦l| P.repr.cone⟧, sorry_proof⟩ rewrite_by quot_lift

  instance : Setoid.Morphism₂ (λ P Q : PrismRepr => P.prod Q) := sorry_proof
  instance : HMul (Prism n l) (Prism m l) (Prism (n+m) l) := ⟨λ P Q => ⟨⟦l| P.repr.prod Q.repr⟧, sorry_proof⟩ rewrite_by quot_lift⟩

  def point : Prism 0 .any := 1

  def segment := reduce_type_of point.cone

  def triangle := reduce_type_of segment.cone
  def square   := reduce_type_of segment*segment

  def tet     := reduce_type_of triangle.cone
  def pyramid := reduce_type_of square.cone
  def prism   := reduce_type_of segment*triangle
  def cube    := reduce_type_of segment*square

  #eval point*triangle*segment*triangle |>.toDbgString
  #eval point*triangle*segment*triangle

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
def FaceBase.ofPrism (f : FaceBase l) : PrismBase l := ⟦l| f.repr.ofPrism⟧ rewrite_by simp

instance : Setoid.Map (λ f : FaceRepr => f.dim) := sorry_proof
def FaceBase.dim (f : FaceBase l) : Nat := f.repr.dim rewrite_by simp[Setoid.quotient_of_map]

structure Face (P : Prism n lvl) (m : Option Nat := none) where
  f : FaceBase lvl
  hp : f.ofPrism = P.1
  hd : f.dim = m.getD f.dim
deriving DecidableEq

namespace FaceBase

  variable {n l}

  -- Not a GradedSetoid.Morphism!!!
  instance : Setoid.Morphism (λ f : FaceRepr => f.toPrism) := sorry_proof
  def toPrism (f : FaceBase l) : PrismBase l := ⟦l| f.repr.toPrism⟧ rewrite_by simp

  def comp (f g : FaceBase l) (h : f.toPrism = g.ofPrism) : FaceBase l :=
    f.liftOn₂ g (λ f g => ⟦⟨f.1.comp (g.normalize.1.fromCanonical f.1.toPrism sorry_proof) sorry_proof, f.2, sorry_proof, f.4⟩⟧) sorry_proof

  instance : GradedSetoid.Morphism (λ P : PrismRepr => FaceRepr.tip P) := sorry_proof
  def tip (P : PrismBase l) : FaceBase l := ⟦l| FaceRepr.tip P.repr⟧ rewrite_by simp

  instance : GradedSetoid.Morphism (λ f : FaceRepr => f.cone) := sorry_proof
  def cone (f : FaceBase l) : FaceBase l := ⟦l| f.repr.cone⟧ rewrite_by simp

  instance : GradedSetoid.Morphism (λ f : FaceRepr => f.base) := sorry_proof
  def base (f : FaceBase l) : FaceBase l := ⟦l| f.repr.base⟧ rewrite_by simp

  instance : Setoid.Morphism₂ (λ f g: FaceRepr => f.prod g) := sorry_proof
  def prod (f g : FaceBase l) : FaceBase l := ⟦l| f.repr.prod g.repr⟧ rewrite_by simp

  instance : Mul (FaceBase l) := ⟨λ f g => f.prod g⟩

  def liftOnP (f : FaceBase l) (P : PrismBase l) (n : Nat) {α : Type}
         (F : (f : GradedSetoid.Repr FaceRepr l) → 
              (hp : f.1.ofPrism.toCanonical = P.nrepr) → 
              (hd : f.1.dim = n) → α)
         (hf : ∀ f f' hp hp' hd hd', f ≈ f' → F f hp hd = F f' hp' hd')
         (hp : f.ofPrism = P) (hd : f.dim = n) : α 
         :=  
         f.recOn (motive := λ (f' : FaceBase l) => (f'.ofPrism = P) → (f'.dim = n) → α)
             (λ f hp hd => F f sorry_proof sorry_proof) sorry_proof hp hd


end FaceBase

namespace Face 

  variable {n m : Option Nat} {l} {P : Prism n l} 

  noncomputable
  abbrev grepr (f : Face P m) : GradedSetoid.Repr FaceRepr l := f.1.grepr

  noncomputable
  abbrev repr (f : Face P m) : FaceRepr := f.1.repr

  def lift (f : Face P m)
         (F : (f : GradedSetoid.Repr FaceRepr l) → 
              (hp : f.1.ofPrism.toCanonical = P.nrepr) → 
              (hd : (match m with | some m => (f.1.dim = m) | none => True)) → α) 
         (hf : ∀ f f' hp hp' hd hd', f ≈ f' → F f hp hd = F f' hp' hd')
         (f : Face P m) : α 
         :=
         f.1.liftOnP P.1 (match m with | some m => m | none => f.1.dim) (λ f hp hd => F f sorry_proof sorry_proof) sorry_proof f.2 sorry_proof

  -- Not a GradedSetoid.Morphism!!!
  instance : Setoid.Morphism (λ f : FaceRepr => f.toPrism) := sorry_proof
  def toPrism (f : Face P m) : Prism m l := ⟨⟦l| f.repr.toPrism⟧ rewrite_by simp, sorry_proof⟩

  abbrev ofPrism (_ : Face P m) : Prism n l := P

  def dim (f : Face P m) : Nat :=
    match m with
    | some m => m
    | none => f.1.dim

  def comp (f : Face P m) (g : Face f.toPrism m') : Face P m' := 
    ⟨f.1.comp g.1 sorry_proof, sorry_proof, sorry_proof⟩

  def tip (P : Prism n l) : Face (P.cone) (P.dim) := ⟨FaceBase.tip P.1, sorry_proof, sorry_proof⟩
  def cone (f : Face P m) : Face (P.cone) (n.map (·+1)) := ⟨f.1.cone, sorry_proof, sorry_proof⟩
  def base (f : Face P m) : Face (P.cone) n := ⟨f.1.base, sorry_proof, sorry_proof⟩
  def prod {Q : Prism n' l} (f : Face P m) (g : Face Q m') : Face (P*Q) (m+m') := ⟨f.1*g.1, sorry_proof, sorry_proof⟩

  instance {Q : Prism n' l} {m m'}  : HMul (Face P m) (Face Q m') (Face (P*Q) (m+m')) := ⟨λ f g => f.prod g⟩
   
end Face

-- Inclusion of P's `m`-faces to Q
-- Can we remove `m`? The problem is that without explicit `m` the `CoeFun` is not synthesized properly
-- If the dimension a face `g` does not match the dimension of the inclusion `f`
-- 
structure Inclusion (P : Prism n l) (Q : Prism n' l) (m : Option Nat := none) where
  val : Face Q n
  domain : P = val.toPrism


namespace Inclusion 

  variable {P : Prism n l} {Q : Prism n' l}

  instance : CoeFun (Inclusion P Q m) (λ _ => Face P m → Face Q m) := ⟨λ f g => f.val.comp (f.domain ▸ g)⟩
  def cast (f : Inclusion P Q m) {m'} : Inclusion P Q m' := ⟨f.1,f.2⟩

  variable (f : Inclusion P Q n) (g : Face P n) (h : Face P m)

  #check f g
  #check f.cast h

  #check f.cast
  
end Inclusion

namespace Prism

  variable {l : TwoLevel}

  def first (P : Prism n l) (m : Option Nat := none) : Option (Face P m) := 
    P.1.liftOn (λ P' => 
    match m with
    | none => match P'.1.first 0 with
      | some f => some ⟨⟦⟨f, l, sorry_proof, sorry_proof⟩⟧, sorry_proof, sorry_proof⟩
      | none => none
    | some m =>
    match P'.1.first m with
    | some f => some ⟨⟦⟨f, l, sorry_proof, sorry_proof⟩⟧, sorry_proof, sorry_proof⟩
    | none => none) sorry_proof

end Prism


namespace Face

  variable {l : TwoLevel}

  def next {P : Prism n l} {m} (f : Face P m) : Option (Face P m) :=
    f.1.liftOn (λ f' => 
      match f'.1.next with
      | some f => some ⟨⟦⟨f, l, sorry_proof, sorry_proof⟩⟧, sorry_proof, sorry_proof⟩
      | none => 
        match m with
        | some _ => none
        | none => 
          match f'.1.ofPrism.first (f'.1.dim+1) with
          | some f => some ⟨⟦⟨f, l, sorry_proof, sorry_proof⟩⟧, sorry_proof, sorry_proof⟩
          | none => none
      ) sorry_proof

  instance : ToString (Face P m) := ⟨λ P => P.1.liftOn (λ P => P.normalize.1.toString) sorry_proof⟩

  instance (P : Prism n l) (m)
    : Iterable (Face P m) :=
  {
    first := P.first m
    next := λ f => f.next
    decEq := by infer_instance
  }

  def faces {P : Prism n l} {m} (f : Face P m) (m' : Option Nat := none)  := Iterable.fullRange (Face f.toPrism m')
  
end Face


namespace Prism

  def faces (P : Prism n l) (m : Option Nat := none) := Iterable.fullRange (Face P m)

  def test (P : Prism l) : IO Unit := do
    for f in P.faces do
      IO.println s!"dim: {f.dim} | {f}"
      IO.print "       "
      for g in f.faces do
        IO.print s!"| {g} | {f.comp g} "
      IO.println ""
    pure ()

  #eval test (triangle)
  -- #eval triangle*segment = prism

end Prism
