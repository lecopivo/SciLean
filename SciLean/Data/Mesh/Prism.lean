import SciLean.Prelude
import SciLean.Mathlib.Data.Enumtype
import SciLean.Algebra
import SciLean.Data.Mesh.PrismRepr
import SciLean.Data.Quotient.GradedQuotient
import SciLean.Tactic.RemoveLambdaLet

namespace SciLean

macro "quot_lift" : conv => `(simp[Setoid.quotient_of_map])

instance : GradedSetoid Prism.Repr TwoLevel where
  r P Q := P.toCanonical = Q.toCanonical
  iseqv := sorry_proof

  OfLevel P lvl := 
    match lvl with
    | .any => True
    | .canonical => P.toCanonical = P

  lvl_order x l l' hl ho := (by cases l; simp; induction l'; simp; cases ho; cases l'; simp; apply hl;)
  every_top _ := by simp
  unique_bottom x y h hx hy := by simp at hx hy; rw [← hx, ← hy]; apply h; done

-- instance Prism.instSetoid : Setoid Prism.Repr where
--   r P Q := P.toCanonical = Q.toCanonical
--   iseqv := sorry_proof

def Prism (maxLvl := TwoLevel.any) := GradedQuotient Prism.Repr maxLvl

namespace Prism

  variable {l : TwoLevel}

  instance : Setoid.Map (λ x : Prism.Repr => x.toCanonical) := sorry_proof
  instance : Setoid.Morphism (λ x : Prism.Repr => x.toCanonical) := sorry_proof

  def nrepr (P : Prism l) : Prism.Repr := P.liftOn (λ P => 
    match P.lvl with
    | .any => P.1.toCanonical 
    | .canonical => P.1
    ) sorry_proof
    -- match P.repr.lvl with
    -- | .any       => P.repr.1.toCanonical
    -- | .canonical => P.repr.1
    -- rewrite_by simp

  instance : DecidableEq (Prism l) := λ P Q => if P.nrepr = Q.nrepr then isTrue sorry_proof else isFalse sorry_proof

  instance : Setoid.Map (λ P : Prism.Repr => P.dim) := sorry_proof
  def dim (P : Prism l) : Nat := P.repr.dim rewrite_by quot_lift

  instance (n) : Setoid.Map (λ P : Prism.Repr => P.faceCount n) := sorry_proof
  def faceCount (n : Nat) (P : Prism l) : Nat := P.repr.faceCount n rewrite_by quot_lift

  abbrev pointCount (P : Prism l) : Nat := P.faceCount 0
  abbrev edgeCount  (P : Prism l) : Nat := P.faceCount 1

  def toString (P : Prism l) : String := P.nrepr.toString
  instance : ToString (Prism l) := ⟨λ P => P.toString⟩
  partial def toDbgString (P : Prism) : String := P.liftOn (λ P => P.1.toString) sorry_proof

  instance (lvl : TwoLevel) : GradedSetoid.Reduce Prism.Repr lvl where
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

  instance : GradedSetoid.Morphism (λ P : Prism.Repr => P.cone) := sorry_proof
  def cone (P : Prism l) : Prism l := ⟦l| P.repr.cone⟧ rewrite_by quot_lift

  instance : Setoid.Morphism₂ (λ P Q : Prism.Repr => P.prod Q) := sorry_proof
  instance : Mul (Prism l) := ⟨λ P Q => ⟦l| P.repr.prod Q.repr⟧ rewrite_by quot_lift⟩

  def point : Prism .any := 1

  def segment := point.cone

  def triangle := segment.cone
  def square   := segment*segment

  def tet     := triangle.cone
  def pyramid := square.cone
  def prism   := segment*triangle
  def cube    := segment*square

  -- #eval point*triangle*segment*triangle |>.toDbgString
  #eval point*triangle*segment*triangle

end Prism


instance : GradedSetoid Face.Repr TwoLevel where
  r f g := f.toCanonical = g.toCanonical
  iseqv := sorry_proof

  OfLevel f lvl := 
    match lvl with
    | .any => True
    | .canonical => f.toCanonical = f

  lvl_order x l l' hl ho := (by cases l; simp; induction l'; simp; cases ho; cases l'; simp; apply hl;)
  every_top _ := by simp
  unique_bottom x y h hx hy := by simp at hx hy; rw [← hx, ← hy]; apply h; done

instance (lvl : TwoLevel) : GradedSetoid.Reduce Face.Repr lvl where
  reduce f := match lvl with | .any => f | .canonical => f.toCanonical
  reduce_sound := sorry_proof
  reduce_lvl   := sorry_proof

def FaceBase (lvl := TwoLevel.any) := GradedQuotient Face.Repr lvl

instance {lvl} : DecidableEq (FaceBase lvl) := λ f g => if (f.nrepr = g.nrepr) then isTrue sorry else isFalse sorry

instance : GradedSetoid.Morphism (λ f : Face.Repr => f.ofPrism) := sorry_proof
def FaceBase.ofPrism (f : FaceBase l) : Prism l := ⟦l| f.repr.ofPrism⟧ rewrite_by simp

instance : Setoid.Map (λ f : Face.Repr => f.dim) := sorry_proof
def FaceBase.dim (f : FaceBase l) : Nat := f.repr.dim rewrite_by simp[Setoid.quotient_of_map]

structure Face (P : Prism lvl) (dim : Option Nat := none) where
  f : FaceBase lvl
  hp : f.ofPrism = P
  hd : f.dim = dim.getD f.dim
deriving DecidableEq

namespace FaceBase

  variable {l}

  -- Not a GradedSetoid.Morphism!!!
  instance : Setoid.Morphism (λ f : Face.Repr => f.toPrism) := sorry_proof
  def toPrism (f : FaceBase l) : Prism l := ⟦l| f.repr.toPrism⟧ rewrite_by simp

  def comp (f g : FaceBase l) (h : f.toPrism = g.ofPrism) : FaceBase l :=
    f.liftOn₂ g (λ f g => ⟦⟨f.1.comp (g.normalize.1.fromCanonical f.1.toPrism sorry_proof) sorry_proof, f.2, sorry_proof, f.4⟩⟧) sorry_proof

  instance : GradedSetoid.Morphism (λ P : Prism.Repr => Face.Repr.tip P) := sorry_proof
  def tip (P : Prism l) : FaceBase l := ⟦l| Face.Repr.tip P.repr⟧ rewrite_by simp

  instance : GradedSetoid.Morphism (λ f : Face.Repr => f.cone) := sorry_proof
  def cone (f : FaceBase l) : FaceBase l := ⟦l| f.repr.cone⟧ rewrite_by simp

  instance : GradedSetoid.Morphism (λ f : Face.Repr => f.base) := sorry_proof
  def base (f : FaceBase l) : FaceBase l := ⟦l| f.repr.base⟧ rewrite_by simp

  instance : Setoid.Morphism₂ (λ f g: Face.Repr => f.prod g) := sorry_proof
  def prod (f g : FaceBase l) : FaceBase l := ⟦l| f.repr.prod g.repr⟧ rewrite_by simp

  instance : Mul (FaceBase l) := ⟨λ f g => f.prod g⟩

  def liftOnP (f : FaceBase l) (P : Prism l) (n : Nat) {α : Type}
         (F : (f : GradedSetoid.Repr Face.Repr l) → 
              (hp : f.1.ofPrism.toCanonical = P.nrepr) → 
              (hd : f.1.dim = n) → α)
         (hf : ∀ f f' hp hp' hd hd', f ≈ f' → F f hp hd = F f' hp' hd')
         (hp : f.ofPrism = P) (hd : f.dim = n) : α 
         :=  
         f.recOn (motive := λ (f' : FaceBase l) => (f'.ofPrism = P) → (f'.dim = n) → α)
             (λ f hp hd => F f sorry_proof sorry_proof) sorry_proof hp hd


end FaceBase

namespace Face 

  variable {l} {P : Prism l} {n : Option Nat}

  noncomputable
  abbrev grepr (f : Face P n) : GradedSetoid.Repr Face.Repr l := f.1.grepr

  noncomputable
  abbrev repr (f : Face P n) : Face.Repr := f.1.repr

  def lift (f : Face P n)
         (F : (f : GradedSetoid.Repr Face.Repr l) → 
              (hp : f.1.ofPrism.toCanonical = P.nrepr) → 
              (hd : (match n with | some n => (f.1.dim = n) | none => True)) → α) 
         (hf : ∀ f f' hp hp' hd hd', f ≈ f' → F f hp hd = F f' hp' hd')
         (f : Face P n) : α 
         :=
         f.1.liftOnP P (match n with | some n => n | none => f.1.dim) (λ f hp hd => F f hp sorry_proof) sorry_proof f.2 sorry_proof

  -- Not a GradedSetoid.Morphism!!!
  instance : Setoid.Morphism (λ f : Face.Repr => f.toPrism) := sorry_proof
  def toPrism (f : Face P n) : Prism l := ⟦l| f.repr.toPrism⟧ rewrite_by simp

  abbrev ofPrism (_ : Face P n) : Prism l := P

  def dim (f : Face P n) : Nat :=
    match n with
    | some n => n
    | none => f.1.dim

  def comp (f : Face P n) (g : Face f.toPrism m) : Face P m := 
    ⟨f.1.comp g.1 sorry_proof, sorry_proof, sorry_proof⟩

  def tip (P : Prism l) : Face (P.cone) (P.dim) := ⟨FaceBase.tip P, sorry_proof, sorry_proof⟩
  def cone (f : Face P n) : Face (P.cone) (n.map (·+1)) := ⟨f.1.cone, sorry_proof, sorry_proof⟩
  def base (f : Face P n) : Face (P.cone) n := ⟨f.1.base, sorry_proof, sorry_proof⟩
  def prod (f : Face P n) (g : Face Q m) : Face (P*Q) (match n, m with | some n, some m => n+m | _, _ => none) := ⟨f.1*g.1, sorry_proof, sorry_proof⟩

  instance {n m : Nat} : HMul (Face P n) (Face Q m) (Face (P*Q) (n+m)) := ⟨λ f g => f.prod g⟩
   
end Face

-- Inclusion of Q's `n`-faces to P
-- Can we remove `n`? The problem is that without explicit `n` the `CoeFun` is not synthesized properly
-- If the dimension a face `g` does not match the dimension of the inclusion `f`
-- 
structure Inclusion (P Q : Prism l) (n : Option Nat := none) where
  val : Face P Q.dim
  domain : Q = val.toPrism


namespace Inclusion 

  instance (P Q : Prism l) : CoeFun (Inclusion P Q n) (λ _ => Face Q n → Face P n) := ⟨λ f g => f.val.comp (f.domain ▸ g)⟩
  def cast (f : Inclusion P Q n) {m} : Inclusion P Q m := ⟨f.1,f.2⟩

  variable (P Q : Prism l) (n m) (f : Inclusion P Q n) (g : Face Q n) (h : Face Q m)

  #check f g
  #check f.cast h

  #check f.cast
  
end Inclusion

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
  
end Prism
