-- import Mathlib
-- import SciLean.Mathlib.Algebra.Module.Basic
import SciLean.Categories
import SciLean.Quot.QuotQ

namespace SciLean

structure Compression (Val : Type) (Compr : Type) where
  canCompress : Val → Bool
  uncompress : Compr → Val
  compress : Val → Compr

  eq (a : Val) (b : Compr) : Prop := (a = uncompress b)
  compressible (a : Val)   : Prop := (a = uncompress (compress a))

  unique : ∀ b, (compress (uncompress b)) = b
  valid  : ∀ a, (canCompress a = true) ↔ compressible a

namespace Compressed

  inductive Repr (Val : Type) (Compr : Type) where
  | val   (a : Val) : Repr Val Compr
  | compr (b : Compr) : Repr Val Compr

  namespace Repr

    variable {α β : Type}

    instance [ToString α] [ToString β] : ToString (Repr α β) := 
    ⟨λ x => 
      match x with
      | val   a => toString a
      | compr b => toString b⟩

    def Eq (c : Compression α β) : Repr α β → Repr α β → Prop 
      | val   x, val   y => x = y
      | compr x, compr y => x = y
      | val   x, compr y => c.eq x y
      | compr x, val   y => c.eq y x

    open Quot'

    instance (c : Compression α β) : QForm (Eq c) where
      RedForm := λ lvl x => 
        match lvl with
        | redLvl _ => True
        | normLvl => 
          match x with 
          | compr _ => True
          | val   a => ¬(c.compressible a)
      redform_norm := sorry
      redform_zero := sorry
      redform_succ := sorry
      redform_inf  := sorry
    
    instance (c : Compression α β) (n : Nat) : QReduce (Eq c) (redLvl n) where
      reduce := id
      is_reduce := sorry
      eq_reduce := sorry
      preserve_stronger := sorry

    instance (c : Compression α β) : QReduce (Eq c) (normLvl) where
      reduce := λ x =>
        match x with
        | compr x => compr x
        | val   x => if h : c.canCompress x then compr (c.compress x) else val x
      is_reduce := sorry
      eq_reduce := sorry
      preserve_stronger := sorry

    def project (x : Repr α β) (c : Compression α β) : β :=
      match x with
      | compr x => x
      | val   x => c.compress x
    
  end Repr
      
end Compressed



def Compressed (α) {β} (c : Compression α β) (autoUncompress := true) := Quot' (Compressed.Repr.Eq c)



namespace Compressed

  variable {α β} {c c' : Compression α β}

  open Quot'


  instance : Coe α (Compressed α c) := ⟨λ a => ⟦⟨.val a, rawLvl, sorry⟩⟧⟩
  instance : Coe β (Compressed α c) := ⟨λ b => ⟦⟨.compr b, normLvl, sorry⟩⟧⟩


  def uncompress (x : Compressed α c) : α :=
    (Quot.lift · sorry x) <| 
      (λ x => 
        match x.repr with
        | .val a => a
        | .compr x => c.uncompress x)

  -- compress if possible
  def maybe_compress (x : Compressed α c) : Compressed α c := 
    (Quot.lift · sorry x) <|
      (λ x => ⟦x.normalize⟧)

  @[simp]
  theorem maybe_compress_is_id (x : Compressed α c)
    : x.maybe_compress = x := sorry

  -- compress no matter what
  def compress (x : Compressed α c) : Compressed α c :=
    (Quot.lift · sorry x) <|
      (λ x => ⟦⟨.compr (x.repr.project c), normLvl, sorry⟩⟧)


  def map (x : Compressed α c) 
    (f : α → γ) (g : β → γ) 
    (h : ∀ a b, c.eq a b → f a = g b) 
    : γ :=
    (Quot.lift · sorry x) <|
    (λ x => 
      match x.repr with
      | .val x => f x
      | .compr x => g x)

  def map₂ (x y : Compressed α c) 
    (faa : α → α → γ) (fbb : β → β → γ)
    (fab : α → β → γ) (fba : β → α → γ)
    (h : (∀ xa xb ya yb,  c.eq xa xb → c.eq ya yb → (faa xa ya = fbb xb yb)) ∧
         (∀ xa xb ya, c.eq xa xb → (faa xa ya = fba xb ya)) ∧ 
         (∀ ya yb xa, c.eq ya yb → (faa xa ya = fab xa yb)))
    := x.map 
        (λ xa => y.map 
         (λ ya => faa xa ya)
         (λ yb => fab xa yb)
         sorry)
        (λ xb => y.map
         (λ ya => fba xb ya)
         (λ yb => fbb xb yb)
         sorry) 
        sorry

  -- What is goint on with this coercion? It is doing odd stuff with `Coe`.
  instance : CoeHead (Compressed α c (autoUncompress := true)) α := ⟨(λ x => x.uncompress)⟩

  section FewTests

    variable (x : Compressed α c) (x' : Compressed α c' (autoUncompress := false))

    #check (x : α)
    #check_failure (x' : α)

    variable {α β} [HMul α β β] (a : α) (b : β)
    #check a * b

  end FewTests
  

end Compressed


def ZeroCompression (α : Type) [Zero α] [DecidableEq α] : Compression α Unit where
  canCompress a := (a = 0)
  uncompress p := 0
  compress a := ()

  valid := sorry
  unique := sorry


namespace ZeroCompression

  abbrev ZCompr (α : Type) [Zero α] [DecidableEq α] := Compressed α (ZeroCompression α)

  variable {α : Type} [DecidableEq α]

  instance [Zero α] : Zero (ZCompr α) := ⟨()⟩
  instance [One α] [Zero α] : One (ZCompr α) := ⟨(1:α)⟩

  instance {R : Type} [Monoid R] [AddMonoid α] [DistribMulAction R α]  : HMul R (ZCompr α) (ZCompr α) := 
    ⟨λ r x => x.map (λ a : α => (HMul.hMul r a : α)) (λ p => ()) 
     (by 
      simp[Compressed.Repr.Eq, ZeroCompression]
      apply Quot.sound; simp
      apply (DistribMulAction.smul_zero)
     )⟩

  instance {α : Type} [DecidableEq α] [AddMonoid α] : Add (ZCompr α) := 
    ⟨λ x y : ZCompr α => 
      (x.map₂ y
        (λ x y => (x + y : α))
        (λ _ _ => ())
        (λ x _ => x)
        (λ _ x => x)
        (by 
      simp[Compressed.Repr.Eq, ZeroCompression]
      constructor
      . intros _ _ h h'; apply Quot.sound; simp[h,h']
      constructor
      . intros _ _ h; apply Quot.sound; simp[h]
      . intros _ _ h; apply Quot.sound; simp[h]
     ))⟩

  instance [SubNegMonoid α] : Sub (ZCompr α) := 
    ⟨λ x y : ZCompr α => 
      (x.map₂ y
        (λ x y => (x - y : α))
        (λ _ _ => ())
        (λ x _ => x)
        (λ _ x => (-x : α))
        (by 
      simp[Compressed.Repr.Eq, ZeroCompression]
      constructor
      . intros _ _ h h'; apply Quot.sound; simp[h,h']; admit
      constructor
      . intros _ _ h; apply Quot.sound; simp[h]; admit
      . intros _ _ h; apply Quot.sound; simp[h]; admit
     ))⟩

  instance [MulZeroClass α] : Mul (ZCompr α) := 
    ⟨λ x y : ZCompr α => 
      (x.map₂ y
        (λ x y => (x * y : α))
        (λ _ _ => ())
        (λ x _ => ())
        (λ _ x => ())
        (by 
      simp[Compressed.Repr.Eq, ZeroCompression]
      constructor
      . intros _ _ h h'; apply Quot.sound; simp[h,h']; admit
      constructor
      . intros _ _ h; apply Quot.sound; simp[h]; admit
      . intros _ _ h; apply Quot.sound; simp[h]; admit
     ))⟩

  instance [SubNegMonoid α] : Neg (ZCompr α) := ⟨λ x => x.map (λ a => (-a : α)) (λ p => ()) 
    (by 
      simp[Compressed.Repr.Eq, ZeroCompression]
      apply Quot.sound; simp
      admit -- -0=0 this should be provable from `SubNegMonoid`
     )⟩

  instance [AddCommGroup α] : AddCommGroup (ZCompr α) where
    add_comm := sorry
    add_assoc := sorry
    add_zero := sorry
    zero_add := sorry
    add_left_neg := sorry
    nsmul_zero' := sorry
    nsmul_succ' n x := sorry
    sub_eq_add_neg a b := sorry
    gsmul_zero' := sorry
    gsmul_succ' n x := sorry
    gsmul_neg' n x := sorry

  instance [Ring α] : Ring (ZCompr α) where
    zero_mul := sorry
    mul_zero := sorry
    -- mul_comm := sorry
    left_distrib := sorry
    right_distrib := sorry
    mul_one := sorry
    one_mul := sorry
    -- npow n x := x^(n.toReal) ----------- !!!
    npow_zero' n := sorry
    npow_succ' n x := sorry
    mul_assoc := sorry
    add_comm := sorry
    add_assoc := sorry
    add_zero := sorry
    zero_add := sorry
    add_left_neg := sorry
    -- nsmul n x := (n.toReal) * x ----------------  !!!
    nsmul_zero' := sorry
    nsmul_succ' n x := sorry
    sub_eq_add_neg a b := sorry
    -- gsmul n x := (n.toReal) * x --------- !!!
    gsmul_zero' := sorry
    gsmul_succ' n x := sorry
    gsmul_neg' n x := sorry
    natCast n := (n : α)
    natCast_zero := sorry
    natCast_succ := sorry
    intCast n := (AddGroupWithOne.intCast n : α)
    intCast_ofNat := sorry
    intCast_negSucc := sorry

  instance [CommRing α] : CommRing (ZCompr α) where
    mul_comm := sorry

  instance [Semiring R] [AddCommGroup α] [Module R α] : Module R (ZCompr α) where
    one_smul := sorry
    mul_smul := sorry
    smul_add := sorry
    smul_zero := sorry
    add_smul := sorry
    zero_smul := sorry

  instance [Vec α] : Vec (ZCompr α) := Vec.mk

end ZeroCompression

namespace HOHO

  open ZeroCompression

  def a : ZCompr Int := (42 : Int)
  def b : ZCompr Int := ()
  def c := a * b
  def d := a + b + a 
  #eval a.toDebugString
  #eval b.toDebugString
  #eval c.toDebugString
  #eval d.toDebugString

end HOHO
