import Mathlib
import SciLean.Mathlib.Algebra.Module.Basic

class Symbolic {Repr : Type} (R : Repr → Repr → Prop) where
  RedForm  : Repr → Prop 
  NormForm : Repr → Prop
  norm_red : ∀ x, NormForm x → RedForm x
  R_norm  : ∀ x y, R x y → NormForm x → NormForm y → x = y

namespace Symbolic


  -- define Hom     -- preserves relation
  -- define RedHom  -- preserving RefForm
  -- define NormHom -- preserving RefForm
  -- define their Hom₂ variants
  section Hom 
    variable {Repr Repr'}
      (R  : Repr  → Repr  → Prop) [Symbolic R]
      (R' : Repr' → Repr' → Prop) [Symbolic R']
      (f : Repr → Repr')

    structure Hom : Prop where
      is_hom : ∀ x y : Repr, R x y → R' (f x) (f y)

    structure RedHom : Prop where
      is_hom : ∀ x y : Repr, R x y → R' (f x) (f y)
      preserve_red  : ∀ x : Repr, RedForm R x → RedForm R' (f x)

    structure NormHom : Prop where
      is_hom : ∀ x y : Repr, R x y → R' (f x) (f y)
      preserve_red  : ∀ x : Repr, RedForm R x → RedForm R' (f x)
      preserve_norm : ∀ x : Repr, NormForm R x → NormForm R' (f x)

  end Hom


  structure SHom {Repr Repr'}
    (R  : Repr  → Repr  → Prop) [Symbolic R]
    (R' : Repr' → Repr' → Prop) [Symbolic R']
    (f : Repr → Repr') : Prop where
       is_hom : ∀ x y : Repr, R x y → R' (f x) (f y)
       preserve_red  : ∀ x : Repr, RedForm R x → RedForm R' (f x)
       preserve_norm : ∀ x : Repr, NormForm R x → NormForm R' (f x)

  structure SHom₂ {Repr Repr' Repr''}
    (R : Repr → Repr → Prop) [Symbolic R]
    (R' : Repr' → Repr' → Prop) [Symbolic R']
    (R'' : Repr'' → Repr'' → Prop) [Symbolic R'']
    (f : Repr → Repr' → Repr'') : Prop where 
      is_hom₂ : ∀ (x y : Repr) (x' y' : Repr'), R x y → R' x' y' → R'' (f x x') (f y y')
      preserve_red  : ∀ x x', RedForm R x → RedForm R' x' → RedForm R'' (f x x')
      preserve_norm : ∀ x x', NormForm R x → NormForm R' x' → NormForm R'' (f x x')

  class SReduce {Repr} (R : Repr → Repr → Prop) [Symbolic R] where
    reduce : Repr → Repr
    is_reduce : ∀ x, RedForm R (reduce x)
    R_reduce : ∀ x, R x (reduce x)
    reduce_of_norm : ∀ x, NormForm R x → NormForm R (reduce x) -- does not destroy norm form

  -- symbolic reduction on quotient will be identity
  class Reduce (X : Type u) where 
    reduce : X → X
    id_reduce : ∀ x : X, reduce x = x

  class SNormalize {Repr} (R : Repr → Repr → Prop) [Symbolic R] where
    normalize : Repr → Repr
    is_normalize : ∀ x, NormForm R (normalize x)
    R_normalize : ∀ x, R x (normalize x)

  -- symbolic normalization on quotient will be identity
  class Normalize (X : Type u) where 
    normalize : X → X
    id_normalize : ∀ x : X, normalize x = x

  -- This just tags `Repr` in which form they are
  inductive SRepr {Repr : Type} (R : Repr → Repr → Prop) [Symbolic R] where
    | raw  (x : Repr) : SRepr R
    | red  (x : Repr) (h : RedForm R x)  : SRepr R
    | norm (x : Repr) (h : NormForm R x) : SRepr R

  namespace SRepr 

    variable {Repr} {R : Repr → Repr → Prop} [Symbolic R]

    def repr (x : SRepr R) : Repr :=
      match x with
      | raw  x   => x
      | red  x _ => x
      | norm x _ => x

    -- instance : Coe (SRepr R) Repr := ⟨λ x => x.repr⟩

    @[simp]
    theorem raw_repr (x : Repr) : (raw x : SRepr R).repr = x := by simp[repr] done

    @[simp]
    theorem red_repr (x : Repr) (h : RedForm R x) : (red x h : SRepr R).repr = x := by simp[repr] done

    @[simp]
    theorem norm_repr (x : Repr) (h : NormForm R x) : (norm x h : SRepr R).repr = x := by simp[repr] done

    def isReduced (x : SRepr R) : Bool :=
      match x with
      | raw x => false
      | _ => true

    def isNormalized (x : SRepr R) : Bool :=
      match x with
      | norm x _ => true
      | _ => false

    variable {Repr' } {R'  : Repr'  → Repr'  → Prop} [Symbolic R']
    variable {Repr''} {R'' : Repr'' → Repr'' → Prop} [Symbolic R'']

    def lift (f : Repr → Repr') (x : SRepr R) : SRepr R' := raw (f x.repr)

    def lift₂ (f : Repr → Repr' → Repr'') (x : SRepr R) (x' : SRepr R') : SRepr R'' :=
      raw (f x.repr x'.repr)

    def liftHom (f : Repr → Repr') (h : SHom R R' f) (x : SRepr R) : SRepr R' := 
      match x with
      | raw x => raw (f x)
      | red  x h' => red  (f x) (h.preserve_red x h')
      | norm x h' => norm (f x) (h.preserve_norm x h')

    @[simp] 
    theorem lift_hom_repr (f : Repr → Repr') (h : SHom R R' f) (x : SRepr R)
      : (liftHom f h x).repr = f x.repr
      := 
      by induction x 
         repeat simp[liftHom]
         done

    def liftHom₂ (f : Repr → Repr' → Repr'') (h : SHom₂ R R' R'' f) 
      (x : SRepr R) (y : SRepr R') : SRepr R'' :=
      match x, y with
      | red x hx,  red y hy  => red  (f x y) (h.preserve_red  x y hx hy)
      | norm x hx, norm y hy => norm (f x y) (h.preserve_norm x y hx hy)
      | x, y => raw (f x.repr y.repr)

    def reduce (x : SRepr R) [SReduce R] : SRepr R :=
      match x with
      | raw x => red (SReduce.reduce R x) (SReduce.is_reduce x)
      | x => x

    def normalize (x : SRepr R) [SNormalize R] : SRepr R :=
      match x with
      | raw x   => norm (SNormalize.normalize R x) (SNormalize.is_normalize x)
      | red x _ => norm (SNormalize.normalize R x) (SNormalize.is_normalize x)
      | x => x

  end SRepr

  def SQuot {Repr} (R : Repr → Repr → Prop) [Symbolic R]
    := Quot (λ x y : SRepr R => R x.repr y.repr)

  variable {Repr} {R : Repr → Repr → Prop} [Symbolic R]
  variable {Repr'} {R' : Repr' → Repr' → Prop} [Symbolic R']
  variable {Repr''} {R'' : Repr'' → Repr'' → Prop} [Symbolic R'']

  -- Not sure about these two with the coercion from SRepr to Repr
  def SQuot.mk  (x : SRepr R) : SQuot R := Quot.mk _ x
  def SQuot.rmk (x : Repr)    : SQuot R := Quot.mk _ (SRepr.raw x)

  def SQuot.mkRed  (x : Repr) (h : RedForm R x)  : SQuot R := Quot.mk _ (SRepr.red  x h)
  def SQuot.mkNorm (x : Repr) (h : NormForm R x) : SQuot R := Quot.mk _ (SRepr.norm x h)

  def SQuot.lift {α : Sort u} (f : Repr → α) (h : ∀ x x' : Repr, R x x' → f x = f x')
    : SQuot R → α
    := Quot.lift (λ x => f x.repr) 
         (by intros a b
             induction a
             repeat(
               induction b
               repeat(
                 simp[SRepr.repr]
                 apply h)))

  def SQuot.slift {α : Sort u} (f : SRepr R → α) (h : ∀ x x' : SRepr R, R x.repr x'.repr → f x = f x')
    : SQuot R → α
    := Quot.lift (λ x => f x) h

  def SQuot.liftHom (f : Repr → Repr') (h : SHom R R' f) 
    : SQuot R → SQuot R'
    := Quot.lift (λ x' => Quot.mk _ (SRepr.liftHom f h x')) 
        (by intro a b req
            apply Quot.sound
            induction a
            repeat 
              (induction b
               repeat 
                 (simp at req
                  apply h.is_hom
                  assumption))
            done)

  def SQuot.lift₂ (f : Repr → Repr' → Repr'')
      (h : ∀ (x y : Repr) (x' y' : Repr'), R x y → R' x' y' → R'' (f x x') (f y y'))
      : SQuot R → SQuot R' → SQuot R''
      := Quot.lift (λ x' => Quot.lift (λ y' => Quot.mk _ (SRepr.lift₂ f x' y')) sorry) sorry

  def SQuot.slift₂ (f : SRepr R → SRepr R' → SRepr R'')
      (h : ∀ (x y : SRepr R) (x' y' : SRepr R'), R x.repr y.repr → R' x'.repr y'.repr → R'' (f x x').repr (f y y').repr)
      : SQuot R → SQuot R' → SQuot R''
      := Quot.lift (λ x' => Quot.lift (λ y' => Quot.mk _ (f x' y')) sorry) sorry

  def SQuot.liftHom₂ (f : Repr → Repr' → Repr'') (h : SHom₂ R R' R'' f) 
    : SQuot R → SQuot R' → SQuot R''
    := Quot.lift (λ x' => Quot.lift (λ y' => Quot.mk _ (SRepr.liftHom₂ f h x' y')) sorry) sorry

  instance [SReduce R] : Reduce (SQuot R) :=
  {
    reduce := SQuot.slift (λ x => Quot.mk _ x.reduce) sorry
    id_reduce := sorry
  }

  instance [SNormalize R] : Normalize (SQuot R) :=
  {
    normalize := SQuot.slift (λ x => Quot.mk _ x.normalize) sorry
    id_normalize := sorry
  }

  

  -- variable {Repr : Type} {RedForm : Repr → Prop} {NormForm : Repr → Prop}

  -- instance : Coe (Symbolic Repr RedForm NormForm) Repr := ⟨repr⟩

  -- def isReduced (x : Symbolic Repr RedForm NormForm) : Bool :=
  --   match x with
  --   | raw _ => false
  --   | _ => true

  -- def isNormalized (x : Symbolic Repr RedForm NormForm) : Bool :=
  --   match x with
  --   | norm _ _ => true
  --   | _ => false

  -- -- Lift reduction preserving function `Repr → Repr'` to Symbolic
  -- def liftHom {Repr' : Type} {RedForm' NormForm' : Repr' → Prop}
  --   (f : Repr → Repr') 
  --   (h  : ∀ x : Repr, RedForm x → RedForm' (f x))
  --   (h' : ∀ x : Repr, NormForm x → NormForm' (f x))
  --   (x : Symbolic Repr RedForm NormForm) 
  --   : Symbolic Repr' RedForm' NormForm'
  --   :=
  --   match x with 
  --   | raw  x => raw (f x)
  --   | red  x g => red  (f x) (h  x g)
  --   | norm x g => norm (f x) (h' x g)


  -- def Symb {Repr} (R : Repr → Repr → Prop) (RedForm NormForm : Repr → Prop)
  --   (h : ∀ x y : Repr, R x y → NormForm x → NormForm y → x = y)
  --   := Quot (λ x y : Symbolic Repr RedForm NormForm => R x y)

  -- variable {R : outParam $ Repr → Repr → Prop} 
  --   {RedForm NormForm : outParam $ Repr → Prop}
  --   {H : outParam $ ∀ x y : Repr, R x y → NormForm x → NormForm y → x = y}

  -- def Symb.lift {α : Sort u} (f : Repr → α) (h : ∀ x y : Repr, R x y → f x = f y) 
  --   (x : Symb R RedForm NormForm H) : α
  --   := Quot.lift (λ x => f x) (by intro a b; induction a; induction b;
  --                                 repeat (simp; apply h)
  --                                 done) x

  -- def Symb.liftSnd
  --   {α : Sort u} {β : Sort v} (f : β → Repr → α) (h : ∀ b (x y : Repr), R x y → f b x = f b y) (b : β)
  --   : Symb R RedForm NormForm H → α
  --   := Quot.lift (λ x => f b x) (by intro x y; induction x; induction y;
  --                                   repeat (simp; apply (h b))
  --                                   done)

  -- def Symb.lift₂ {α : Sort u} (f : Repr → Repr → α) 
  --     (h  : ∀ x y y' : Repr, R y y' → f x y = f x y')
  --     (h' : ∀ (x x' : Repr), R x x' → liftSnd (RedForm := RedForm) (NormForm := NormForm) (H := H) f h x = liftSnd f h x')
  --     (x y : Symb R RedForm NormForm H) : α
  --     := lift (liftSnd f h) h' x y

  -- constant toString [ToString Repr] (x : Symb R RedForm NormForm H) : String
  --     := Symb.lift (λ r => toString r) sorry (x)
    
  -- -- `reduce` function should send representative to its reduced form
  -- class Reduce (X : Type) where
  --   reduce : X → X
  --   reduce_id : ∀ x, reduce x = x

  -- def lift_reduce (reduce : Repr → Repr) 
  --   (h  : ∀ x, RedForm (reduce x)) (h' : ∀ x, NormForm x → RedForm x)
  --   (x : Symbolic Repr RedForm NormForm) : (Symbolic Repr RedForm NormForm)
  --   := 
  --   match x with
  --   | raw x => red (reduce x) (h x)
  --   | x => x

  -- -- `normalize` function should send representative to its normal form
  -- class Normalize (X : Type) where
  --   normalize : X → X
  --   normalize_id : ∀ x, normalize x = x

  -- def lift_normalize (normalize : Repr → Repr) 
  --   (h  : ∀ x, NormForm (normalize x))
  --   (x : Symbolic Repr RedForm NormForm) : (Symbolic Repr RedForm NormForm)
  --   := 
  --   match x with
  --   | raw x   => norm (normalize x) (h x)
  --   | red x _ => norm (normalize x) (h x)
  --   | x => x

end Symbolic

inductive List.Sorted {X : Type u} [LE X] : List X → Prop where
| empty : Sorted []
| singl (x : X) : Sorted [x]
| head  (x y : X) (ys : List X) (h : x ≤ y) (h' : Sorted (y :: ys)) 
        : Sorted (x :: y :: ys)

inductive List.StrictlySorted {X : Type u} [LT X] : List X → Prop where
| empty : StrictlySorted []
| singl (x : X) : StrictlySorted [x]
| head  (x y : X) (ys : List X) (h : x < y) 
        (h' : StrictlySorted (y :: ys)) 
        : StrictlySorted (x :: y :: ys)

structure FreeMonoid (X : Type u) where
  vars : List X

namespace FreeMonoid

  instance {X} : Mul (FreeMonoid X) := ⟨λ x y => ⟨x.1.append y.1⟩⟩
  instance {X} : One (FreeMonoid X) := ⟨⟨[]⟩⟩

  def rank {X} (x : FreeMonoid X) : Nat := x.1.length

  inductive SymmMonoidEq {X} : FreeMonoid X → FreeMonoid X → Prop where
    | mul_comm (x y : FreeMonoid X) : SymmMonoidEq (x*y) (y*x)

end FreeMonoid


namespace Monomial 

  structure Repr (X : Type u) (K : Type v) where
    coef : K
    base : FreeMonoid X

  instance {X K} [Mul K] : Mul (Repr X K) := 
    ⟨λ x y => ⟨x.coef * y.coef, x.base * y.base⟩⟩
  instance {X K} [Mul K] : HMul K (Repr X K) (Repr X K) := 
    ⟨λ a x => ⟨a * x.coef, x.base⟩⟩

  def Repr.rank {X K} (x : Repr X K) : Nat := x.base.rank

  inductive SymMonomialEq {X K : Type} [One K] [Neg K] [Mul K] [HPow K Nat K] : Repr X K → Repr X K → Prop where
    | refl (x : Repr X K) : SymMonomialEq x x
    | mul_comm (x y : Repr X K) : SymMonomialEq (x * y) (y * x)

  inductive AltMonomialEq {X K : Type} [One K] [Neg K] [Mul K] [HPow K Nat K] : Repr X K → Repr X K → Prop where
    | refl (x : Repr X K) : AltMonomialEq x x
    | mul_alt (x y : Repr X K) : AltMonomialEq (x * y) ((-1 : K)^(x.rank + y.rank) * y * x)

  instance {X K} [LT X] [CommRing K] : Symbolic (SymMonomialEq (X := X) (K := K)) :=
  {
    RedForm  := λ x => x.base.1.StrictlySorted
    NormForm := λ x => (x.base.1.StrictlySorted) ∧ (x.coef = 0 → x.base.1 = [])
    norm_red := λ x h => h.left
    R_norm   := sorry -- this is probably hard as I need CommRing for it
  }

  instance {X K} [LT X] [CommRing K] : Symbolic (AltMonomialEq (X := X) (K := K)) :=
  {
    RedForm  := λ x => x.base.1.StrictlySorted
    NormForm := λ x => (x.base.1.StrictlySorted) ∧ (x.coef = 0 → x.base.1 = [])
    norm_red := λ x h => h.left
    R_norm   := sorry -- this is probably hard as I need CommRing for it
  }

end Monomial 


open Symbolic Monomial in
def SymMonomial (X K) [LT X] [CommRing K] := SQuot (SymMonomialEq (X := X) (K := K))

open Symbolic Monomial in
def AltMonomial (X K) [LT X] [CommRing K] := SQuot (AltMonomialEq (X := X) (K := K))

inductive DecComparison {X : Type u} [LT X] (x y : X) where
  | cpEq (h : x = y) : DecComparison x y
  | cpLt (h : x < y) : DecComparison x y
  | cpGt (h : x > y) : DecComparison x y

export DecComparison (cpEq cpLt cpGt)

class DecCompar (X : Type u) [LT X] where
  compare (x y : X) : DecComparison x y

abbrev compare {X} [LT X] [DecCompar X] (x y : X) : DecComparison x y := DecCompar.compare x y

namespace AltMonomial
  open Symbolic

  variable {X K} [LT X] [DecCompar X] [CommRing K]

  instance [DecCompar X] : Reduce (AltMonomial X K) :=
  {
    reduce := sorry  
    id_reduce := sorry
  }

  instance [DecCompar X] [DecidableEq K] : Normalize (AltMonomial X K) :=
  {
    normalize := sorry  
    id_normalize := sorry
  }

  -- TODO: change these definitions 
  --       add reduction
  instance : Mul  (AltMonomial X K) := ⟨λ x' y' => (SQuot.lift₂ (λ x y => (x * y)) sorry) x' y' |> Reduce.reduce⟩
  instance [Mul K] : HMul K (AltMonomial X K) (AltMonomial X K) := ⟨λ c => SQuot.lift (λ x => SQuot.rmk (c * x)) sorry⟩
  instance : One  (AltMonomial X K) := ⟨SQuot.mkNorm ⟨1,1⟩ sorry⟩
  instance : Zero (AltMonomial X K) := ⟨SQuot.mkNorm ⟨0,1⟩ sorry⟩


  instance : Monoid (AltMonomial X K) :=
  {
    mul_assoc := sorry
    mul_one := sorry
    one_mul := sorry
    npow_zero' := sorry
    npow_succ' := sorry
  }

  instance : MulAction K (AltMonomial X K) :=
  {
    one_smul := sorry
    mul_smul := sorry
  }

end AltMonomial

