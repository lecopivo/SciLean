class Symbolic {Repr : Type} (R : Repr → Repr → Prop) where
  RedForm  : Repr → Prop 
  NormForm : Repr → Prop
  norm_red : ∀ x, NormForm x → RedForm x
  R_norm  : ∀ x y, R x y → NormForm x → NormForm y → x = y

namespace Symbolic

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

    def liftHom (f : Repr → Repr') (h : SHom R R' f) (x : SRepr R) : SRepr R' := 
      match x with
      | raw x => raw (f x)
      | red  x h' => red  (f x) (h.preserve_red x h')
      | norm x h' => norm (f x) (h.preserve_norm x h')

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

  def SQuot.liftHom (f : Repr → Repr') (h : SHom R R' f) 
    : SQuot R → SQuot R'
    := Quot.lift (λ x' => Quot.mk _ (SRepr.liftHom f h x')) 
        (by intro a b req
            apply Quot.sound
            induction a
            repeat 
              (induction b
               repeat 
                 (simp[SRepr.repr, SRepr.liftHom]
                  simp[SRepr.repr] at req
                  apply h.is_hom
                  assumption))
            done)

  def SQuot.liftHom₂ (f : Repr → Repr' → Repr'') (h : SHom₂ R R' R'' f) 
    : SQuot R → SQuot R' → SQuot R''
    := Quot.lift (λ x' => Quot.lift (λ y' => Quot.mk _ (SRepr.liftHom₂ f h x' y')) sorry) sorry

  instance [SReduce R] : Reduce (SQuot R) :=
  {
    reduce := SQuot.liftHom (SReduce.reduce R) sorry
    id_reduce := sorry
  }

  instance [SNormalize R] : Normalize (SQuot R) :=
  {
    normalize := SQuot.liftHom (SNormalize.normalize R) sorry
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

namespace SymmMonoid

  structure Repr (X : Type u) where
    vars : List X

  def RedForm {X : Type u} [LE X] (x : Repr X) := x.1.Sorted

  abbrev NormForm


end SymmMonoid
