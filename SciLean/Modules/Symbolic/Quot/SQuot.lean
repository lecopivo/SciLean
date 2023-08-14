import SciLean.Quot.Basic

namespace SciLean.Quot'

  class QForm {α} (S : Rel α) where
    RedForm  : α → Prop 
    NormForm : α → Prop
    norm_red : ∀ x, NormForm x → RedForm x
    norm_eq  : ∀ x y, S x y → NormForm x → NormForm y → x = y

  open QForm

  class IsQHomR (S : Rel α) (R : Rel β) [QForm S] [QForm R] (f : α → β) extends IsQHom S R f where
    preserve_red : ∀ x : α, RedForm S x → RedForm R (f x)

  class IsQHomN (S : Rel α) (R : Rel β) [QForm S] [QForm R] (f : α → β) extends IsQHomR S R f where
    preserve_norm : ∀ x : α, NormForm S x → NormForm R (f x)

  ---
  
  class QReduce {α} (S : Rel α) [QForm S] where
    reduce : α → α
    is_reduce : ∀ x, RedForm S (reduce x)
    eq_reduce : ∀ x, ⟦x, S⟧ = ⟦reduce x⟧
    preserve_norm : ∀ x, NormForm S x → NormForm S (reduce x)

  class Reduce (α) where
    reduce : α → α
    id_reduce : ∀ x : α, reduce x = x

  ---
  
  class QNormalize {α} (S : Rel α) [QForm S] where
    normalize : α → α
    is_normalize : ∀ x, NormForm S (normalize x)
    eq_normalize : ∀ x, ⟦x, S⟧ = ⟦normalize x⟧

  class Normalize (α) where
    normalize : α → α
    id_normalize : ∀ x : α, normalize x = x

  ---

  -- This just tags `Repr` in which form they are
  inductive QRepr {α} (S : Rel α) [QForm S] where
    | raw  (x : α) : QRepr S
    | red  (x : α) (h : RedForm S x)  : QRepr S
    | norm (x : α) (h : NormForm S x) : QRepr S

  namespace QRepr 

    variable {α} {S : Rel α} [QForm S]

    def repr (x : QRepr S) : α :=
      match x with
      | raw  x   => x
      | red  x _ => x
      | norm x _ => x

    @[simp]
    theorem raw_repr (x : α) : (raw x : QRepr S).repr = x := by simp[repr] done

    @[simp]
    theorem red_repr (x : α) (h : RedForm S x) : (red x h : QRepr S).repr = x := by simp[repr] done

    @[simp]
    theorem norm_repr (x : α) (h : NormForm S x) : (norm x h : QRepr S).repr = x := by simp[repr] done

    def isReduced (x : QRepr S) : Bool :=
      match x with
      | raw x => false
      | _ => true

    def isNormalized (x : QRepr S) : Bool :=
      match x with
      | norm x _ => true
      | _ => false

    -- variable {Repr' } {R'  : Repr'  → Repr'  → Prop} [Symbolic R']
    -- variable {Repr''} {R'' : Repr'' → Repr'' → Prop} [Symbolic R'']

    -- def lift (f : Repr → Repr') (x : QRepr R) : QRepr R' := raw (f x.repr)

    -- def lift₂ (f : Repr → Repr' → Repr'') (x : QRepr R) (x' : QRepr R') : QRepr R'' :=
    --   raw (f x.repr x'.repr)

    -- def liftHom (f : Repr → Repr') (h : SHom R R' f) (x : QRepr R) : QRepr R' := 
    --   match x with
    --   | raw x => raw (f x)
    --   | red  x h' => red  (f x) (h.preserve_red x h')
    --   | norm x h' => norm (f x) (h.preserve_norm x h')

    -- @[simp] 
    -- theorem lift_hom_repr (f : Repr → Repr') (h : SHom R R' f) (x : QRepr R)
    --   : (liftHom f h x).repr = f x.repr
    --   := 
    --   by induction x 
    --      repeat simp[liftHom]
    --      done

    -- def liftHom₂ (f : Repr → Repr' → Repr'') (h : SHom₂ R R' R'' f) 
    --   (x : QRepr R) (y : QRepr R') : QRepr R'' :=
    --   match x, y with
    --   | red x hx,  red y hy  => red  (f x y) (h.preserve_red  x y hx hy)
    --   | norm x hx, norm y hy => norm (f x y) (h.preserve_norm x y hx hy)
    --   | x, y => raw (f x.repr y.repr)

    def reduce (x : QRepr S) [QReduce S] : QRepr S :=
      match x with
      | raw x => red (QReduce.reduce S x) (QReduce.is_reduce x)
      | x => x

    def normalize (x : QRepr S) [QNormalize S] : QRepr S :=
      match x with
      | raw x   => norm (QNormalize.normalize S x) (QNormalize.is_normalize x)
      | red x _ => norm (QNormalize.normalize S x) (QNormalize.is_normalize x)
      | x => x

  end QRepr

end Quot'

open Quot' in
def Quot' {α} (S : Rel α) [QForm S]
  := Quot (λ x y : QRepr S => S x.repr y.repr)

namespace Quot'

  variable {α} {S : Rel α} [QForm S]

  -- Normalized representant is unique, follows from `QForm.norm_eq`
  def nrepr [QNormalize S] : Quot' S → α := Quot.lift (λ x => x.normalize.repr) sorry

  noncomputable
  def srepr (x : Quot' S) : QRepr S := x.repr

  noncomputable
  def repr (x : Quot' S) : α := x.srepr.repr

  variable (x : Quot' S)

  #check x.repr
  #check x.srepr

end Quot'

  


  -- TODO:
  ---  QNormalize -> Normalize
  ---  QNormalize -> DecidableEq
