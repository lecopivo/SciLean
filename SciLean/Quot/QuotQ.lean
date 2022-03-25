import SciLean.Quot.Basic

partial def Nat.toSubscript (n : Nat) : String := 
  let rec impl (k : Nat) : String :=
    if k≠0 then
      match k%10 with
      | 0 => impl (k/10) ++ "₀"
      | 1 => impl (k/10) ++ "₁"
      | 2 => impl (k/10) ++ "₂"
      | 3 => impl (k/10) ++ "₃"
      | 4 => impl (k/10) ++ "₄"
      | 5 => impl (k/10) ++ "₅"
      | 6 => impl (k/10) ++ "₆"
      | 7 => impl (k/10) ++ "₇"
      | 8 => impl (k/10) ++ "₈"
      | 9 => impl (k/10) ++ "₉"
      | _ => ""
    else
      ""
  if n=0 then 
    "₀"
  else
    impl n

partial def Nat.toSupscript (n : Nat) : String := 
  let rec impl (k : Nat) : String :=
    if k≠0 then
      match k%10 with
      | 0 => impl (k/10) ++ "⁰"
      | 1 => impl (k/10) ++ "¹"
      | 2 => impl (k/10) ++ "²"
      | 3 => impl (k/10) ++ "³"
      | 4 => impl (k/10) ++ "⁴"
      | 5 => impl (k/10) ++ "⁵"
      | 6 => impl (k/10) ++ "⁶"
      | 7 => impl (k/10) ++ "⁷"
      | 8 => impl (k/10) ++ "⁸"
      | 9 => impl (k/10) ++ "⁹"
      | _ => ""
    else
      ""
  if n=0 then 
    "₀"
  else
    impl n

class ToDebugString (α : Type u) where
   toDebugString : α → String

namespace SciLean.Quot'

  -- class QForm {α} (S : Rel α) where
  --   RedForm  : α → Prop 
  --   NormForm : α → Prop
  --   norm_red : ∀ x, NormForm x → RedForm x
  --   norm_eq  : ∀ x y, S x y → NormForm x → NormForm y → x = y

  inductive Level where
    | redLvl (lvl : Nat) : Level
    | normLvl : Level

  export Level (redLvl normLvl)

  namespace Level

    inductive lt : Level → Level → Prop where
      | redLt (n n' : Nat) (h : n < n') : lt (redLvl n) (redLvl n')
      | normLt (n : Nat) : lt (redLvl n) normLvl

    instance : LT Level := ⟨lt⟩
    instance : LE Level := ⟨λ l l' => l < l' ∨ l = l'⟩

    instance decLt (l l' : Level) : Decidable (l < l') :=
    match l, l' with
    | redLvl n, redLvl n' => if n < n' then isTrue sorry else isFalse sorry
    | redLvl n, normLvl => isTrue sorry
    | normLvl, _ => isFalse sorry

    instance decLe (l l' : Level) : Decidable (l ≤ l') :=
    match l, l' with
    | redLvl n, redLvl n' => if n ≤ n' then isTrue sorry else isFalse sorry
    | normLvl, normLvl => isFalse sorry
    | redLvl n, normLvl => isTrue sorry
    | normLvl, redLvl n' => isFalse sorry

    instance decEq (l l' : Level) : Decidable (l = l') :=
    match l, l' with
    | redLvl n, redLvl n' => if n = n' then isTrue sorry else isFalse sorry
    | normLvl, normLvl => isTrue sorry
    | _, _ => isFalse sorry

    instance : HAdd Level Nat Level := 
    ⟨λ l n' => 
      match l with
      | redLvl n => redLvl (n + n')
      | normLvl => normLvl⟩

    -- instance (n : Nat) : OfNat Level n := ⟨redLvl n⟩

  end Level

  abbrev rawLvl := redLvl 0

  class QForm {α} (S : Rel α) where
    -- normLvl : Nat
    RedForm  : Level → α → Prop 
    redform_norm : ∀ x y, S x y → RedForm normLvl x → RedForm normLvl y → x = y
    redform_zero : ∀ x, RedForm rawLvl x = True
    redform_succ : ∀ x n, RedForm (n+(1 : Nat)) x → RedForm n x
    redform_inf  : ∀ x lvl, RedForm normLvl x → RedForm lvl x

  open QForm

  --- IsQHom' S R lvl f  preserves all reduction levels bellow or equal to lvl
  class IsQHom' (lvl : Level) (S : Rel α) [QForm S]  (f : α → α) extends IsQHom S S f where
    preserve_red : ∀ x lvl', lvl' ≤ lvl → RedForm S lvl' x → RedForm S lvl' (f x)

  -- class IsQHomN (S : Rel α) (R : Rel β) [QForm S] [QForm R] (f : α → β) extends IsQHomR S R f where
  --   preserve_norm : ∀ x : α, NormForm S x → NormForm R (f x)

  -- class IsQHomR₂ (S : Rel α) (R : Rel β) [QForm S] [QForm R] (f : α → β) extends IsQHom S R f where
  --   preserve_red : ∀ x : α, RedForm S x → RedForm R (f x)

  -- class IsQHomN₂ (S : Rel α) (R : Rel β) [QForm S] [QForm R] (f : α → β) extends IsQHomR S R f where
  --   preserve_norm : ∀ x : α, NormForm S x → NormForm R (f x)

  ---
  
  class QReduce {α} (S : Rel α) (lvl : Level) [QForm S] where
    reduce : α → α
    is_reduce : ∀ x, RedForm S lvl (reduce x)
    eq_reduce : ∀ x, S x (reduce x)
    -- Reduction should not destroy stronger reduction levels
    preserve_stronger : ∀ x lvl', lvl' > lvl → RedForm S lvl' x → RedForm S lvl' (reduce x)

  class Reduce (α) (lvl : Level) where
    reduce : α → α
    id_reduce : ∀ x : α, reduce x = x

  -- instance (priority := low) {α lvl} : Reduce α lvl :=
  -- {
  --   reduce := id
  --   id_reduce := λ _ => rfl
  -- }

  instance {lvl} : Reduce Nat lvl := ⟨id, λ _ => rfl⟩
  instance {lvl} : Reduce Int lvl := ⟨id, λ _ => rfl⟩
  instance {lvl} : Reduce Float lvl := ⟨id, λ _ => rfl⟩

  export Reduce (reduce)

  ---

  abbrev QNormalize {α} (S : Rel α) [QForm S] := QReduce S normLvl
  abbrev Normalize (α) := Reduce α normLvl

  abbrev normalize {α} (a : α) [Normalize α] : α := Reduce.reduce normLvl a
  
  -- class Normalize (α) where
  --   normalize : α → α
  --   id_normalize : ∀ x : α, normalize x = x

  -- instance (priority := low) {α} : Normalize α :=
  -- {
  --   normalize := id
  --   id_normalize := λ _ => rfl
  -- }

  -- export Normalize (normalize)

  ---
  
  -- class QNormalize {α} (S : Rel α) [QForm S] where
  --   normalize : α → α
  --   is_normalize : ∀ x, NormForm S (normalize x)
  --   eq_normalize : ∀ x, S x (normalize x)

  -- ---

  -- This just tags `Repr` in which form they are
  structure QRepr {α} (S : Rel α) [QForm S] where
    repr : α
    lvl : Level
    h : RedForm S lvl x

  namespace QRepr 

    variable {α} {S : Rel α} [QForm S]

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

    def reduce (x : QRepr S) (lvl : Level) [QReduce S lvl] : QRepr S :=
      if lvl > x.lvl then
        ⟨QReduce.reduce S lvl x.repr, lvl, sorry⟩
      else
        x

    abbrev normalize (x : QRepr S) [QReduce S normLvl] : QRepr S :=
      x.reduce normLvl

  end QRepr

end Quot'

open Quot' in
abbrev Quot' {α} (S : Rel α) [QForm S]
  := Quot (λ x y : QRepr S => S x.repr y.repr)

namespace Quot'

  variable {α} {S : Rel α} [QForm S]
  variable {β} {R : Rel β} [QForm R]
  variable {γ} {T : Rel γ} [QForm T]

  -- Normalized representant is unique, follows from `QForm.norm_eq`
  def nrepr [QNormalize S] : Quot' S → α := Quot.lift (λ x => x.normalize.repr) sorry

  noncomputable
  def repr' (x : Quot' S) : QRepr S := x.repr

  noncomputable
  def repr (x : Quot' S) : α := x.repr'.repr

  def lift (f : α → β) [hom : IsQHom S R f] : Quot' S → Quot' R :=
  Quot.lift (λ x => ⟦⟨f x.repr, rawLvl, by intro x; rw[QForm.redform_zero]; simp; done⟩⟧) sorry

  def lift' (lvl : Level) (f : α → α) [hom : IsQHom' lvl S f] : Quot' S → Quot' S :=
  Quot.lift (λ x => ⟦⟨f x.repr, lvl, sorry⟩⟧) sorry

  abbrev nlift (f : α → α) [hom : IsQHom' normLvl S f] : Quot' S → Quot' S :=
    lift' normLvl f

  def lift₂ (f : α → β → γ) [hom : IsQHom₂ S R T f] : Quot' S → Quot' R → Quot' T :=
  Quot.lift (λ x => 
    Quot.lift (λ y => ⟦⟨f x.repr y.repr, rawLvl, sorry⟩⟧               
      ) sorry
    ) sorry

  instance {lvl} [QReduce S lvl] : Reduce (Quot' S) lvl :=
  {
    reduce := Quot.lift (λ x : QRepr S => ⟦x.reduce lvl⟧) sorry
    id_reduce := sorry
  }

  instance [QNormalize S] [DecidableEq α] : DecidableEq (Quot' S) :=
    λ a b => 
      if a.nrepr = b.nrepr 
      then (isTrue sorry) 
      else (isFalse sorry)

  variable (x : Quot' S) [QNormalize S]

  #check x.repr
  #check x.repr'
  #check x.nrepr

  constant toDebugString (x : Quot' S) [ToString α] : String :=
    Quot.lift (λ x => s!"⟦{x.repr}⟧{match x.lvl with 
                                    | redLvl n => n.toSubscript 
                                    | normLvl => "∞"}") sorry x

end Quot'

  


  -- TODO:
  ---  QNormalize -> Normalize
  ---  QNormalize -> DecidableEq
