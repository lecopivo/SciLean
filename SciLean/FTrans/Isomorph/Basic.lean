import Lean
import Mathlib
import Mathlib.Data.Real.Basic
import SciLean.Tactic.FTrans.Basic

open Lean

namespace SciLean


class IsomorphicType (tag : Name) (α : Sort _) (α' : outParam (Sort _)) where
  equiv : α ≃ α'

instance 
  {α α' β β' : Type _}
  (tag : Name)
  [IsomorphicType tag α α']
  [IsomorphicType tag β β']
  : IsomorphicType tag (α × β) (α' × β') where
  equiv := {
    toFun := fun (x,y) =>  
      (IsomorphicType.equiv tag x, IsomorphicType.equiv tag y)
    invFun := fun (x,y) => 
      ((IsomorphicType.equiv tag).symm x, (IsomorphicType.equiv tag).symm y)
    left_inv := by simp[Function.LeftInverse, IsomorphicType.equiv]
    right_inv := by simp[Function.LeftInverse, Function.RightInverse, IsomorphicType.equiv]
  }


instance (P : Prop)
  : IsomorphicType tag P P where
  equiv := {
    toFun := fun p => p
    invFun := fun p => p
    left_inv := by simp[Function.LeftInverse]
    right_inv := by simp[Function.RightInverse,Function.LeftInverse]
  }


variable {α β γ : Type _}
  {α' β' γ' : outParam (Type _)}
  (tag : Name)
  [IsomorphicType tag α α']
  [IsomorphicType tag β β']
  [IsomorphicType tag γ γ']


def isomorph (f : α → β) (a' : α') : β' := 
    a' |> (IsomorphicType.equiv tag (α:=α)).symm
       |> f 
       |> (IsomorphicType.equiv tag)


def invIsomorph (f : α' → β') (a : α) : β := 
    a |> (IsomorphicType.equiv tag (α:=α))
      |> f 
      |> (IsomorphicType.equiv tag).symm


instance 
  {α α' β β' : Type _}
  (tag : Name)
  [IsomorphicType tag α α']
  [IsomorphicType tag β β']
  : IsomorphicType tag (α → β) (α' → β') where
  equiv := {
    toFun := fun f => isomorph tag f
    invFun := fun f => invIsomorph tag f
    left_inv := by simp[Function.LeftInverse, IsomorphicType.equiv, isomorph, invIsomorph]
    right_inv := by simp[Function.LeftInverse, Function.RightInverse, IsomorphicType.equiv, isomorph, invIsomorph]
  }
  

namespace isomorph

variable (α)
theorem id_rule 
  : isomorph tag (fun (x : α) => x)
    =
    fun (x : α') => x :=
by
  simp[isomorph]


theorem const_rule 
  (y : β)
  : isomorph tag (fun (_ : α) => y)
    =
    fun (_ : α') => (IsomorphicType.equiv tag) y :=
by
  simp[isomorph]

variable {α}
variable (β)
theorem proj_rule 
  (x : α)
  : isomorph tag (fun (f : α → β) => f x)
    =
    fun (f : α' → β') => f ((IsomorphicType.equiv tag) x) :=
by
  simp[isomorph, invIsomorph, IsomorphicType.equiv]
variable {β}

theorem comp_rule 
  (f : β → γ) (g : α → β)
  : isomorph tag (fun x => f (g x))
    =
    fun x => isomorph tag f (isomorph tag g x) := 
by
  simp[isomorph]


theorem let_rule 
  (f : α → β → γ) (g : α → β)
  : isomorph tag (fun x => let y := g x; f x y)
    =
    fun x' => 
      let y' := isomorph tag g x'
      isomorph tag (fun (xy : α×β) => f xy.1 xy.2) (x', y') := 
by
  funext x'; simp[isomorph, IsomorphicType.equiv]


theorem pi_rule 
  (f : α → β → γ) 
  : isomorph tag (fun x y => f x y)
    =
    fun x' => isomorph tag (f ((IsomorphicType.equiv tag).symm x')) := 
by
  funext x'; simp[isomorph, IsomorphicType.equiv]


-- Register `isomorph` as function transformation -------------------------------
--------------------------------------------------------------------------------


open Lean Meta FTrans
def ftransExt : FTransExt where
  ftransName := ``isomorph

  getFTransFun? e := 
    if e.isAppOf ``isomorph then

      if let .some f := e.getArg? 7 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``isomorph then
      e.modifyArg (fun _ => f) 7
    else          
      e

  idRule  e X := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppOptM ``id_rule #[X, none, tag, none], origin := .decl ``id_rule, rfl := false} ]
      (fun _ => none) e

  constRule e X y := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[X,tag,y], origin := .decl ``const_rule, rfl := false} ]
      (fun _ => none) e

  projRule e X i := do
    let tag := e.getArg! 4
    let X' := X.bindingBody!
    if X'.hasLooseBVars then
      trace[Meta.Tactic.ftrans.step] "can't handle this bvar app case, projection rule for dependent function of type {← ppExpr X} is not supported"
      return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[X, tag, i], origin := .decl ``proj_rule, rfl := false} ]
      (fun _ => none) e

  compRule e f g := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← withTransparency .all <| 
             mkAppM ``comp_rule #[tag, f, g], origin := .decl ``comp_rule, rfl := false} ]
      (fun _ => none) e

  letRule e f g := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[tag, f, g], origin := .decl ``let_rule, rfl := false} ]
      (fun _ => none) e

  piRule  e f := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[tag, f], origin := .decl ``pi_rule, rfl := false} ]
      (fun _ => none) e

  discharger := fun _ => none


-- register isomorph
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``isomorph, isomorph.ftransExt))


@[simp]
theorem isoapp (f : α → β) (x : α) : (IsomorphicType.equiv tag) (f x) = isomorph tag f (IsomorphicType.equiv tag x) := by simp[IsomorphicType.equiv, isomorph]

@[simp]
theorem isoext (a b : α) : a = b ↔ (IsomorphicType.equiv tag a) = (IsomorphicType.equiv tag b) := by simp[IsomorphicType.equiv]


@[simp]
theorem isofunext {β β' : Sort _} [IsomorphicType tag β β'] (f g : α → β) : f = g ↔ isomorph tag f = isomorph tag g := 
by
  sorry


section RealToFloat

variable {α α' β β' γ γ' : Type _}
  [IsomorphicType `RealToFloat α α']
  [IsomorphicType `RealToFloat β β']
  [IsomorphicType `RealToFloat γ γ']


noncomputable
scoped instance : IsomorphicType `RealToFloat ℝ Float where
  equiv := sorry


@[ftrans_rule]
axiom HAdd.hAdd.arg_a0a1.isomorphRealToFloat (f g : α → ℝ) 
  : isomorph `RealToFloat (fun x => f x + g x)
    =
    fun x : α' => isomorph `RealToFloat f x + isomorph `RealToFloat g x

@[ftrans_rule]
axiom HSub.hSub.arg_a0a1.isomorphRealToFloat (f g : α → ℝ) 
  : isomorph `RealToFloat (fun x => f x - g x)
    =
    fun x : α' => isomorph `RealToFloat f x - isomorph `RealToFloat g x


@[ftrans_rule]
axiom HMul.hMul.arg_a0a1.isomorphRealToFloat (f g : α → ℝ) 
  : isomorph `RealToFloat (fun x => f x * g x)
    =
    fun x : α' => isomorph `RealToFloat f x * isomorph `RealToFloat g x


@[ftrans_rule]
axiom HDiv.hDiv.arg_a0a1.isomorphRealToFloat (f g : α → ℝ) 
  : isomorph `RealToFloat (fun x => f x / g x)
    =
    fun x : α' => isomorph `RealToFloat f x / isomorph `RealToFloat g x


@[ftrans_rule]
axiom HNeg.hNeg.arg_a0.isomorphRealToFloat (f : α → ℝ) 
  : isomorph `RealToFloat (fun x => - f x)
    =
    fun x : α' => - isomorph `RealToFloat f x


end RealToFloat

section FloatToReal

variable {α α' β β' γ γ' : Type _}
  [IsomorphicType `FloatToReal α α']
  [IsomorphicType `FloatToReal β β']
  [IsomorphicType `FloatToReal γ γ']


noncomputable
scoped instance : IsomorphicType `FloatToReal Float ℝ where
  equiv := sorry

noncomputable
abbrev floatToReal (x : Float) : ℝ := IsomorphicType.equiv `FloatToReal x

instance : Inv Float := ⟨fun x => 1.0 / x⟩

@[ftrans_rule]
axiom HAdd.hAdd.arg_a0a1.isomorphFloatToReal (f g : α → Float) 
  : isomorph `FloatToReal (fun x => f x + g x)
    =
    fun x : α' => isomorph `FloatToReal f x + isomorph `FloatToReal g x


@[ftrans_rule]
axiom HSub.hSub.arg_a0a1.isomorphFloatToReal (f g : α → Float) 
  : isomorph `FloatToReal (fun x => f x - g x)
    =
    fun x : α' => isomorph `FloatToReal f x - isomorph `FloatToReal g x


@[ftrans_rule]
axiom HMul.hMul.arg_a0a1.isomorphFloatToReal (f g : α → Float) 
  : isomorph `FloatToReal (fun x => f x * g x)
    =
    fun x : α' => isomorph `FloatToReal f x * isomorph `FloatToReal g x


@[ftrans_rule]
axiom HDiv.hDiv.arg_a0a1.isomorphFloatToReal (f g : α → Float) 
  : isomorph `FloatToReal (fun x => f x / g x)
    =
    fun x : α' => isomorph `FloatToReal f x / isomorph `FloatToReal g x


@[ftrans_rule]
axiom HNeg.hNeg.arg_a0.isomorphFloatToReal (f : α → Float) 
  : isomorph `FloatToReal (fun x => - f x)
    =
    fun x : α' => - isomorph `FloatToReal f x


@[ftrans_rule]
axiom HDiv.hDiv.arg_a0.isomorphFloatToReal (f : α → Float) 
  : isomorph `FloatToReal (fun x => (f x)⁻¹)
    =
    fun x : α' => (isomorph `FloatToReal f x)⁻¹


@[ftrans_rule]
axiom Float.exp.arg_a0.isomorphFloatToReal (f : α → Float) 
  : isomorph `FloatToReal (fun x => Float.exp (f x))
    =
    fun x => Real.exp (isomorph `FloatToReal f x)

@[ftrans_rule]
axiom Float.sin.arg_a0.isomorphFloatToReal (f : α → Float) 
  : isomorph `FloatToReal (fun x => Float.sin (f x))
    =
    fun x => Real.sin (isomorph `FloatToReal f x)

@[ftrans_rule]
axiom Float.cos.arg_a0.isomorphFloatToReal (f : α → Float) 
  : isomorph `FloatToReal (fun x => Float.cos (f x))
    =
    fun x => Real.cos (isomorph `FloatToReal f x)

@[ftrans_rule]
axiom Float.asin.arg_a0.isomorphFloatToReal (f : α → Float) 
  : isomorph `FloatToReal (fun x => Float.asin (f x))
    =
    fun x => Real.arcsin (isomorph `FloatToReal f x)

@[ftrans_rule]
axiom Float.acos.arg_a0.isomorphFloatToReal (f : α → Float) 
  : isomorph `FloatToReal (fun x => Float.acos (f x))
    =
    fun x => Real.arccos (isomorph `FloatToReal f x)

@[ftrans_rule]
axiom Float.atan.arg_a0.isomorphFloatToReal (f : α → Float) 
  : isomorph `FloatToReal (fun x => Float.atan (f x))
    =
    fun x => Real.arctan (isomorph `FloatToReal f x)



@[simp]
axiom Zero.zero.isomorphFloatToReal 
  : floatToReal (0 : Float)
    =
    (0 : ℝ)


@[simp]
axiom One.one.isomorphFloatToReal 
  : floatToReal (1 : Float)
    =
    (1 : ℝ)


instance : Semigroup Float where
  mul_assoc := by 
    intro a b c
    apply (isoext `FloatToReal _ _).2
    ftrans; ftrans; ftrans
    rw[mul_assoc]


instance : Monoid Float where
  one_mul := by 
    intro a
    apply (isoext `FloatToReal _ _).2
    simp; ftrans
  mul_one := by 
    intro a
    apply (isoext `FloatToReal _ _).2
    simp; ftrans


instance : DivInvMonoid Float where
  div_eq_mul_inv := by 
    intro a b
    apply (isoext `FloatToReal _ _).2
    simp; ftrans; ftrans; rw[div_eq_mul_inv]
  zpow := zpowRec
  zpow_zero' := by intros; rfl
  zpow_succ' := by intros; rfl
  zpow_neg' := by intros; rfl


instance : AddSemigroup Float where
  add_assoc := by 
    intro a b c
    apply (isoext `FloatToReal _ _).2
    simp; ftrans; ftrans; rw[add_assoc]

instance : AddZeroClass Float where
  zero_add := by 
    intro a
    apply (isoext `FloatToReal _ _).2
    simp; ftrans
  add_zero := by 
    intro a
    apply (isoext `FloatToReal _ _).2
    simp; ftrans

instance : AddMonoid Float where
  zero_add := by 
    intro a
    apply (isoext `FloatToReal _ _).2
    simp
  add_zero := by 
    intro a
    apply (isoext `FloatToReal _ _).2
    simp

instance : AddCommSemigroup Float where
  add_comm := by 
    intro a b
    apply (isoext `FloatToReal _ _).2
    simp; ftrans; rw[add_comm]
  
instance : AddCommMonoid Float where
  add_comm := by 
    intro a b
    apply (isoext `FloatToReal _ _).2
    simp; ftrans; rw[add_comm]
  
instance : SubNegMonoid Float where
  sub_eq_add_neg := sorry -- important
  
instance : AddGroup Float where
  add_left_neg := sorry

instance : AddCommGroup Float where
  add_comm := sorry

instance : Semiring Float where
  left_distrib := sorry 
  right_distrib := sorry
  zero_mul := sorry 
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

-- instance : Ring Float where
--   add_left_neg := sorry
  
-- instance : Field Float where
--   mul_comm := sorry
--   exists_pair_ne := sorry
--   mul_inv_cancel := sorry
--   inv_zero := sorry
    
