import SciLean.Core.Objects.IsomorphicType

import SciLean.Tactic.FTrans.Basic

open Lean

namespace SciLean

variable 
  {α β γ : Type _}
  {α' β' γ' : outParam (Type _)}
  (tag : Name)
  [IsomorphicType tag α α']
  [IsomorphicType tag β β']
  [IsomorphicType tag γ γ']

namespace isomorph

variable (α)
theorem id_rule 
  : isomorph tag (fun (x : α) => x)
    =
    fun (x : α') => x :=
by
  simp[isomorph]


theorem const_rule (y : β)
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
  funext x'; simp[isomorph, IsomorphicType.equiv, -isomorph.app]

theorem pi_rule 
  (f : α → β → γ) 
  : isomorph tag (fun x y => f x y)
    =
    fun x' => isomorph tag (f ((IsomorphicType.equiv tag).symm x')) := 
by
  funext x'; simp[isomorph, IsomorphicType.equiv]


-- Register `isomorph` as function transformation -------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := return none

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
      e.setArg 7 f
    else          
      e

  idRule  e X := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppOptM ``id_rule #[X, none, tag, none], origin := .decl ``id_rule, rfl := false} ]
      discharger e

  constRule e X y := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[X,tag,y], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := do
    let tag := e.getArg! 4
    let X' := X.bindingBody!
    if X'.hasLooseBVars then
      trace[Meta.Tactic.ftrans.step] "can't handle this bvar app case, projection rule for dependent function of type {← ppExpr X} is not supported"
      return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[X, tag, i], origin := .decl ``proj_rule, rfl := false} ]
      discharger e

  compRule e f g := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← withTransparency .all <|
             mkAppM ``comp_rule #[tag, f, g], origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[tag, f, g], origin := .decl ``let_rule, rfl := false} ]
      discharger e

  piRule  e f := do
    let tag := e.getArg! 4
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[tag, f], origin := .decl ``pi_rule, rfl := false} ]
      discharger e

  discharger := discharger


-- register isomorph
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``isomorph, isomorph.ftransExt))


#exit


instance : CommRing Float where
  zero_mul := by intros; apply ext `FloatToReal; (repeat ftrans); try ring
  mul_zero := by intros; apply ext `FloatToReal; sorry -- (repeat ftrans); try ring
  mul_comm := by intros; apply ext `FloatToReal; sorry --(repeat ftrans); try ring
  left_distrib := by intros; apply ext `FloatToReal; sorry -- (repeat ftrans); try ring
  right_distrib := by intros; apply ext `FloatToReal; sorry -- (repeat ftrans); try ring
  mul_one := sorry_proof
  one_mul := sorry_proof
  npow n x := x.pow (n.toFloat)  --- TODO: change this implementation
  npow_zero n := sorry_proof
  npow_succ n x := sorry_proof
  mul_assoc := sorry_proof
  add_comm := sorry_proof
  add_assoc := sorry_proof
  add_zero := sorry_proof
  zero_add := sorry_proof
  add_left_neg := sorry_proof
  nsmul n x := n.toFloat * x
  nsmul_zero := sorry_proof
  nsmul_succ n x := sorry_proof
  sub_eq_add_neg a b := sorry_proof
  natCast n := n.toFloat
  natCast_zero := sorry_proof
  natCast_succ := sorry_proof
  intCast n := if n ≥ 0 then n.toNat.toFloat else -((-n).toNat).toFloat
  intCast_ofNat := sorry_proof
  intCast_negSucc := sorry_proof

instance : Field Float where
  exists_pair_ne := sorry_proof
  div_eq_mul_inv := sorry_proof 
  mul_inv_cancel := sorry_proof
  inv_zero := sorry_proof

#exit

instance : Semigroup Float where
  mul_assoc := by 
    intro a b c
    apply ext `FloatToReal
    ftrans; ftrans; ftrans
    rw[mul_assoc]


instance : Monoid Float where
  one_mul := by 
    intro a
    apply ext `FloatToReal
    simp; ftrans
  mul_one := by 
    intro a
    apply ext `FloatToReal
    simp; ftrans


instance : DivInvMonoid Float where
  div_eq_mul_inv := by 
    intro a b
    apply ext `FloatToReal
    simp; ftrans; ftrans; rw[div_eq_mul_inv]
  zpow := zpowRec
  zpow_zero' := by intros; rfl
  zpow_succ' := by intros; rfl
  zpow_neg' := by intros; rfl


instance : AddSemigroup Float where
  add_assoc := by 
    intro a b c
    apply ext `FloatToReal
    simp; ftrans; ftrans; rw[add_assoc]

instance : AddZeroClass Float where
  zero_add := by 
    intro a
    apply ext `FloatToReal
    simp; ftrans
  add_zero := by 
    intro a
    apply ext `FloatToReal
    simp; ftrans

instance : AddMonoid Float where
  zero_add := by 
    intro a
    apply ext `FloatToReal
    simp
  add_zero := by 
    intro a
    apply ext `FloatToReal
    simp

instance : AddCommSemigroup Float where
  add_comm := by 
    intro a b
    apply ext `FloatToReal
    simp; ftrans; rw[add_comm]
  
instance : AddCommMonoid Float where
  add_comm := by 
    intro a b
    apply ext `FloatToReal
    simp; ftrans; rw[add_comm]
  
instance : SubNegMonoid Float where
  sub_eq_add_neg := by 
    intro a b
    apply ext `FloatToReal
    simp; ftrans; ftrans; rw[sub_eq_add_neg]
  
instance : AddGroup Float where
  add_left_neg := by 
    intro a
    apply ext `FloatToReal
    simp; ftrans; ftrans

instance : AddCommGroup Float where
  add_comm := by 
    intro a b
    apply ext `FloatToReal
    simp; ftrans; rw[add_comm]

instance : Semiring Float where
  left_distrib := sorry 
  right_distrib := sorry
  zero_mul := sorry 
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

instance : Ring Float where
  add_left_neg := sorry
  
-- instance : Field Float where
--   mul_comm := sorry
--   exists_pair_ne := sorry
--   mul_inv_cancel := sorry
--   inv_zero := sorry
    
