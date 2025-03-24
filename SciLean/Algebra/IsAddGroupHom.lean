import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.LinearAlgebra.Prod

import SciLean.Data.IndexType
import SciLean.Meta.GenerateLinearMapSimp

import Mathlib.Tactic.FunProp

open SciLean

variable {X Y Z ι : Type _} {E : ι → Type _}
  [AddGroup X]
  [AddGroup Y]
  [AddGroup Z]
  [∀ i, AddGroup (E i)]

@[fun_prop]
structure IsAddGroupHom (f : X → Y) : Prop where
  map_add : ∀ x y, f (x + y) = f x + f y
  map_neg : ∀ x, f (-x) = - f x

namespace IsAddGroupHom

@[fun_prop]
theorem id_rule : IsAddGroupHom (fun x : X => x) := by constructor <;> aesop

@[fun_prop]
theorem const_rule : IsAddGroupHom (fun _ : X => (0:Y)) := by constructor <;> aesop

@[fun_prop]
theorem comp_rule (f : Y → Z) (g : X → Y) (hf : IsAddGroupHom f) (hg : IsAddGroupHom g) :
    IsAddGroupHom (fun x => f (g x)) := by constructor <;> simp (disch:=assumption) [map_add,map_neg]

@[fun_prop]
theorem apply_rule (i : ι) :
    IsAddGroupHom (fun (f : (i' : ι) → E i') => f i) := by
  constructor <;> simp

@[fun_prop]
theorem pi_rule (f : X → (i : ι) → E i) (hf : ∀ i, IsAddGroupHom (f · i)) :
    IsAddGroupHom (fun x i => f x i) := by
  constructor <;> (intros; funext i; simp [(hf i).map_add,(hf i).map_neg])

end IsAddGroupHom

open IsAddGroupHom

variable {X Y Z ι : Type _} {E : ι → Type _}
  [AddCommGroup X]
  [AddCommGroup Y]
  [AddCommGroup Z]
  [∀ i, AddGroup (E i)]

-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_prop]
theorem Prod.mk.arg_fstsnd.IsAddGroupHom_rule
    (f : X → Z) (g : X → Y)
    (hf : IsAddGroupHom f) (hg : IsAddGroupHom g) :
    IsAddGroupHom fun x => (g x, f x) := by
  constructor
  · simp [hf.map_add,hg.map_add]
  · simp [hf.map_neg,hg.map_neg]


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.fst.arg_self.IsAddGroupHom_rule
    (f : X → Y×Z) (hf : IsAddGroupHom f) : IsAddGroupHom fun (x : X) => (f x).fst := by
  constructor
  · simp [hf.map_add]
  · simp [hf.map_neg]

-- #generate_linear_map_simps Prod.fst.arg_self.IsAddGroupHom_rule_simple


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.snd.arg_self.IsAddGroupHom_rule
    (f : X → Y×Z) (hf : IsAddGroupHom f) : IsAddGroupHom fun (x : X) => (f x).snd := by
  constructor
  · simp [hf.map_add]
  · simp [hf.map_neg]

-- #generate_linear_map_simps Prod.snd.arg_self.IsAddGroupHom_rule_simple


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.IsAddGroupHom_rule
    (f : X → Y) (hf : IsAddGroupHom f) : IsAddGroupHom fun x => - f x := by
  constructor
  · simp [hf.map_add, add_comm]
  · simp [hf.map_neg]

-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.IsAddGroupHom_rule
    (f g : X → Y) (hf : IsAddGroupHom f) (hg : IsAddGroupHom g) :
    IsAddGroupHom fun x => f x + g x := by
  constructor
  · simp [hf.map_add,hg.map_add,add_comm]; sorry_proof
  · simp [hf.map_neg,hg.map_neg,add_comm]




-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0a1.IsAddGroupHom_rule
    (f g : X → Y) (hf : IsAddGroupHom f) (hg : IsAddGroupHom g) :
    IsAddGroupHom fun x => f x - g x := by
  constructor
  · simp [hf.map_add,hg.map_add,add_comm]; sorry_proof
  · simp [hf.map_neg,hg.map_neg,add_comm,←neg_add_eq_sub]


-- sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

-- @[fun_prop]
-- theorem sum.arg_f.IsAddGroupHom_rule
--   [IndexType ι]
--   (f : X → ι → Y) (hf : ∀ i, IsAddGroupHom (f · i))
--   : IsAddGroupHom fun x => ∑ i, f x i := by have := hf; sorry_proof


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_prop]
theorem ite.arg_te.IsAddGroupHom_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : IsAddGroupHom t) (he : IsAddGroupHom e)
  : IsAddGroupHom fun x => ite c (t x) (e x) :=
by
  induction dec
  case isTrue h  => simp[h]; fun_prop
  case isFalse h => simp[h]; fun_prop


@[fun_prop]
theorem dite.arg_te.IsAddGroupHom_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (ht : ∀ p, IsAddGroupHom (t p))
  (e : ¬c → X → Y) (he : ∀ p, IsAddGroupHom (e p))
  : IsAddGroupHom fun x => dite c (t · x) (e · x) :=
by
  induction dec
  case isTrue h  => simp[h]; apply ht
  case isFalse h => simp[h]; apply he
