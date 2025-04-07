import SciLean.Meta.SimpAttr
import Mathlib.Algebra.Group.Prod
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace SciLean

-- basic algebraic operations
attribute [simp_core] add_zero zero_add sub_zero zero_sub sub_self neg_zero mul_zero zero_mul zero_smul smul_zero smul_eq_mul smul_neg eq_self iff_self mul_one one_mul one_smul tsub_zero pow_one mul_neg neg_mul neg_neg one_pow zero_pow div_self one_div inv_one neg_sub sub_neg_eq_add

-- simps theorems for `Nat`
attribute [simp_core] Nat.succ_sub_succ_eq_sub Nat.cast_ofNat

-- simp theorems for `Prod`
attribute [simp_core] Prod.mk.eta Prod.fst_zero Prod.snd_zero Prod.mk_add_mk Prod.mk_mul_mk Prod.mk_sub_mk Prod.neg_mk Prod.vadd_mk Prod.smul_mk

-- simp theorems for `Equiv`
attribute [simp_core] Equiv.invFun_as_coe Equiv.symm_symm

-- simp theorems for `if _ then _ else _`
attribute [simp_core] ite_self dite_eq_ite eq_self ite_true ite_false dite_true dite_false

-- simp theorems for `Sum`
attribute [simp_core] Sum.inr.injEq Sum.inl.injEq

-- complex
attribute [simp_core] Complex.conj_I

-- pi type and algebra
attribute [simp_core] Pi.zero_apply Pi.add_apply Pi.sub_apply Pi.mul_apply Pi.neg_apply Pi.one_apply Pi.smul_apply Pi.pow_apply

-- finrank
attribute [simp_core]
  Module.finrank_self Module.finrank_prod

-- normalize `<` and `≤`
attribute [simp_core]
  not_le

-- setOf and membership
-- bunch of other theorems are in SciLean.Mathlib.Set
open Set in
attribute [simp_core]
  Set.top_eq_univ Set.inter_univ Set.univ_inter mem_setOf_eq not_le setOf_eq_eq_singleton mem_compl_iff mem_preimage

-- PUnit
attribute [simp_core]
  PUnit.default_eq_unit

-- finset
attribute [simp_core]
  Finset.card_singleton Finset.univ_unique Finset.sum_const

-- Eq
attribute [simp_core]
  eq_rec_constant





-- Lawful Monad

/-- The same as `pure_bind` but we should include let binding on rhs for better code generations. -/
@[simp_core]
theorem pure_bind' {m} [Monad m] [LawfulMonad m] (x : α) (f : α → m β) :
  pure x >>= f = let x := x; f x := by simp
