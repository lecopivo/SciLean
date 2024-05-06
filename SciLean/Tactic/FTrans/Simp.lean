import SciLean.Tactic.FTrans.Init
import Mathlib.Algebra.Group.Prod
import Mathlib.GroupTheory.GroupAction.Prod
import Mathlib.Algebra.SMulWithZero
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace SciLean

-- basic algebraic operations
attribute [ftrans_simp] add_zero zero_add sub_zero zero_sub sub_self neg_zero mul_zero zero_mul zero_smul smul_zero smul_eq_mul smul_neg eq_self iff_self mul_one one_mul one_smul tsub_zero pow_one mul_neg neg_mul neg_neg one_pow zero_pow div_self one_div

-- simps theorems for `Nat`
attribute [ftrans_simp] Nat.succ_sub_succ_eq_sub Nat.cast_ofNat

-- simp theorems for `Prod`
attribute [ftrans_simp] Prod.mk.eta Prod.fst_zero Prod.snd_zero Prod.mk_add_mk Prod.mk_mul_mk Prod.mk_sub_mk Prod.neg_mk Prod.vadd_mk -- Prod.smul_mk

-- simp theorems for `Equiv`
attribute [ftrans_simp] Equiv.invFun_as_coe Equiv.symm_symm

-- simp theorems for `if _ then _ else _`
attribute [ftrans_simp] ite_self dite_eq_ite eq_self ite_true ite_false dite_true dite_false ite_mul mul_ite

-- simp theorems for `Sum`
attribute [ftrans_simp] Sum.inr.injEq Sum.inl.injEq

-- complex
attribute [ftrans_simp] Complex.conj_I

-- pi type and algebra
attribute [ftrans_simp] Pi.zero_apply Pi.add_apply Pi.sub_apply Pi.mul_apply Pi.neg_apply Pi.one_apply Pi.smul_apply Pi.pow_apply

-- finrank
attribute [ftrans_simp]
  FiniteDimensional.finrank_self FiniteDimensional.finrank_prod

-- normalize `<` and `≤`
attribute [ftrans_simp]
  not_le

-- setOf
open Set in
attribute [ftrans_simp]
  mem_setOf_eq not_le  setOf_eq_eq_singleton mem_Ioo mem_Icc mem_Ico mem_Ioc mem_compl_iff mem_prod_eq

-- PUnit
attribute [ftrans_simp]
  PUnit.default_eq_unit

-- finset
attribute [ftrans_simp]
  Finset.card_singleton Finset.univ_unique Finset.sum_const

-- IndexType
attribute [ftrans_simp] IndexType.card_sum IndexType.card_prod IndexType.card_unit
