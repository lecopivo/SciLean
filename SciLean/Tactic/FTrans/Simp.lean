import SciLean.Tactic.FTrans.Init
import Mathlib.Algebra.Group.Prod
import Mathlib.GroupTheory.GroupAction.Prod
import Mathlib.Algebra.SMulWithZero
import Mathlib.Data.Complex.Basic

namespace SciLean

-- basic algebraic operations
attribute [ftrans_simp] add_zero zero_add sub_zero zero_sub sub_self neg_zero mul_zero zero_mul zero_smul smul_zero smul_eq_mul smul_neg eq_self iff_self mul_one one_mul one_smul tsub_zero pow_one

-- simps theorems for `Nat`
attribute [ftrans_simp] Nat.succ_sub_succ_eq_sub Nat.cast_ofNat

-- simp theorems for `Prod`
attribute [ftrans_simp] Prod.mk.eta Prod.fst_zero Prod.snd_zero Prod.mk_add_mk Prod.mk_mul_mk Prod.smul_mk Prod.mk_sub_mk Prod.neg_mk Prod.vadd_mk 

-- simp theorems for `Equiv`
attribute [ftrans_simp] Equiv.invFun_as_coe Equiv.symm_symm

-- simp theorems for `if _ then _ else _`
attribute [ftrans_simp] dite_eq_ite eq_self ite_true ite_false dite_true dite_false

-- simp theorems for `Sum`
attribute [ftrans_simp] Sum.inr.injEq Sum.inl.injEq

-- complex
attribute [ftrans_simp] Complex.conj_I
