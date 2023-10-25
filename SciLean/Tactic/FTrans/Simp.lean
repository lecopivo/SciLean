import SciLean.Tactic.FTrans.Init
import Mathlib.Algebra.Group.Prod
import Mathlib.GroupTheory.GroupAction.Prod
import Mathlib.Algebra.SMulWithZero

namespace SciLean

attribute [ftrans_simp] Prod.mk_add_mk Prod.mk_mul_mk Prod.smul_mk Prod.mk_sub_mk Prod.neg_mk Prod.vadd_mk add_zero zero_add sub_zero zero_sub sub_self neg_zero mul_zero zero_mul zero_smul smul_zero smul_eq_mul smul_neg eq_self iff_self

attribute [ftrans_simp] Equiv.invFun_as_coe Equiv.symm_symm
