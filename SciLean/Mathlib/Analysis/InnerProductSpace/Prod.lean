import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

import SciLean.Util.SorryProof

namespace SciLean

open NNReal


def ProdLp (_ : ℝ) (α β : Type _) := α × β

abbrev ProdL2.mk {α β : Type _} (fst : α) (snd : β) : ProdLp 2 α β := (fst, snd)
abbrev ProdL2.fst {α β : Type _} (self : ProdLp 2 α β) : α := self.1
abbrev ProdL2.snd {α β : Type _} (self : ProdLp 2 α β) : β := self.2

macro α:term:35 " ×[" p:term "] " β:term:36 : term => `(ProdLp $p $α $β)
macro α:term:35 " ×₂ " β:term:36 : term => `(ProdLp 2 $α $β)

namespace ProdLp

variable {α b : Type _} {p : ℝ}


instance
  [AddGroup α] [AddGroup β] : AddGroup (α ×[p] β)
  := by unfold ProdLp; infer_instance

-- @[reducible]
-- instance [AddCommMonoid α] [AddCommMonoid β]
--   : AddCommMonoid (α ×[p] β)
--   := by unfold ProdLp; infer_instance

instance
  [AddCommGroup α] [AddCommGroup β] : AddCommGroup (α ×[p] β)
  := by unfold ProdLp; infer_instance

instance [Semiring K] [AddCommGroup α] [Module K α] [AddCommGroup β] [Module K β]
  : Module K (α ×[p] β) := by unfold ProdLp; infer_instance

noncomputable
instance instDist [Dist α] [Dist β] : Dist (α ×[p] β) where
  dist x y := ((dist x.1 y.1)^p + (dist x.2 y.2)^p)^(1/p)


-- Dist
-- PseudoMetricSpace
-- MetricSpace

-- Norm


noncomputable
instance instInner [RCLike K]
  [Inner K α] [Inner K β] : Inner K (α ×₂ β) where
  inner x y := Real.sqrt (RCLike.re (@inner K _ _ x.1 y.1 + @inner K _ _ x.2 y.2))

noncomputable
instance instNorm
  [Norm α] [Norm β] : Norm (α ×[p] β) where
  norm := fun (x,y) => (‖x‖^p + ‖y‖^p) ^ (1/p)


instance
  [UniformSpace α] [UniformSpace β]
  : UniformSpace (α ×[p] β) := by unfold ProdLp; infer_instance

instance
  [UniformSpace α] [CompleteSpace α]
  [UniformSpace β] [CompleteSpace β]
  : CompleteSpace (α ×[p] β) :=  by unfold ProdLp; infer_instance

noncomputable
instance [MetricSpace α] [MetricSpace β]
  : MetricSpace (α ×[p] β) where
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  edist := fun x y => ENNReal.ofReal (dist x y)
  edist_dist := sorry_proof
  toUniformSpace := by infer_instance
  uniformity_dist := sorry_proof
  toBornology := sorry_data
  cobounded_sets := sorry_proof
  eq_of_dist_eq_zero := sorry_proof

noncomputable
instance [NormedAddCommGroup α] [NormedAddCommGroup β]
  : NormedAddCommGroup (α ×[p] β) where
  dist_eq := sorry_proof

noncomputable
instance [RCLike K]
  [NormedAddCommGroup α] [InnerProductSpace K α]
  [NormedAddCommGroup β] [InnerProductSpace K β]
  : InnerProductSpace K (α ×₂ β) where
  norm_sq_eq_inner := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof
  norm_smul_le := sorry_proof



-- -- TODO: move to mathlib
-- instance
--   {K : Type _} [RCLike K]
--   {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
--   {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
--   : CompleteSpace (X × Y) := by infer_instance
