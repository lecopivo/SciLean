import SciLean
import SciLean.Core.Meta.GenerateRevCDeriv'

namespace SciLean.ML

variable 
  {K : Type} [RealScalar K]
  {W : Type} [Vec K W]

set_default_scalar K

variable {α β κ ι : Type} [Index κ] [Index ι] [PlainDataType K] [PlainDataType R]

variable (κ)
def denseLazy (weights : κ → ι → K) (bias : κ → K) (x : ι → K) (j : κ) : K := 
  ∑ i, weights j i * x i + bias j
variable {κ}

#generate_revCDeriv' denseLazy weights bias x | j
  prop_by unfold denseLazy; fprop
  trans_by 
    unfold denseLazy
    autodiff

variable (κ)
def dense (weights : DataArrayN K (κ×ι)) (bias : K^κ) (x : K^ι) : K^κ := 
  -- ⊞ j => ∑ i, weights[(j,i)] * x[i] + bias[j]
  ⊞ j => denseLazy κ (fun j i => weights[(j,i)]) (fun j => bias[j]) (fun i => x[i]) j
variable {κ}

#generate_revCDeriv' dense weights bias x
  prop_by unfold dense; fprop
  trans_by unfold dense; autodiff



#check Nat
#check Function.repeatIdx

-- @[simp, ftrans_simp]
-- theorem _root_.Function.repeatIdx_modify {ι} [EnumType ι]
--   (g : ι → α → α) 
--   : Function.repeatIdx (fun i f => Function.modify f i (g i))
--     =
--     fun f i => g i (f i) := sorry_proof


-- @[simp, ftrans_simp]
-- theorem _root_.Function.repeatIdx_add {ι} [EnumType ι] [Zero α] [Add α]
--   (f : ι → κ → α)
--   : Function.repeatIdx (fun i x j => x j + f i j)
--     =
--     fun (x : κ → α) j => x j + ∑ i, f i j := sorry_proof

-- @[simp, ftrans_simp]
-- theorem _root_.Function.repeatIdx_repeatIdx {ι κ} [EnumType ι] [EnumType κ]
--   (f : ι → κ → α → α)
--   : Function.repeatIdx (fun i x => (Function.repeatIdx fun j x => f i j x) x)
--     =
--     Function.repeatIdx (fun (ij : ι×κ) x => f ij.1 ij.2 x) := sorry_proof


section lazy
variable (weights : κ → ι → K) (bias : κ → K) (x : ι → K)

attribute [ftrans_simp] Pi.zero_apply

set_option trace.Meta.Tactic.simp.rewrite true in
#check 
  (revDeriv K fun (x : ι → K) => denseLazy κ weights bias x)
  rewrite_by
    unfold denseLazy
    ftrans; ftrans

set_option pp.funBinderTypes true in
#check 
  (revDeriv K fun (weights : κ → ι → K) => denseLazy κ weights bias x)
  rewrite_by
    unfold denseLazy
    ftrans; ftrans; simp
end lazy


section dense
variable (weights : DataArrayN K (κ×ι)) (bias : K ^ κ) (x : K ^ ι)

attribute [ftrans_simp] Pi.zero_apply


set_option trace.Meta.Tactic.simp.rewrite true in
#check 
  (revDeriv K fun (x : K ^ ι) => dense κ weights bias x)
  rewrite_by
    unfold dense; unfold denseLazy; dsimp
    ftrans; ftrans


set_option pp.funBinderTypes true in
#check 
  (revDeriv K fun (weights : DataArrayN K (κ×ι)) => dense κ weights bias x)
  rewrite_by
    unfold dense; unfold denseLazy
    ftrans; ftrans; simp


set_option pp.funBinderTypes true in
#check 
  (revDeriv K fun (wx : DataArrayN K (κ×ι) × K ^ ι) => dense κ wx.1 bias wx.2)
  rewrite_by
    unfold dense; unfold denseLazy
    ftrans; ftrans; simp


#check 
  (revDeriv K fun (wx : DataArrayN K (κ×ι) × K^κ × K^ι) => dense κ wx.1 wx.2.1 wx.2.2)
  rewrite_by
    unfold dense; unfold denseLazy
    ftrans


end dense


