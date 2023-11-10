import SciLean.Core
import SciLean.Data.DataArray
import SciLean.Data.Prod
import SciLean.Core.Meta.GenerateRevCDeriv'

import SciLean.Core.FloatAsReal


namespace SciLean

variable 
  {R : Type} [RealScalar R]

set_default_scalar R

variable {α β κ ι} [Index α] [Index κ] [Index β] [Index ι] [PlainDataType R]

#check AddAction

variable (κ) 
/-- 
  @param α indexing set of 
  -/
def convolutionLazy [Nonempty ι]
  (indexAction : κ → ι≃ι) 
  (weights : κ → R) (bias : ι → R) (x : ι → R) 
  (i : ι) : R := 
  ∑ j, weights j * x (indexAction j i) + bias i

variable {κ}

#generate_revCDeriv' convolutionLazy weights bias x | i
  prop_by unfold convolutionLazy; fprop
  trans_by 
    unfold convolutionLazy
    autodiff

--------------------------------------------------------------------------------
-- Index actions used for concrete convolutions --------------------------------
--------------------------------------------------------------------------------

-- This is probably broken when overflow happens
def idxShift (j : Idx m) : Idx n ≃ Idx n where
  toFun i := ⟨((n + i.1 + j.1) - (m >>> 1)) % n, sorry_proof⟩
  invFun i := ⟨((n + i.1 + (m >>> 1)) - j.1) % n, sorry_proof⟩
  left_inv := sorry_proof
  right_inv := sorry_proof

-- This is probably broken when overflow happens
def idx2Shift (j : Idx m × Idx m') : Idx n × Idx n' ≃ Idx n × Idx n' where
  toFun i := (idxShift j.1 i.1, idxShift j.2 i.2)
  invFun i := ((idxShift j.1).invFun i.1, (idxShift j.2).invFun i.2)
  left_inv := sorry_proof
  right_inv := sorry_proof


--------------------------------------------------------------------------------
-- Concrete convolutions over arrays -------------------------------------------
--------------------------------------------------------------------------------

def conv1d {m n} [Nonempty (Idx n)]
  (weights : R ^ Idx m) (bias : R ^ Idx n) (x : R ^ Idx n) 
  : R ^ Idx n := 
  introElem fun ij => convolutionLazy (Idx m) idxShift (fun i => weights[i]) (fun i => bias[i]) (fun i => x[i]) ij

#generate_revCDeriv' conv1d weights bias x
  prop_by unfold conv1d; fprop
  trans_by 
    unfold conv1d
    autodiff

def conv2d {m₁ m₂ n₁ n₂} [Nonempty (Idx n₁)] [Nonempty (Idx n₂)]
  (weights : R ^ (Idx m₁ × Idx m₂)) (bias : R ^ (Idx n₁ × Idx n₂)) (x : R ^ (Idx n₁ × Idx n₂)) 
  : R ^ (Idx n₁ × Idx n₂) := 
  introElem fun ij => convolutionLazy (Idx m₁ × Idx m₂) idx2Shift (fun i => weights[i]) (fun i => bias[i]) (fun i => x[i]) ij

#generate_revCDeriv' conv2d weights bias x
  prop_by unfold conv2d; fprop
  trans_by 
    unfold conv2d
    autodiff

-- #check fun (n : Nat) ≃> n +ᵥ n

variable (α κ) 


def x := ⊞ (i : Idx 10) => if i == 0 then 1.0 else 0.0
def w := ⊞ (i : Idx 3) => if i == 0 then 0.25 else if i == 1 then 0.5 else 0.25

instance : CoeDep (Array Float) a (Float ^ (Idx (no_index a.size.toUSize))) := sorry

#eval conv1d ⊞[0.25,0.5,0.25] 0 ⊞[0.0,0,0,1,1,1,1,0,0,0]

-- #eval conv1d ⊞[[0.0,0.125,0.0],[0.125,0.5,0.125],[0.0,0.125,0.0]] 0 ⊞[0.0,0,0,1,1,1,1,0,0,0]


def idxSplit2 (h : n % 2 = 0) : Idx n ≃ Idx (n/2) × Idx 2 where
  toFun i := (⟨i.1 >>>1,sorry_proof⟩, ⟨i.1 &&& 1, sorry_proof⟩)
  invFun i := ⟨i.1.1<<<1 + i.2.1, sorry_proof⟩
  left_inv := sorry_proof
  right_inv := sorry_proof

def idx2Split2 (h : n % 2 = 0 ∧ n' % 2 = 0) : Idx n × Idx n' ≃ (Idx (n/2) × Idx (n'/2)) × (Idx 2 × Idx 2) where
  toFun i := 
    let (a,b) := idxSplit2 h.1 i.1
    let (c,d) := idxSplit2 h.2 i.2
    ((a,c),(b,d))
  invFun i := 
    let a := (i.1.1, i.2.1)
    let b := (i.1.2, i.2.2)
    ((idxSplit2 h.1).invFun a, (idxSplit2 h.2).invFun b)
  left_inv := sorry_proof
  right_inv := sorry_proof


#exit
#eval ⊞ i : Idx 10 => i.toFloat

def convolution 
  (indexAction : κ → ι≃ι) (weights : DataArrayN R (α×κ)) 
  (bias : DataArrayN R (α×β×ι)) (x : DataArrayN R (β×ι)) 
  : DataArrayN R ((α×β)×ι) := 
  introElem fun ((a,b),i) => ∑ j, weights[(a,j)] * x[(b, indexAction j i)] + bias[(a,b,i)]

variable {α κ}

/-- **WARNING**: This works correctly only for `op := ·+·` right now -/
def pool [EnumType κ'] (split : ι ≃ κ×κ') (op : R → R → R) (x : DataArrayN R (β×ι)) : DataArrayN R (β×κ) := 
  introElem fun (b,j) => Id.run do
      let mut val := 0
      for j' in fullRange κ' do
        let i := split.invFun (j,j')
        val := op val x[(b,i)]
      val


variable [EnumType κ'] (split : ι ≃ κ×κ') (op : R → R → R) (x : DataArrayN R (β×ι))

example  (i : β×κ) (a : κ') 
  : SciLean.IsDifferentiableM (m:=Id) R fun (xy : (DataArrayN R (β×ι)) × R) => ForInStep.yield (xy.snd + xy.fst[(i.fst, split.symm (i.snd, a))]) := 
by 
  fprop


example (i : β × κ)
   : IsDifferentiable R fun (x : DataArrayN R (β × ι)) =>
      Id.run (forIn (fullRange κ') 0 fun (j' : κ') (r : R) => ForInStep.yield (r + x[(i.fst, split.symm (i.snd, j'))])) := by fprop



example : SciLean.Vec R (SciLean.DataArrayN R (β × ι)) := by infer_instance

example : IsDifferentiable R fun (x : DataArrayN R (β × ι)) => (0 : R) := by fprop

example 
  : IsDifferentiable R fun (x' :  DataArrayN R (β×ι)) (x : β×κ) =>
    Id.run (forIn (fullRange κ') 0 fun j' r => ForInStep.yield (r + x'[(x.fst, split.symm (x.snd, j'))])) :=
by
  fprop

example (i : β×κ)
  : ∂> (x:=x;dx),
    Id.run
      (forIn (SciLean.fullRange κ') 0 fun (j' : κ') (r : R) =>
        ForInStep.yield (r + x[(i.fst, split.symm (i.snd, j'))]))
    = 0 :=
by
  conv => 
    lhs
    autodiff
    autodiff
    simp only [fwdDerivM]
    autodiff

    -- rw[ForIn.forIn.arg_bf.fwdDerivM_rule _ _ _ (by fprop) (by fprop)]
    -- simp (discharger:=fprop) only [ForIn.forIn.arg_bf.fwdDerivM_rule]

    autodiff
  sorry    

set_option pp.funBinderTypes true

set_option trace.Meta.Tactic.fprop.step true in
set_option trace.Meta.Tactic.fprop.apply true in
set_option trace.Meta.Tactic.fprop.discharge true in
set_option trace.Meta.Tactic.fprop.unify true in
example 
  : IsDifferentiableM (m:=Id) R fun (val : R) => val := 
by
  apply Pure.pure.arg_a0.IsDifferentiableM_rule _ _ (by fprop)

@[simp ↓]
theorem asdf {K X Y} [IsROrC K] [Vec K X] [Vec K Y] (f : X → Y)
  : IsDifferentiableM (m:=Id) K f
    =
    IsDifferentiable K f := by rfl

set_option trace.Meta.Tactic.fprop.step true in
set_option trace.Meta.Tactic.fprop.apply true in
set_option trace.Meta.Tactic.fprop.discharge true in
set_option trace.Meta.Tactic.fprop.unify true in
example 
  : IsDifferentiableM (m:=Id) R fun (xy : DataArrayN R (β × ι) × R) =>
      let val := xy.snd;
      val :=
by
  fprop
  sorry

-- set_option pp.all true in
-- set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.rewrite true in
-- set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.ftrans.step true in
-- set_option trace.Meta.Tactic.fprop.discharge true in
set_option trace.Meta.Tactic.fprop.step true in
-- set_option trace.Meta.isDefEq.onFailure true in
#check 
  ∂> (x':=x), pool split (·+·) x'
  rewrite_by
    unfold pool
    conv => rw[SciLean.IntroElem.introElem.arg_f.fwdCDeriv_rule _ (by sorry)]
    autodiff
    autodiff
    -- dsimp
    -- -- autodiff
    -- conv => rw[SciLean.fwdCDeriv.pi_rule R _ sorry]
    -- ftrans only; let_normalize
    -- ftrans only 
    -- simp only [fwdDerivM]
    -- ftrans only


variable (f : X → Y) [Vec R X] [Vec R Y] (x dx : X)

/--
info: ∂ (x:=x;dx), f x : Y
-/
#guard_msgs in
#check 
  (∂> x:=x;dx, f x).snd
  rewrite_by let_normalize

  --; autodiff
    -- autodiff

    -- autodiff    


def relu (ε x : R) := x - Scalar.sqrt (x*x + ε)

def mnits_model := 
  fun (w₁,b₁,w₂,b₂,w₃,b₃) (x : DataArrayN R (Unit×(Idx 28 × Idx 28))) => 
    x |> convolution (Idx 32) (Idx 3 × Idx 3) idx2Shift w₁ b₁
      |> ArrayType.map (fun x : R => x - Scalar.abs x)
      |> pool (idx2Split2 (by native_decide)) (·+·)
      |> dense (Idx 100) w₂ b₂
      |> ArrayType.map (relu 1/10)
      |> dense (Idx 10) w₃ b₃
      |> ArrayType.map (relu 1/10)


