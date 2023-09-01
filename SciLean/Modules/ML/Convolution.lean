import SciLean.Core
import SciLean.Data.DataArray
import SciLean.Data.Prod

namespace SciLean

variable 
  {R : Type _} [RealScalar R]
  {K : Type _} [Scalar R K]

set_default_scalar R

variable {α β κ ι} [Index α] [Index κ] [Index β] [Index ι] [PlainDataType K] [PlainDataType R]

variable (κ)
def dense (weights : DataArrayN K (κ×ι)) (bias : DataArrayN K κ) (x : DataArrayN K ι) : DataArrayN K κ := 
  ⊞ j => ∑ i, weights[(j,i)] * x[i] + bias[j]
variable {κ}


section denseDerivTest
  variable (weights : DataArrayN R (κ×ι)) (bias : DataArrayN R κ) (x : DataArrayN R ι)

  #check 
    ∇ x, dense κ weights bias x
    rewrite_by
      unfold dense; symdiff

  #check 
    ∇ bias, dense κ weights bias x
    rewrite_by
      unfold dense; symdiff

  #check 
    ∇ weights, dense κ weights bias x
    rewrite_by
      unfold dense; symdiff

end denseDerivTest


-- This is probably broken when overflow happens
def idxAction (j : Idx m) : Idx n ≃ Idx n where
  toFun i := ⟨((n + i.1 + j.1) - (m >>> 1)) % n, sorry_proof⟩
  invFun i := ⟨((n + i.1 + (m >>> 1)) - j.1) % n, sorry_proof⟩
  left_inv := sorry_proof
  right_inv := sorry_proof

-- This is probably broken when overflow happens
def idx2Action (j : Idx m × Idx m') : Idx n × Idx n' ≃ Idx n × Idx n' where
  toFun i := (idxAction j.1 i.1, idxAction j.2 i.2)
  invFun i := ((idxAction j.1).invFun i.1, (idxAction j.2).invFun i.2)
  left_inv := sorry_proof
  right_inv := sorry_proof


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

#check  Function.invFun (fun (i : Idx 10) => idxSplit2 sorry i)
        rewrite_by ftrans


variable [Nonempty (Idx n)]
example : Function.invFun (fun (i : Idx n) => idxSplit2 sorry i)
          =
          fun j => (idxSplit2 sorry).invFun j := by ftrans

variable (α κ) 

def convolution 
  (indexAction : κ → ι≃ι) (weights : DataArrayN K (α×κ)) 
  (bias : DataArrayN K (α×β×ι)) (x : DataArrayN K (β×ι)) 
  : DataArrayN K ((α×β)×ι) := 
  introElem fun ((a,b),i) => ∑ j, weights[(a,j)] * x[(b, indexAction j • i)] + bias[(a,b,i)]

variable {α κ}

/-- **WARNING**: This works correctly only for `op := ·+·` right now -/
def pool [EnumType κ'] (split : ι ≃ κ×κ') (op : K → K → K) (x : DataArrayN K (β×ι)) : DataArrayN K (β×κ) := 
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
    x |> convolution (Idx 32) (Idx 3 × Idx 3) idx2Action w₁ b₁
      |> ArrayType.map (fun x : R => x - Scalar.abs x)
      |> pool (idx2Split2 (by native_decide)) (·+·)
      |> dense (Idx 100) w₂ b₂
      |> ArrayType.map (relu 1/10)
      |> dense (Idx 10) w₃ b₃
      |> ArrayType.map (relu 1/10)


