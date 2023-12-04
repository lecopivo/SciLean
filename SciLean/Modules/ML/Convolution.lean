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

variable (κ) 
/-- 
  @param α indexing set of 
  -/
def convolutionLazy
  (indexAction : κ → ι≃ι) 
  (weights : κ → R) (bias : ι → R) (x : ι → R) 
  (i : ι) : R := 
  ∑ j, weights j * x (indexAction j i) + bias i

variable {κ}

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

def conv1d {m n}
  (weights : R^[m]) (bias : R^[n]) (x : R^[n]) 
  : R ^ Idx n := 
  introElem fun ij => convolutionLazy (Idx m) idxShift (fun i => weights[i]) (fun i => bias[i]) (fun i => x[i]) ij

#generate_revDeriv conv1d weights bias x
  prop_by unfold conv1d convolutionLazy; fprop
  trans_by unfold conv1d convolutionLazy; ftrans

def conv2d {m₁ m₂ n₁ n₂}
  (weights : R^[m₁,m₂]) (bias : R^[n₁,n₂]) (x : R^[n₁,n₂]) 
  : R^[n₁,n₂] := 
  introElem fun ij => convolutionLazy (Idx m₁ × Idx m₂) idx2Shift (fun i => weights[i]) (fun i => bias[i]) (fun i => x[i]) ij

#generate_revDeriv conv2d weights bias x
  prop_by unfold conv2d convolutionLazy; fprop
  trans_by unfold conv2d convolutionLazy; ftrans

-- #check fun (n : Nat) ≃> n +ᵥ n

variable (α κ)

variable {m n} (weights : R^[m]) (bias : R^[n]) (x : R^[n]) 

#check 
  (revDeriv R fun (x : R^[n]) => conv1d weights bias x)
  rewrite_by
    unfold conv1d; unfold convolutionLazy
    ftrans

variable {m₁ m₂ n₁ n₂} [Nonempty (Idx n₁)] [Nonempty (Idx n₂)]
  (weights : R^[m₁,m₂]) (bias : R^[n₁,n₂]) (x : R^[n₁,n₂])

#check 
  (revDeriv R fun (weights : R^[m₁,m₂]) => conv2d weights bias x)
  rewrite_by
    unfold conv2d; unfold convolutionLazy
    ftrans


#check 
  (revDeriv R fun (wbx : R^[m₁,m₂] × R^[n₁,n₂] × R^[n₁,n₂]) => conv2d wbx.1 wbx.2.1 wbx.2.2)
  rewrite_by
    unfold conv2d; unfold convolutionLazy
    ftrans

-- Int64[-dx/2,dx/2]
-- USize[n]

/- notation " USize[" n "]"  => Idx n
notation " Int64[" n ", " m "]" => Idx' n m
 -/
#eval show IO Unit from Id.run do
  let mut a := ⊞[0.0,0,0]
  for i in fullRange (Idx 3) do
    a[i] += 10.0 * i.toFloat + i.toFloat
  IO.println a

#check Float^[10,20,30]
#check Float^[[10,20],30]
#check Float^[[10,20],ι]
#check Float^[[κ,20],ι]
#check R^[ι,[-2:3]]
#check R^(Idx 10)
#check arrayTypeCont (Idx 10) R
#check R^ι

#check R^[ι]
def a := arrayTypeCont ι R
#check R^(ι×κ)

variable {ι κ: Type} [Index ι] [Index κ]

#check R^(ι×κ)

#check R^[[10,ι],[20,20]]
#check R^[10,10,[-3:3]]
#check R^[10, 10, [-1:1], [-5:5]]

#check Nat.succ^[5]


def conv2d' {n₁ n₂} (rx ry : Int64)
  (weights : R^[depth, [-rx:rx], [-ry:ry]]) (bias x  : R^[depth', n₁, n₂])
  : R^[[depth,depth'],[n₁,n₂]] := 
  introElem fun i' => 
    let ((d,d'),i) := i'
    ∑ j, weights[(d,j)] * x[(d',(j.1.val+ᵥi.1, j.2.val+ᵥi.2))] + bias[(d',i)]


#generate_revDeriv conv2d' weights bias x
  prop_by unfold conv2d'; fprop
  trans_by unfold conv2d'; ftrans


def idxSplit2 (h : n % 2 = 0) : Idx n ≃ Idx (n/2) × Idx 2 where
  toFun i := (⟨i.1 >>>1,sorry_proof⟩, ⟨i.1 &&& 1, sorry_proof⟩)
  invFun i := ⟨i.1.1<<<1 + i.2.1, sorry_proof⟩
  left_inv := sorry_proof
  right_inv := sorry_proof

def idx2Split2 (h : n % 2 = 0 ∧ n' % 2 = 0) : Idx n × Idx n' ≃ (Idx (n/2) × Idx (n'/2)) × (Idx 2 × Idx 2) where
  toFun i := 
    let (a,b) := idxSplit2 h.1 i.1
    let (c,d) := idxSplit2 h.2 i.2
    ((a,c), (b,d))
  invFun i := 
    let a := (i.1.1, i.2.1)
    let b := (i.1.2, i.2.2)
    ((idxSplit2 h.1).invFun a, (idxSplit2 h.2).invFun b)
  left_inv := sorry_proof
  right_inv := sorry_proof


#check Index

#exit
#eval ⊞ i : Idx 10 => i.toFloat

def convolution 
  (indexAction : κ → ι≃ι) 
  (weights : DataArrayN R (KernelIdx×ImageIdx)) 
  (bias : DataArrayN R (Idx×β×ι)) (x : DataArrayN R (×ImageIdx)) 
  : DataArrayN R ((α×β)×ι) := 
  introElem fun ((a,b),i) => ∑ j, weights[(a,j)] * x[(b, indexAction j i)] + bias[(a,b,i)]


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



