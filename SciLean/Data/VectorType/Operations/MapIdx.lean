import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Data.VectorType.Operations.FromVec
import SciLean.Data.VectorType.Operations.Set
import SciLean.Data.IndexType.Fold

namespace SciLean

open VectorType ComplexConjugate

variable
  {X : Type*} {n : Type u} {R K :  Type*}
  {_ : RealScalar R} {_ : Scalar R K} {_ : IndexType n}
  [VectorType.Base X n K] [VectorType.Dense X]

theorem mapIdx_spec (f : n → K → K) (x : X) :
  mapIdx f x = fromVec (fun i => f i (toVec x i)) := sorry_proof

section NormedSpaces

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]
variable [VectorType.Lawful X]

-- linear, continuous, differentiable
@[fun_prop]
theorem VectorType.mapIdx.arg_fx.IsContinusousLinearMap_rule
    (f : W → n → K → K) (x : W → X)
    (hf : ∀ i, IsContinuousLinearMap K (fun (w,x) => f w i x))
    (hx : IsContinuousLinearMap K x) :
    IsContinuousLinearMap K (fun w => mapIdx (f w) (x w)) := by

  simp only [mapIdx_spec]
  fun_prop

@[fun_prop]
theorem VectorType.mapIdx.arg_f.IsContinusousLinearMap_rule
    (f : W → n → K → K) (x : X)
    (hf : ∀ i x, IsContinuousLinearMap K (f · i x)) :
    IsContinuousLinearMap K (fun w => mapIdx (f w) x) := by

  simp only [mapIdx_spec]
  fun_prop

def_fun_prop mapIdx in x [Lawful X] (hf : ∀ i, IsContinuousLinearMap K (f i)) :
    IsContinuousLinearMap K by

  simp only [mapIdx_spec]
  fun_prop

@[fun_prop]
theorem VectorType.mapIdx.arg_f.Differentiable_rule
    (f : W → n → K → K) (x : W → X)
    (hf : ∀ i, Differentiable K (fun (w,x) => f w i x))
    (hx : Differentiable K x) :
    Differentiable K (fun w => mapIdx (f w) (x w)) := by

  simp only [mapIdx_spec]
  fun_prop

def_fun_prop mapIdx in x [Lawful X] (hf : ∀ i, Differentiable K (f i)) :
    Differentiable K by
  simp only [mapIdx_spec]
  fun_prop


-- fderiv
@[fun_trans]
theorem VectorType.mapIdx.arg_f.fderiv_rule
    (f : W → n → K → K) (x : W → X)
    (hf : ∀ i, Differentiable K (fun (w,x) => f w i x))
    (hx : Differentiable K x) :
    fderiv K (fun w => mapIdx (f w) (x w))
    =
    fun w => fun dw =>L[K]
      let x₀  := x w
      let dx₀ := fderiv K x w dw
      mapIdx (fun i dxi => fderiv K (fun (w,x) => f w i x) (w,toVec x₀ i) (dw,dxi)) dx₀ := by
  unfold mapIdx; fun_trans;
  funext w; ext dw : 1;
  simp
  -- this is non trivial as we need some tools to reason about `fold` invariants
  sorry_proof

@[fun_trans]
theorem VectorType.mapIdx.arg_f.fwdFDeriv_rule
    (f : W → n → K → K) (x : W → X)
    (hf : ∀ i, Differentiable K (fun (w,x) => f w i x))
    (hx : Differentiable K x) :
    fwdFDeriv K (fun w => mapIdx (f w) (x w))
    =
    fun w dw =>
      let' (x,dx) := fwdFDeriv K x w dw
      let  f' := fun i xi dxi => fwdFDeriv K (fun (w,x) => f w i x) (w,xi) (dw,dxi)
      mapIdx₂ f' x dx := by
  unfold mapIdx; fun_trans; rfl


end NormedSpaces

section AdjointSpace

variable {W : Type*} [NormedAddCommGroup W] [AdjointSpace K W]
variable [VectorType.Lawful X]

-- adjoint
set_option linter.unusedVariables false in
@[data_synth]
theorem VectorType.mapIdx.arg_f.HasAdjoint_rule
    (f : W → n → K → K) (x : W → X)
    {f' : n → _} (hf : ∀ i, HasAdjointUpdate K (fun (w,x) => f w i x) (f' i))
    {x'} (hx : HasAdjointUpdate K x x') :
    HasAdjoint K
      (fun w => mapIdx (f w) (x w))
      (fun y =>
        let' (dw,dx) := IndexType.foldl (init:=((0:W),(0:X))) fun (dw,dx) i =>
          let yi := toVec y i
          let' (dw,dxi) := f' i yi (dw,0)
          (dw,set dx i dxi)
        x' dx dw) := by
  sorry_proof


-- reverse AD
set_option linter.unusedVariables false in
@[data_synth]
theorem VectorType.mapIdx.arg_f.HasAdjointUpdate_rule
    (f : W → n → K → K) (x : W → X)
    {f' : n → _} (hf : ∀ i, HasAdjointUpdate K (fun (w,x) => f w i x) (f' i))
    {x'} (hx : HasAdjointUpdate K x x') :
    HasAdjointUpdate K
      (fun w => mapIdx (f w) (x w))
      (fun y w' =>
        let' (dw,dx) := IndexType.foldl (init:=(w',(0:X))) fun (dw,dx) i =>
          let yi := toVec y i
          let' (dw,dxi) := f' i yi (dw,0)
          (dw,set dx i dxi)
        x' dx dw) := by
  sorry_proof

set_option linter.unusedVariables false in
@[fun_trans]
theorem VectorType.mapIdx.arg_f.HasRevFDeriv_rule
    (f : W → n → K → K) (x : W → X)
    {f' : n → _ } (hf : ∀ i, HasRevFDerivUpdate K (fun (w,x) => f w i x) (f' i))
    {x'} (hx : HasRevFDerivUpdate K x x') :
    HasRevFDeriv K
      (fun w => mapIdx (f w) (x w))
      (fun w =>
        let' (x₀,dx₀) := x' w
        let df' := fun (i : n) (xi : K) => (f' i (w,xi)).2
        let y := mapIdx (f w) x₀
        (y, fun dy =>
          let' (dw,dx) := IndexType.foldl (init:=((0:W),(0:X))) fun (dw,dx) i =>
            let xi₀ := toVec x₀ i
            let dyi := toVec dy i
            let' (dw,dxi) := df' i xi₀ dyi (dw,0)
            (dw,set dx i dxi)
          dx₀ dx dw)) := by
  sorry_proof

set_option linter.unusedVariables false in
@[fun_trans]
theorem VectorType.mapIdx.arg_f.HasRevFDerivUpdate_rule
    (f : W → n → K → K) (x : W → X)
    {f' : n → _ } (hf : ∀ i, HasRevFDerivUpdate K (fun (w,x) => f w i x) (f' i))
    {x'} (hx : HasRevFDerivUpdate K x x') :
    HasRevFDerivUpdate K
      (fun w => mapIdx (f w) (x w))
      (fun w =>
        let' (x₀,dx₀) := x' w
        let df' := fun (i : n) (xi : K) => (f' i (w,xi)).2
        let y := mapIdx (f w) x₀
        (y, fun dy dw =>
          let' (dw,dx) := IndexType.foldl (init:=(dw,(0:X))) fun (dw,dx) i =>
            let' (dw,dxi) := df' i (toVec x₀ i) (toVec dy i) (dw,0)
            (dw,set dx i dxi)
          dx₀ dx dw)) := by
  sorry_proof
