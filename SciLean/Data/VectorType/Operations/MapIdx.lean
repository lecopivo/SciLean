import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Data.VectorType.Operations.FromVec
import SciLean.Data.VectorType.Operations.Set
import SciLean.Data.IndexType.Fold

namespace SciLean

open VectorType ComplexConjugate

variable
  {X : Type*} {I : Type u} {R K :  Type*}
  {_ : RealScalar R} {_ : Scalar R K} {nI} {_ : IdxType I nI}
  [VectorType.Base X I K] [VectorType.Dense X] [IdxType.Fold' I]

theorem mapIdx_spec (f : I → K → K) (x : X) :
  mapIdx f x = fromVec (fun i => f i (toVec x i)) := sorry_proof

section NormedSpaces

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]
variable [InjectiveGetElem X I]

-- linear, continuous, differentiable
@[fun_prop]
theorem VectorType.mapIdx.arg_fx.IsContinusousLinearMap_rule
    (f : W → I → K → K) (x : W → X)
    (hf : ∀ i, IsContinuousLinearMap K (fun (w,x) => f w i x))
    (hx : IsContinuousLinearMap K x) :
    IsContinuousLinearMap K (fun w => mapIdx (f w) (x w)) := by

  simp only [mapIdx_spec]
  fun_prop

@[fun_prop]
theorem VectorType.mapIdx.arg_f.IsContinusousLinearMap_rule
    (f : W → I → K → K) (x : X)
    (hf : ∀ i x, IsContinuousLinearMap K (f · i x)) :
    IsContinuousLinearMap K (fun w => mapIdx (f w) x) := by

  simp only [mapIdx_spec]
  fun_prop

def_fun_prop mapIdx in x [InjectiveGetElem X n] (hf : ∀ i, IsContinuousLinearMap K (f i)) :
    IsContinuousLinearMap K by

  simp only [mapIdx_spec]
  fun_prop

@[fun_prop]
theorem VectorType.mapIdx.arg_f.Differentiable_rule
    (f : W → I → K → K) (x : W → X)
    (hf : ∀ i, Differentiable K (fun (w,x) => f w i x))
    (hx : Differentiable K x) :
    Differentiable K (fun w => mapIdx (f w) (x w)) := by

  simp only [mapIdx_spec]
  fun_prop

def_fun_prop mapIdx in x [InjectiveGetElem X n] (hf : ∀ i, Differentiable K (f i)) :
    Differentiable K by
  simp only [mapIdx_spec]
  fun_prop

set_option linter.unusedVariables false
-- fderiv
@[fun_trans]
theorem VectorType.mapIdx.arg_fx.fderiv_rule
    (f : W → I → K → K) (x : W → X)
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
theorem VectorType.mapIdx.arg_x.fderiv_rule
    (f : I → K → K) (x : W → X)
    (hf : ∀ i, Differentiable K (f i))
    (hx : Differentiable K x) :
    fderiv K (fun w => mapIdx f (x w))
    =
    fun w => fun dw =>L[K]
      let x₀  := x w
      let dx₀ := fderiv K x w dw
      mapIdx (fun i dxi => fderiv K (f i) (toVec x₀ i) (dxi)) dx₀ := by
  autodiff
  dsimp

set_option linter.unusedVariables false in
abbrev_data_synth mapIdx in x
    {f' : n → _} (hf : ∀ i x, HasFDerivAt (𝕜:=K) (f i) (f' i) x)
    [InjectiveGetElem X n] (x₀) : (HasFDerivAt (𝕜:=K) · · x₀) by
  have : ∀ i, Differentiable K (f i) := sorry_proof
  apply hasFDerivAt_from_fderiv
  case deriv => fun_trans only; rfl
  case diff => dsimp[autoParam]; fun_prop

@[fun_trans]
theorem VectorType.mapIdx.arg_fx.fwdFDeriv_rule
    (f : W → I → K → K) (x : W → X)
    (hf : ∀ i, Differentiable K (fun (w,x) => f w i x))
    (hx : Differentiable K x) :
    fwdFDeriv K (fun w => mapIdx (f w) (x w))
    =
    fun w dw =>
      let' (x,dx) := fwdFDeriv K x w dw
      let  f' := fun i xi dxi => fwdFDeriv K (fun (w,x) => f w i x) (w,xi) (dw,dxi)
      mapIdx₂ f' x dx := by
  unfold mapIdx;
  fun_trans
  sorry_proof


end NormedSpaces

section AdjointSpace

variable {W : Type*} [NormedAddCommGroup W] [AdjointSpace K W]
variable [InjectiveGetElem X I]

-- adjoint
set_option linter.unusedVariables false in
@[data_synth]
theorem VectorType.mapIdx.arg_fx.HasAdjoint_rule [IdxType.Fold' I]
    (f : W → I → K → K) (x : W → X)
    {f' : I → _} (hf : ∀ i, HasAdjointUpdate K (fun (w,x) => f w i x) (f' i))
    {x'} (hx : HasAdjointUpdate K x x') :
    HasAdjoint K
      (fun w => mapIdx (f w) (x w))
      (fun y =>
        let' (dw,dx) := IdxType.fold .full (init:=((0:W),(0:X))) fun i (dw,dx) =>
          let yi := y[i]
          let' (dw,dxi) := f' i yi (dw,(0:K))
          (dw,set dx i dxi)
        x' dx dw) := by
  sorry_proof

-- reverse AD
set_option linter.unusedVariables false in
@[data_synth]
theorem VectorType.mapIdx.arg_fx.HasAdjointUpdate_rule [IdxType.Fold' I]
    (f : W → I → K → K) (x : W → X)
    {f' : I → _} (hf : ∀ i, HasAdjointUpdate K (fun (w,x) => f w i x) (f' i))
    {x'} (hx : HasAdjointUpdate K x x') :
    HasAdjointUpdate K
      (fun w => mapIdx (f w) (x w))
      (fun y w' =>
        let' (dw,dx) := IdxType.fold .full (init:=(w',(0:X))) fun i (dw,dx) =>
          let yi := y[i]
          let' (dw,dxi) := f' i yi (dw,(0:K))
          (dw,set dx i dxi)
        x' dx dw) := by
  sorry_proof

set_option linter.unusedVariables false in
abbrev_data_synth mapIdx in x
    {f' : n → _} (hf : ∀ i, HasAdjoint K (fun x => f i x) (f' i))
    [InjectiveGetElem X n] :
    HasAdjoint K by
  conv => enter [3]; assign (fun y : X => mapIdx f' y)
  constructor
  case adjoint =>
    have := fun i => (hf i).adjoint
    simp_all [mapIdx_spec,vector_to_spec]
  case is_linear =>
    have := fun i => (hf i).isContinuousLinearMap
    -- fun_prop - some odd bug in `fun_prop`
    sorry_proof

set_option linter.unusedVariables false in
abbrev_data_synth mapIdx in x
    {f' : n → _} (hf : ∀ i, HasAdjoint K (fun x => f i x) (f' i))
    [InjectiveGetElem X n] :
    HasAdjointUpdate K by
  conv => enter [3]; assign (fun (y : X) x' => x' + mapIdx f' y)
  constructor
  case adjoint =>
    have h := fun i => (hf i).adjoint
    simp_all [mapIdx_spec,vector_to_spec,←Finset.sum_sub_distrib,mul_add]
  case is_linear =>
    have := fun i => (hf i).isContinuousLinearMap
    -- fun_prop - some odd bug in `fun_prop`
    sorry_proof


set_option linter.unusedVariables false in
@[data_synth]
theorem VectorType.mapIdx.arg_x.HasAdjoint_rule
    (f : I → K → K) (x : W → X)
    {f' : I → _} (hf : ∀ i, HasAdjoint K (fun x => f i x) (f' i))
    {x'} (hx : HasAdjoint K x x') :
    HasAdjoint K
      (fun w => mapIdx f (x w))
      (fun y =>
        let y := mapIdx f' y
        let w := x' y
        w) := by
  sorry_proof

set_option linter.unusedVariables false in
@[data_synth]
theorem VectorType.mapIdx.arg_x.HasAdjointUpdate_rule
    (f : I → K → K) (x : W → X)
    {f' : I → _} (hf : ∀ i, HasAdjoint K (fun x => f i x) (f' i))
    {x'} (hx : HasAdjointUpdate K x x') :
    HasAdjointUpdate K
      (fun w => mapIdx f (x w))
      (fun y w =>
        let y := mapIdx f' y
        let w := x' y w
        w) := by
  sorry_proof


set_option linter.unusedVariables false in
@[fun_trans]
theorem VectorType.mapIdx.arg_fx.HasRevFDeriv_rule [IdxType.Fold' I]
    (f : W → I → K → K) (x : W → X)
    {f' : I → _ } (hf : ∀ i, HasRevFDerivUpdate K (fun (w,x) => f w i x) (f' i))
    {x'} (hx : HasRevFDerivUpdate K x x') :
    HasRevFDeriv K
      (fun w => mapIdx (f w) (x w))
      (fun w =>
        let' (x₀,dx₀) := x' w
        let df' := fun (i : I) (xi : K) => (f' i (w,xi)).2
        let y := mapIdx (f w) x₀
        (y, fun dy =>
          let' (dw,dx) := IdxType.fold .full (init:=((0:W),(0:X))) fun i (dw,dx) =>
            let xi₀ := toVec x₀ i
            let dyi := toVec dy i
            let' (dw,dxi) := df' i xi₀ dyi (dw,0)
            (dw,set dx i dxi)
          dx₀ dx dw)) := by
  sorry_proof

set_option linter.unusedVariables false in
@[fun_trans]
theorem VectorType.mapIdx.arg_fx.HasRevFDerivUpdate_rule [IdxType.Fold' I]
    (f : W → I → K → K) (x : W → X)
    {f' : I → _ } (hf : ∀ i, HasRevFDerivUpdate K (fun (w,x) => f w i x) (f' i))
    {x'} (hx : HasRevFDerivUpdate K x x') :
    HasRevFDerivUpdate K
      (fun w => mapIdx (f w) (x w))
      (fun w =>
        let' (x₀,dx₀) := x' w
        let df' := fun (i : I) (xi : K) => (f' i (w,xi)).2
        let y := mapIdx (f w) x₀
        (y, fun dy dw =>
          let' (dw,dx) := IdxType.fold .full (init:=(dw,(0:X))) fun i (dw,dx) =>
            let' (dw,dxi) := df' i (toVec x₀ i) (toVec dy i) (dw,0)
            (dw,set dx i dxi)
          dx₀ dx dw)) := by
  sorry_proof

set_option linter.unusedVariables false in
@[fun_trans]
theorem VectorType.mapIdx.arg_f.HasRevFDeriv_rule [IdxType.Fold' I]
    (f : W → I → K → K) (x : W → X)
    {f' : I → _ } (hf : ∀ i, HasRevFDerivUpdate K (fun (w,x) => f w i x) (f' i))
    {x'} (hx : HasRevFDerivUpdate K x x') :
    HasRevFDeriv K
      (fun w => mapIdx (f w) (x w))
      (fun w =>
        let' (x₀,dx₀) := x' w
        let df' := fun (i : I) (xi : K) => (f' i (w,xi)).2
        let y := mapIdx (f w) x₀
        (y, fun dy =>
          let' (dw,dx) := IdxType.fold .full (init:=((0:W),(0:X))) fun i (dw,dx) =>
            let xi₀ := toVec x₀ i
            let dyi := toVec dy i
            let' (dw,dxi) := df' i xi₀ dyi (dw,0)
            (dw,set dx i dxi)
          dx₀ dx dw)) := by
  sorry_proof

set_option linter.unusedVariables false in
@[fun_trans]
theorem VectorType.mapIdx.arg_f.HasRevFDerivUpdate_rule [IdxType.Fold' I]
    (f : W → I → K → K) (x : W → X)
    {f' : I → _ } (hf : ∀ i, HasRevFDerivUpdate K (fun (w,x) => f w i x) (f' i))
    {x'} (hx : HasRevFDerivUpdate K x x') :
    HasRevFDerivUpdate K
      (fun w => mapIdx (f w) (x w))
      (fun w =>
        let' (x₀,dx₀) := x' w
        let df' := fun (i : I) (xi : K) => (f' i (w,xi)).2
        let y := mapIdx (f w) x₀
        (y, fun dy dw =>
          let' (dw,dx) := IdxType.fold .full (init:=(dw,(0:X))) fun i (dw,dx) =>
            let' (dw,dxi) := df' i (toVec x₀ i) (toVec dy i) (dw,0)
            (dw,set dx i dxi)
          dx₀ dx dw)) := by
  sorry_proof


set_option linter.unusedVariables false in
abbrev_data_synth mapIdx in x
    {f' : n → _} (hf : ∀ i, HasRevFDeriv K (fun x => f i x) (f' i))
    [InjectiveGetElem X n] :
    HasRevFDeriv K by
  conv => enter[3]; assign (fun (x : X) =>
     let y := mapIdx f x
     let df := fun i dxi => ((f' i) (toVec x i)).2 dxi
     (y, fun (dy : X) => mapIdx df dy))
  sorry_proof

set_option linter.unusedVariables false in
abbrev_data_synth mapIdx in x
    {f' : n → _} (hf : ∀ i, HasRevFDeriv K (fun x => f i x) (f' i))
    [InjectiveGetElem X n] :
    HasRevFDerivUpdate K by
  conv => enter[3]; assign (fun (x : X) =>
     let y := mapIdx f x
     let df := fun i dxi => ((f' i) (toVec x i)).2 dxi
     (y, fun (dy dx' : X) => mapIdx (fun i dxi' => dxi' + df i (toVec dy i)) dx'))
  sorry_proof
