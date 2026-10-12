module

public import SciLean.Analysis.Calculus.RevFDeriv
public import SciLean.Analysis.Calculus.FwdFDeriv
public import SciLean.Analysis.Calculus.HasRevFDeriv
public import SciLean.Util.HoldLet

@[expose] public section


namespace SciLean

/-- Reduce `holdLet f x` to `f x` as in such cases `holdLet` is not serving its purpose anymore.

`holdLet` is designed to preserve let bindings like `let f := holdLet (fun x => x*x)` which
would get removed by `lsimp` or `autodiff` tactics without `holdLet`. Therefore let binding
`let z := holdLet (fun x => x*x) y` can be safely reduced to `let z := y*y`. -/
@[simp, simp_core]
theorem holdLet_apply {α β : Type*} (f : α → β) (x : α) : holdLet f x = f x := rfl


@[fun_prop]
theorem holdLet.arg_a.Differentiable_rule
  {𝕜} [RCLike 𝕜] {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
  IsContinuousLinearMap 𝕜 fun x : X => holdLet x := by simp[holdLet]; fun_prop

@[fun_prop]
theorem holdLet.arg_a1.Differentiable_rule
  {𝕜} [RCLike 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (f : X → Y) (hf : Differentiable 𝕜 f):
  Differentiable 𝕜 (holdLet f) := by simp[holdLet,hf]

@[fun_prop]
theorem holdLet.arg_a1.IsContinusousLinearMap_rule
  {𝕜} [RCLike 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (f : X → Y) (hf : IsContinuousLinearMap 𝕜 f):
  IsContinuousLinearMap 𝕜 (holdLet f) := by simp[holdLet,hf]

@[fun_trans]
theorem holdLet.arg_a1.fderiv_rule
  {𝕜} [RCLike 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (f : X → Y) :
  fderiv 𝕜 (holdLet f) = holdLet (fderiv 𝕜 f) := by rfl

@[data_synth]
theorem holdLet.arg_a1.HasFDerivAt_rule
  {𝕜} [RCLike 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (x : X) (f : X → Y) {f'} (hf : HasFDerivAt (𝕜:=𝕜) f f' x) :
  HasFDerivAt (𝕜:=𝕜) (holdLet f) (holdLet f') x := hf

@[fun_trans]
theorem holdLet.arg_a1.fwdFDeriv_rule
  {𝕜} [RCLike 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (f : X → Y) :
  fwdFDeriv 𝕜 (holdLet f) = holdLet (fwdFDeriv 𝕜 f) := by rfl

@[fun_trans]
theorem holdLet.arg_a1.revFDeriv_rule
  {𝕜} [RCLike 𝕜]
  {X} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  (f : X → Y) :
  revFDeriv 𝕜 (holdLet f) = holdLet (revFDeriv 𝕜 f) := by rfl

@[data_synth]
theorem holdLet.arg_a1.HasRevFDeriv_rule
    {𝕜} [RCLike 𝕜]
    {X} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    {Y} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    (f : X → Y) {f'} (hf : HasRevFDeriv 𝕜 f f'):
    HasRevFDeriv 𝕜 (holdLet f) (holdLet f') := hf

@[data_synth]
theorem holdLet.arg_a1.HasRevFDerivUpdate_rule
    {𝕜} [RCLike 𝕜]
    {X} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    {Y} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    (f : X → Y) {f'} (hf : HasRevFDerivUpdate 𝕜 f f'):
    HasRevFDerivUpdate 𝕜 (holdLet f) (holdLet f') := hf
