module

public import SciLean.Analysis.Calculus.HasRevFDeriv
public import SciLean.Analysis.Calculus.HasFwdFDeriv

@[expose] public section



namespace SciLean.IndexType

set_option linter.unusedVariables false

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {I : Type*} {nI : ℕ} [IndexType I nI] [Fold I]


@[fun_prop]
theorem fold.arg_initf.IsContinuousLinearMap_rule
    (r : IndexType.Range I)
    (init : W → X) (hinit : IsContinuousLinearMap 𝕜 init)
    (f : W → I → X → X) (hf : ∀ i , IsContinuousLinearMap 𝕜 (fun wx : W×X => f wx.1 i wx.2)) :
    IsContinuousLinearMap 𝕜 (fun w => fold r (init w) (f w)) := by sorry_proof


@[fun_prop]
theorem fold.arg_initf.Differentiable_rule
    (r : IndexType.Range I)
    (init : W → X) (hinit : Differentiable 𝕜 init)
    (f : W → I → X → X) (hf : ∀ i , Differentiable 𝕜 (fun wx : W×X => f wx.1 i wx.2)) :
    Differentiable 𝕜 (fun w => fold r (init w) (f w)) := by sorry_proof


@[data_synth]
theorem fold.arg_initf.HasFwdFDeriv_rule
    (r : IndexType.Range I)
    (init : W → X) {init'} (hinit : HasFwdFDeriv 𝕜 init init')
    (f : W → I → X → X) {f' : I → _} (hf : ∀ i , HasFwdFDeriv 𝕜 (fun wx : W×X => f wx.1 i wx.2) (f' i)) :
    HasFwdFDeriv 𝕜
      (fun w => fold r (init w) (f w))
      (fun w dw =>
        let' (x₀,dx₀) := init' w dw
        let' (x,dx) := fold r (x₀,dx₀) (fun i xdx =>
          let' (x,dx) := xdx
          let' (x,dx) := f' i (w,x) (dw,dx)
          (x,dx))
        (x,dx)) := by sorry_proof



variable
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace 𝕜 W]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]


@[data_synth]
theorem fold.arg_initf.HasRevFDeriv_rule [Fold I]
    (r : IndexType.Range I)
    (init : W → X) {init'} (hinit : HasRevFDerivUpdate 𝕜 init init')
    (f : W → I → X → X) {f' : I → _}
    (hf : ∀ i , HasRevFDerivUpdate 𝕜 (fun wx : W×X => f wx.1 i wx.2) (f' i)) :
    HasRevFDeriv 𝕜
      (fun w => fold r (init w) (f w))
      (fun w =>
        let' (x₀,dinit) := init' w
        let' (x,df) := fold r
          (init:=(x₀, fun dx dw => (dx,dw)))
          (fun i xdf =>
            let' (x,df) := xdf
            let' (y,dfᵢ) := f' i (w,x)
            (y, fun dx dw =>
              let' (dw,dx) := dfᵢ dx (dw,0)
              let' (dw,dx) := df dx dw
              (dw,dx)))
        (x, fun dx =>
          let' (dx,dw) := df dx 0
          let dw := dinit dx dw
          dw)) := by sorry_proof


@[data_synth]
theorem fold.arg_initf.HasRevFDerivUpdate_rule [Fold I]
    (r : IndexType.Range I)
    (init : W → X) {init'} (hinit : HasRevFDerivUpdate 𝕜 init init')
    (f : W → I → X → X) {f' : I → _}
    (hf : ∀ i , HasRevFDerivUpdate 𝕜 (fun wx : W×X => f wx.1 i wx.2) (f' i)) :
    HasRevFDerivUpdate 𝕜
      (fun w => fold r (init w) (f w))
      (fun w =>
        let' (x₀,dinit) := init' w
        let' (x,df) := fold r
          (init:=(x₀, fun dx dw => (dx,dw)))
          (fun i xdf =>
            let' (x,df) := xdf
            let' (y,dfᵢ) := f' i (w,x)
            (y, fun dx dw =>
              let' (dw,dx) := dfᵢ dx (dw,0)
              let' (dw,dx) := df dx dw
              (dw,dx)))
        (x, fun dx dw =>
          let' (dx,dw) := df dx dw
          let dw := dinit dx dw
          dw)) := by sorry_proof


theorem fold.arg_initf.HasRevFDeriv_scalar_rule [Fold I]
    (r : IndexType.Range I)
    (init : W → 𝕜) {init'} (hinit : HasRevFDerivUpdate 𝕜 init init')
    (f : W → I → 𝕜 → 𝕜) {f' : I → _}
    (hf : ∀ i , HasRevFDerivUpdate 𝕜 (fun wx : W×𝕜 => f wx.1 i wx.2) (f' i)) :
    HasRevFDeriv 𝕜
      (fun w => fold r (init w) (f w))
      (fun w =>
        let' (x₀,dinit) := init' w
        let' (x,dx,dw) := fold r
          (init:=(x₀, (1 : 𝕜), (0 : W)))
          (fun i xdxdw =>
            let' (x,dx,dw) := xdxdw;
            let' (x,df) := f' i (w,x)
            let dx' := (df 1 (0,0)).2
            -- this step is problematic as `dx'•dw` can be expensive if `W` is really large
            let dw := (df 1 (dx'•dw,0)).1
            let dx := dx*dx'
            (x, dx, dw))
        (x, fun dx' =>
          let dx := dx'*dx
          let dw := dx'•dw
          let dw := dinit dx dw
          dw)) := by sorry_proof



-- @[data_synth]
-- theorem fold.arg_initf.HasRevFDerivUpdate_rule [Fold I]
--     (r : IndexType.Range I)
--     (init : W → X) {init'} (hinit : HasRevFDerivUpdate 𝕜 init init')
--     (f : W → I → X → X) {f' : I → _}
--     (hf : ∀ i , HasRevFDerivUpdate 𝕜 (fun (w,x) => f w i x) (f' i)) :
--     HasRevFDerivUpdate 𝕜
--       (fun w => fold r (init w) (f w))
--       (fun w =>
--         let' (x₀,dinit) := init' w
--         let' (x,df) := fold r
--           (init:=(x₀, fun dx dw => (dx,dw)))
--           (fun i xdf =>
--             let' (x,df) := xdf
--             let' (y,dfᵢ) := f' i (w,x)
--             (y, fun dx dw =>
--               let' (dw,dx) := dfᵢ dx (dw,0)
--               let' (dw,dx) := df dx dw
--               (dw,dx)))
--         (x, fun dx dw =>
--           let' (dx,dw) := df dx dw
--           let dw := dinit dx dw
--           dw)) := by sorry_proof
