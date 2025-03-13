import SciLean

open SciLean Scalar

set_default_scalar Float

instance {n:ℕ} : Inhabited (Fin n) := ⟨0, sorry_proof⟩

@[data_synth]
theorem SciLean.sum.arg_f.HasRevFDeriv_rule_scalar
    {K} [RCLike K]
    {W} [NormedAddCommGroup W] [AdjointSpace K W]
    {I : Type*} [IndexType I]
    (f : W → I → K) {f' : I → _} (hf : ∀ i, HasRevFDerivUpdate K (f · i) (f' i))  :
    HasRevFDeriv K
      (fun w => sum (f w))
      (fun w =>
        let' (s,dw) := IndexType.foldl (init := ((0 : K), (0:W)))
          (fun sdw (i : I) =>
            let' (s,dw) := sdw
            let' (x,df) := f' i w
            let s := s + x
            (s, df 1 dw))
        (s, fun dx => dx•dw)) := sorry_proof


def objective {n k d : ℕ} (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) :=
  ∑ i, (- IndexType.maxD (fun j => -‖points[i] - centroids[j]‖₂²) 0)

-- TODO: this version should be differentiable too!
-- def objective {n k d : ℕ} (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) :=
--   ∑ (i : Fin n), (- IndexType.maxD (fun (j : Fin k) => ∑ (l : Fin d), (-(points[i,l] - centroids[j,l])^2 : Float)) 0)


set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

def direction {n k d : ℕ} (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
  (let' ((_a,J),(_b,Hdiag)) :=
    ∂> (c:=centroids;VectorType.const 1),
      let' (y,df) := <∂ (objective points) c
      (y,df 1)
  VectorType.div J Hdiag)
rewrite_by
  unfold objective
  lsimp -zeta (disch:=unsafeAD) only [simp_core,↓revFDeriv_simproc,↓fwdFDeriv_simproc]
