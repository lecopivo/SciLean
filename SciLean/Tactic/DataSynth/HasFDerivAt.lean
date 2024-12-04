import SciLean.Analysis.Calculus.FDeriv
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.DataSynth.Elab

section Missing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f g : E → F} {f' g' : E →L[𝕜] F} {x : E} {s : Set E} {L : Filter E}

theorem HasFDerivAt.letE {g : F → E → G} {g'}
    (hf : HasFDerivAt f f' x)
    (hg : HasFDerivAt (fun yx : F×E => g yx.1 yx.2) g' (f x, x)) :
    HasFDerivAt
      (fun x => let y := f x; g y x)
      (g'.comp (f'.prod (.id 𝕜 E))) x := sorry_proof

end Missing

attribute [data_synth out f' in f] HasFDerivAt

attribute [data_synth]
  hasFDerivAt_id
  hasFDerivAt_const
  hasFDerivAt_apply
  hasFDerivAt_pi''
  -- HasFDerivAt.comp
  -- HasFDerivAt.letE

  HasFDerivAt.prod
  HasFDerivAt.fst
  HasFDerivAt.snd

  HasFDerivAt.add
  HasFDerivAt.sub
  HasFDerivAt.neg
  HasFDerivAt.mul
  HasFDerivAt.smul



variable {𝕜 : Type} [NontriviallyNormedField 𝕜] (x : 𝕜)

set_option profiler true in
set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
#check (HasFDerivAt (𝕜:=𝕜) (fun x : 𝕜 => x * x * x) _ x)
  rewrite_by
    data_synth +simp



set_option profiler true in
#check (HasFDerivAt (𝕜:=𝕜) (fun yx : 𝕜×𝕜 => yx.1 * yx.2* yx.2* yx.2* yx.2* yx.2* yx.2* yx.2* yx.2* yx.2* yx.2* yx.2* yx.2* yx.2) _ (x, x))
  rewrite_by
    data_synth +simp
