import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.DataSynth.Elab
import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.AdjointSpace.Adjoint
import SciLean.Analysis.Normed.IsContinuousLinearMap
import SciLean.Analysis.Calculus.FDeriv

import SciLean.Analysis.Calculus.FDeriv

open SciLean

attribute [data_synth out f' in f] HasFDerivAt

section LambdaTheorems
variable (𝕜 : Type*) {E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open ContinuousLinearMap

@[data_synth]
theorem hasFDerivAt_id' (x : E) : HasFDerivAt (fun x : E => x) (fun dx =>L[𝕜] dx) x :=
  hasFDerivAt_id x

theorem hasFDerivAt_comp {g : E → F} {f : F → G} {g' : E →L[𝕜] F} {f'  : F →L[𝕜] G} (x : E)
    (hg : HasFDerivAt g g' x) (hf : HasFDerivAt f f' (g x)) :
    HasFDerivAt (fun x => f (g x)) (fun dx =>L[𝕜] f' (g' dx)) x :=
  HasFDerivAtFilter.comp x hf hg hg.continuousAt

theorem hasFDerivAt_let {g : E → F} {f : F → E → G} {g' : E →L[𝕜] F} {f'  : F×E →L[𝕜] G} (x : E)
    (hg : HasFDerivAt g g' x) (hf : HasFDerivAt ↿f f' (g x,x)) :
    HasFDerivAt (fun x => let y := g x; f y x) (fun dx =>L[𝕜] f' (g' dx, dx)) x :=
  hasFDerivAt_comp 𝕜 x (hg.prod (hasFDerivAt_id x)) hf

set_option linter.unusedVariables false in
theorem hasFDerivAt_proj
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    (f : E → F) (g : E₁ → F) (p₁ : E → E₁) (p₂ : E → E₂) (q : E₁ → E₂ → E)
    (x : E) {g' : E₁ →L[𝕜] F} (hg : HasFDerivAt g g' (p₁ x))
    (hp₁ : IsContinuousLinearMap 𝕜 p₁ := by fun_prop) (hf : ∀ x, f x = g (p₁ x) := by simp) :
    HasFDerivAt f (fun dx : E =>L[𝕜] g' (p₁ dx)) x := by
  conv => enter[1,x]; rw[hf]
  have hp₁' := (fun x =>L[𝕜] p₁ x).hasFDerivAt (x:=x)
  simp at hp₁'
  exact hg.comp x hp₁'

-- add data_synth lambda_theorems
-- todo: this should be done automatically by @[data_synth] attribute the same way @[fun_prop] works
open Lean Meta SciLean in
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem (.const ``HasFDerivAt ``hasFDerivAt_const)
   Tactic.DataSynth.addLambdaTheorem (.comp ``HasFDerivAt ``hasFDerivAt_comp
      (← getConstArgId ``hasFDerivAt_comp `g) (← getConstArgId ``hasFDerivAt_comp `f)
      (← getConstArgId ``hasFDerivAt_comp `hg) (← getConstArgId ``hasFDerivAt_comp `hf))
   Tactic.DataSynth.addLambdaTheorem (.letE ``HasFDerivAt ``hasFDerivAt_let
      (← getConstArgId ``hasFDerivAt_let `g) (← getConstArgId ``hasFDerivAt_let `f)
      (← getConstArgId ``hasFDerivAt_let `hg) (← getConstArgId ``hasFDerivAt_let `hf))
   Tactic.DataSynth.addLambdaTheorem (.pi ``HasFDerivAt ``hasFDerivAt_pi''
      (← getConstArgId ``hasFDerivAt_pi'' `Φ) (← getConstArgId ``hasFDerivAt_pi'' `hφ))
   Tactic.DataSynth.addLambdaTheorem (.proj ``HasFDerivAt ``hasFDerivAt_proj
      (← getConstArgId ``hasFDerivAt_proj `f) (← getConstArgId ``hasFDerivAt_proj `g)
      (← getConstArgId ``hasFDerivAt_proj `p₁) (← getConstArgId ``hasFDerivAt_proj `p₂)
      (← getConstArgId ``hasFDerivAt_proj `q) (← getConstArgId ``hasFDerivAt_proj `hg))

end LambdaTheorems


variable
  {K : Type*} [NontriviallyNormedField K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace K Z]

@[data_synth]
theorem Prod.mk.arg_a0a1.HasFDerivAt_comp_rule (f : X → Y) (g : X → Z) (x : X) {f' g' : _ →L[K] _}
    (hf : HasFDerivAt f f' x)
    (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x => (f x, g x)) (fun dx =>L[K] (f' dx, g' dx)) x :=
  hf.prod hg

@[data_synth]
theorem Prod.fst.arg_self.HasFDerivAt_comp_rule (f : X → X×Y) (x : X)
    {f' : _ →L[K] _} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => (f x).1) (fun dx =>L[K] (f' dx).1) x := hf.fst

@[data_synth]
theorem Prod.snd.arg_self.HasFDerivAt_comp_rule (f : X → X×Y) (x : X)
    {f' : _ →L[K] _} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => (f x).2) (fun dx =>L[K] (f' dx).2) x := hf.snd

attribute [data_synth]
  HasFDerivAt.add HasFDerivAt.sub HasFDerivAt.neg
  HasFDerivAt.smul HasFDerivAt.mul

@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasFDerivAt_simple_rule (xy) :
    HasFDerivAt (fun x : X×X => x.1 + x.2)
      (fun dx =>L[K] (dx.1 + dx.2)) xy :=
  HasFDerivAt.add (hasFDerivAt_id (𝕜:=K) xy).fst (hasFDerivAt_id (𝕜:=K) xy).snd

@[data_synth]
theorem HSub.hSub.arg_a0a1.HasFDerivAt_simple_rule (xy) :
    HasFDerivAt (fun x : X×X => x.1 - x.2)
      (fun dx =>L[K] dx.1 - dx.2) xy :=
  HasFDerivAt.sub (hasFDerivAt_id (𝕜:=K) xy).fst (hasFDerivAt_id (𝕜:=K) xy).snd

@[data_synth]
theorem Neg.neg.arg_a0.HasFDerivAt_simple_rule (x) :
    HasFDerivAt (fun x : X => -x)
      (fun dx =>L[K] -dx) x :=
  HasFDerivAt.neg (hasFDerivAt_id (𝕜:=K) x)

@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasFDerivAt_simple_rule (rx : K×X) :
    HasFDerivAt (fun kx : K×X => kx.1 • kx.2)
      (fun dx =>L[K] rx.1 • dx.2 + dx.1 • rx.2) rx :=
  HasFDerivAt.smul (hasFDerivAt_id (𝕜:=K) rx).fst (hasFDerivAt_id (𝕜:=K) rx).snd

@[data_synth]
theorem HMul.hMul.arg_a0a1.HasFDerivAt_simple_rule (xy : K×K) :
    HasFDerivAt (fun x : K×K => x.1 * x.2)
      (fun dx =>L[K] xy.1 * dx.2 +  xy.2 * dx.1) xy :=
  HasFDerivAt.mul (hasFDerivAt_id (𝕜:=K) xy).fst (hasFDerivAt_id (𝕜:=K) xy).snd

set_option linter.unusedVariables false in
open ComplexConjugate in
@[data_synth]
theorem HDiv.hDiv.arg_a0a1.HasFDerivAt_simp_rule (xy : K×K) (h : xy.2 ≠ 0) :
    HasFDerivAt (fun x : K×K => x.1 / x.2)
      (fun dx =>L[K] (xy.2 * dx.1 - xy.1 * dx.2) / (xy.2 ^ 2)) xy :=
  sorry_proof

set_option linter.unusedVariables false in
@[data_synth]
theorem Inv.inv.arg_a0.HasFDerivAt_simp_rule (x : K) (h : x ≠ 0) :
    HasFDerivAt (fun x : K => x⁻¹)
      (fun dx =>L[K] -dx / x^2) x :=
  sorry_proof

@[data_synth]
theorem SciLean.sum.arg_f.HasFDerivAt_simp_rule {I : Type*} [IndexType I] (f : I → X) :
    HasFDerivAt (fun f => ∑ i, f i) (fun df =>L[K] ∑ i, df i) f :=
  (fun f : I → X =>L[K] ∑ i, f i).hasFDerivAt (x:=f)

@[data_synth]
theorem Finset.sum.arg_f.HasFDerivAt_simp_rule {I : Type*} (A : Finset I) [Fintype I] (f : I → X) :
    HasFDerivAt (fun f => A.sum f) (fun df =>L[K] A.sum df) f :=
  (fun f : I → X =>L[K] A.sum f).hasFDerivAt (x:=f)

@[data_synth]
theorem ite.arg_te.HasFDerivAt_simple_rule {c : Prop} [Decidable c] (te : X×X) :
    HasFDerivAt (fun te => if c then te.1 else te.2)
      (fun dte =>L[K] if c then dte.1 else dte.2) te := by
  by_cases h : c
  · simp[h]; exact (hasFDerivAt_id (𝕜:=K) te).fst
  · simp[h]; exact (hasFDerivAt_id (𝕜:=K) te).snd

@[data_synth]
theorem Inner.inner.arg_a0a1.HasFDerivAt_simple_rule
    {R K} [RealScalar R] [Scalar R K] [ScalarSMul R K]
    {X} [NormedAddCommGroup X] [AdjointSpace K X] [AdjointSpace R X] (xy) :
    HasFDerivAt (𝕜:=R) (fun x : X×X => ⟪x.1,x.2⟫[K])
      (fun dx =>L[R] ⟪dx.1,xy.2⟫[K] + ⟪xy.1,dx.2⟫[K]) xy := sorry_proof

@[data_synth]
theorem Inner.inner.arg_a1.HasFDerivAt_simple_rule
    {K} [RCLike K] {X} [NormedAddCommGroup X] [AdjointSpace K X] (x y) :
    HasFDerivAt (fun y : X => ⟪x,y⟫[K])
      (fun dy =>L[K] ⟪x,dy⟫[K]) y := sorry_proof
