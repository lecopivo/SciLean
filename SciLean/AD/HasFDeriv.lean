import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.DataSynth.Elab
import SciLean.Tactic.DataSynth.DefDataSynth
import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.AdjointSpace.Adjoint
import SciLean.Analysis.Normed.IsContinuousLinearMap
import SciLean.Analysis.Calculus.FDeriv
import SciLean.Analysis.Normed.IsContinuousLinearMap

open SciLean

attribute [data_synth out f' in f] HasFDerivAt

section LambdaTheorems
variable {𝕜 : Type*} {E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]


theorem fderiv_from_hasFDerivAt
    {f : E → F} {f' : E → _} (hf : ∀ x, HasFDerivAt f (f' x) x) :
    fderiv 𝕜 f = f' := by
  funext x; exact (hf x).fderiv

theorem fderivAt_from_hasFDerivAt
  {f : E → F} {x : E} {f'} (hf : HasFDerivAt f f' x) :
  fderiv 𝕜 f x = f' := hf.fderiv

simproc_decl fderiv_simproc (fderiv _ _) :=
  mkDataSynthSimproc `fderiv_simproc ``fderiv_from_hasFDerivAt

simproc_decl fderivAt_simproc  (fderiv _ _ _) :=
  mkDataSynthSimproc `fderivAt_simproc ``fderivAt_from_hasFDerivAt

theorem hasFDerivAt_from_hasFDerivAt {f : E → F} {f' f'' : E →L[𝕜] F} {x}
  (deriv : HasFDerivAt f f' x) (simp : f'' = f') : HasFDerivAt f f'' x := by rw[simp]; exact deriv

theorem hasFDerivAt_from_isContinuousLinearMap
    {f : E → F} {x₀ : E} (hf : IsContinuousLinearMap 𝕜 f) :
    HasFDerivAt f (fun x =>L[𝕜] f x) x₀ :=
  (fun x =>L[𝕜] f x).hasFDerivAt

set_option linter.unusedVariables false in
theorem hasFDerivAt_from_fderiv
    {f : E → F} {x₀ : E}
    {f'} (deriv : f' = fderiv 𝕜 f x₀)
    (diff : Differentiable 𝕜 f := by fun_prop) :
    HasFDerivAt f f' x₀ :=
  sorry_proof


open ContinuousLinearMap

@[data_synth]
theorem hasFDerivAt_id' (x : E) : HasFDerivAt (fun x : E => x) (fun dx =>L[𝕜] dx) x :=
  hasFDerivAt_id x

theorem hasFDerivAt_comp {g : E → F} {f : F → G} {g' : E →L[𝕜] F} {f'  : F →L[𝕜] G} (x : E)
    (hg : HasFDerivAt g g' x) (hf : HasFDerivAt f f' (g x)) :
    HasFDerivAt
      (fun x => f (g x))
      (fun dx =>L[𝕜]
        let dy := g' dx
        let dz := f' dy
        dz) x :=
  HasFDerivAtFilter.comp x hf hg hg.continuousAt

theorem hasFDerivAt_let {g : E → F} {f : F → E → G} {g' : E →L[𝕜] F} {f'  : F×E →L[𝕜] G} (x : E)
    (hg : HasFDerivAt g g' x) (hf : HasFDerivAt ↿f f' (g x,x)) :
    HasFDerivAt
      (fun x =>
        let y := g x
        f y x)
      (fun dx =>L[𝕜]
        let dy := g' dx
        let dz := f' (dy,dx)
        dz) x :=
  hasFDerivAt_comp x (hg.prodMk (hasFDerivAt_id x)) hf

set_option linter.unusedVariables false in
theorem hasFDerivAt_proj
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    (f : E → F) (g : E₁ → F) (p₁ : E → E₁) (p₂ : E → E₂) (q : E₁ → E₂ → E)
    (x : E) {g' : E₁ →L[𝕜] F} (hg : HasFDerivAt g g' (p₁ x))
    (hp₁ : IsContinuousLinearMap 𝕜 p₁ := by fun_prop) (hf : ∀ x, f x = g (p₁ x) := by simp) :
    HasFDerivAt f
      (fun dx : E =>L[𝕜]
        let dx₁ := p₁ dx
        let dy := g' dx₁
        dy) x := by
  conv => enter[1,x]; rw[hf]
  have hp₁' := (fun x =>L[𝕜] p₁ x).hasFDerivAt (x:=x)
  simp at hp₁'
  exact hg.comp x hp₁'

open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFDerivAt,``hasFDerivAt_const⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFDerivAt, ``hasFDerivAt_comp⟩, .comp
      (← getConstArgId ``hasFDerivAt_comp `g) (← getConstArgId ``hasFDerivAt_comp `f)
      (← getConstArgId ``hasFDerivAt_comp `hg) (← getConstArgId ``hasFDerivAt_comp `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFDerivAt,``hasFDerivAt_let⟩, .letE
      (← getConstArgId ``hasFDerivAt_let `g) (← getConstArgId ``hasFDerivAt_let `f)
      (← getConstArgId ``hasFDerivAt_let `hg) (← getConstArgId ``hasFDerivAt_let `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFDerivAt,``hasFDerivAt_pi''⟩, .pi
      (← getConstArgId ``hasFDerivAt_pi'' `Φ) (← getConstArgId ``hasFDerivAt_pi'' `hφ)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFDerivAt,``hasFDerivAt_proj⟩, .proj
      (← getConstArgId ``hasFDerivAt_proj `f) (← getConstArgId ``hasFDerivAt_proj `g)
      (← getConstArgId ``hasFDerivAt_proj `p₁) (← getConstArgId ``hasFDerivAt_proj `p₂)
      (← getConstArgId ``hasFDerivAt_proj `q) (← getConstArgId ``hasFDerivAt_proj `hg)⟩

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
    HasFDerivAt
      (fun x => (f x, g x))
      (fun dx =>L[K]
        let dy := f' dx
        let dz := g' dx
        (dy,dz)) x :=
  hf.prodMk hg

@[data_synth]
theorem Prod.fst.arg_self.HasFDerivAt_comp_rule (f : X → Y×Z) (x : X)
    {f' : _ →L[K] _} (hf : HasFDerivAt f f' x) :
    HasFDerivAt
      (fun x => (f x).1)
      (fun dx =>L[K]
        let dyz := f' dx
        let dy := dyz.1
        dy) x := hf.fst

@[data_synth]
theorem Prod.snd.arg_self.HasFDerivAt_comp_rule (f : X → Y×Z) (x : X)
    {f' : _ →L[K] _} (hf : HasFDerivAt f f' x) :
    HasFDerivAt
      (fun x => (f x).2)
      (fun dx =>L[K]
        let dyz := f' dx
        let dz := dyz.2
        dz) x := hf.snd

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

@[data_synth]
theorem HPow.hPow.arg_a0.HasFDerivAt_simple_rule_nat (x : K) (n : ℕ) :
    HasFDerivAt (fun x : K => x^n)
      (fun dx =>L[K] n*x^(n-1)*dx) x := sorry_proof

-- #check Scalar.pow
-- @[data_synth]
-- theorem HPow.hPow.arg_a0.HasFDerivAt_simple_rule (xy : K×K) (h : xy.1 ∈ Scalar.slitPlane) :
--     HasFDerivAt (fun xy : K×K => (Scalar.pow (R:=R) xy.1 xy.2))
--       (fun dx =>L[K] (xy.2)*xy.1^(xy.2-1)*dx) xy := sorry_proof

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

-- @[data_synth]
-- theorem SciLean.sum.arg_f.HasFDerivAt_simp_rule {I : Type*} [IndexType I] (f : I → X) :
--     HasFDerivAt (fun f => ∑ i, f i) (fun df =>L[K] ∑ i, df i) f :=
--   (fun f : I → X =>L[K] ∑ i, f i).hasFDerivAt (x:=f)

@[data_synth]
theorem Finset.sum.arg_f.HasFDerivAt_simp_rule {I : Type*} (A : Finset I) [Fintype I] (f : I → X) :
    HasFDerivAt (fun f => A.sum (fun i => f i)) (fun df =>L[K] A.sum (fun i => df i)) f :=
  (fun f : I → X =>L[K] A.sum f).hasFDerivAt (x:=f)

@[data_synth]
theorem SciLean.IndexType.sum.arg_f.HasFDerivAt_simp_rule
    {I : Type*} {nI} [IndexType I nI] [Fold I] (f : I → X) :
    HasFDerivAt (fun f => ∑ᴵ i, f i) (fun df =>L[K] ∑ᴵ i, df i) f :=
  (fun f : I → X =>L[K] ∑ᴵ i, f i).hasFDerivAt (x:=f)

@[data_synth]
theorem ite.arg_te.HasFDerivAt_simple_rule {c : Prop} [Decidable c] (te : X×X) :
    HasFDerivAt (fun te => if c then te.1 else te.2)
      (fun dte =>L[K] if c then dte.1 else dte.2) te := by
  by_cases h : c
  · simp[h]; exact (hasFDerivAt_id (𝕜:=K) te).fst
  · simp[h]; exact (hasFDerivAt_id (𝕜:=K) te).snd

@[data_synth]
theorem Inner.inner.arg_a0a1.HasFDerivAt_simple_rule
    {R K : Type*} [RealScalar R] [Scalar R K] [ScalarSMul R K]
    {X : Type*} [NormedAddCommGroup X] [AdjointSpace K X] [AdjointSpace R X] (xy) :
    HasFDerivAt (𝕜:=R) (fun x : X×X => ⟪x.1,x.2⟫[K])
      (fun dx =>L[R] ⟪dx.1,xy.2⟫[K] + ⟪xy.1,dx.2⟫[K]) xy := sorry_proof

@[data_synth]
theorem Inner.inner.arg_a0a1.HasFDerivAt_comp_rule
    {R K : Type*} [RealScalar R] [Scalar R K] [ScalarSMul R K]
    {W : Type*} [NormedAddCommGroup W] [AdjointSpace K W] [AdjointSpace R W]
    {X : Type*} [NormedAddCommGroup X] [AdjointSpace K X] [AdjointSpace R X]
    (f g : W → X) {f' g' : _ →L[R] _} (w) (hf : HasFDerivAt f f' w) (hg : HasFDerivAt g g' w) :
    HasFDerivAt (𝕜:=R) (fun w => ⟪f w, g w⟫[K])
      (fun dw =>L[R]
        let y := f w
        let dy := f' dw
        let z := g w
        let dz := g' dw
        ⟪dy,z⟫[K] + ⟪y,dz⟫[K]) w := by
  apply hasFDerivAt_from_hasFDerivAt
  case deriv => data_synth
  case simp => simp

@[data_synth]
theorem Inner.inner.arg_a1.HasFDerivAt_simple_rule
    {K X : Type*} [RCLike K] [NormedAddCommGroup X] [AdjointSpace K X] (x y) :
    HasFDerivAt (fun y : X => ⟪x,y⟫[K])
      (fun dy =>L[K] ⟪x,dy⟫[K]) y := sorry_proof

@[data_synth]
theorem Norm2.norm2.arg_a0.HasRevFDeriv_simple_rule_complex
  {R K : Type*} [RealScalar R] [Scalar R K] [ScalarSMul R K] [ScalarInner R K]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace K X] [AdjointSpace R X] (x) :
  HasFDerivAt
    (fun x : X => ‖x‖₂²[K])
    (fun dx =>L[R]
      let s₁ := ⟪dx,x⟫[K]
      let s₂ := ⟪x,dx⟫[K]
      s₁ + s₂) x := by
  simp +unfoldPartialApp only [Norm2.norm2]
  apply hasFDerivAt_from_hasFDerivAt
  case deriv => data_synth
  case simp => ext; dsimp

@[data_synth]
theorem Norm2.norm2.arg_a0.HasRevFDeriv_simple_rule_real
  {R : Type*} [RealScalar R]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X] [AdjointSpace R X] (x) :
  HasFDerivAt
    (fun x : X => ‖x‖₂²[R])
    (fun dx =>L[R]
      let s := ⟪x,dx⟫[R]
      2 * s) x := by
  simp +unfoldPartialApp only [Norm2.norm2]
  apply hasFDerivAt_from_hasFDerivAt
  case deriv => data_synth
  case simp =>
    ext; dsimp; (conv => rhs; enter[1]; rw[← AdjointSpace.conj_symm])
    simp only [conj_for_real_scalar]; ring
