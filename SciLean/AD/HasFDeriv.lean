module

public import SciLean.Tactic.DataSynth.Attr
public import SciLean.Tactic.DataSynth.Elab
public import SciLean.Tactic.DataSynth.DefDataSynth
public import SciLean.Analysis.AdjointSpace.Basic
public import SciLean.Analysis.AdjointSpace.Adjoint
public import SciLean.Analysis.Normed.IsContinuousLinearMap
public import SciLean.Analysis.Calculus.FDeriv
public import SciLean.Analysis.Normed.IsContinuousLinearMap

@[expose] public section
set_option linter.overlappingInstances false


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

/-- A map of two arguments that is jointly differentiable and continuous linear in each argument
separately has the sum of its two partial maps as its derivative. -/
theorem hasFDerivAt_of_isContinuousLinearMap_partials
    {f : E → G → F}
    (hf : Differentiable 𝕜 (fun p : E×G => f p.1 p.2))
    (hf₁ : ∀ y, IsContinuousLinearMap 𝕜 (fun x => f x y))
    (hf₂ : ∀ x, IsContinuousLinearMap 𝕜 (fun y => f x y))
    (p : E×G) :
    HasFDerivAt (fun q : E×G => f q.1 q.2)
      (ContinuousLinearMap.mk' 𝕜 (fun dq : E×G => f dq.1 p.2 + f p.1 dq.2) (by fun_prop)) p := by
  have hF : HasFDerivAt (fun q : E×G => f q.1 q.2) (fderiv 𝕜 (fun q : E×G => f q.1 q.2) p) p :=
    (hf p).hasFDerivAt
  set L := fderiv 𝕜 (fun q : E×G => f q.1 q.2) p with hL
  have h₁ : HasFDerivAt (fun x : E => f x p.2)
      (L.comp ((ContinuousLinearMap.id 𝕜 E).prod 0)) p.1 :=
    HasFDerivAt.comp (𝕜:=𝕜) p.1 (g := fun q : E×G => f q.1 q.2) (f := fun x : E => (x, p.2))
      (by simpa using hF) ((hasFDerivAt_id (𝕜:=𝕜) p.1).prodMk (hasFDerivAt_const (𝕜:=𝕜) p.2 p.1))
  have h₁' : HasFDerivAt (fun x : E => f x p.2)
      (ContinuousLinearMap.mk' 𝕜 (fun x => f x p.2) (hf₁ p.2)) p.1 :=
    (ContinuousLinearMap.mk' 𝕜 (fun x => f x p.2) (hf₁ p.2)).hasFDerivAt
  have e₁ : ∀ dx : E, L (dx, 0) = f dx p.2 := fun dx =>
    congrFun (congrArg DFunLike.coe (h₁.unique h₁')) dx
  have h₂ : HasFDerivAt (fun y : G => f p.1 y)
      (L.comp ((0 : G →L[𝕜] E).prod (ContinuousLinearMap.id 𝕜 G))) p.2 :=
    HasFDerivAt.comp (𝕜:=𝕜) p.2 (g := fun q : E×G => f q.1 q.2) (f := fun y : G => (p.1, y))
      (by simpa using hF) ((hasFDerivAt_const (𝕜:=𝕜) p.1 p.2).prodMk (hasFDerivAt_id (𝕜:=𝕜) p.2))
  have h₂' : HasFDerivAt (fun y : G => f p.1 y)
      (ContinuousLinearMap.mk' 𝕜 (fun y => f p.1 y) (hf₂ p.1)) p.2 :=
    (ContinuousLinearMap.mk' 𝕜 (fun y => f p.1 y) (hf₂ p.1)).hasFDerivAt
  have e₂ : ∀ dy : G, L (0, dy) = f p.1 dy := fun dy =>
    congrFun (congrArg DFunLike.coe (h₂.unique h₂')) dy
  have hLe : (ContinuousLinearMap.mk' 𝕜 (fun dq : E×G => f dq.1 p.2 + f p.1 dq.2) (by fun_prop))
      = L := by
    refine ContinuousLinearMap.ext fun dq => ?_
    show f dq.1 p.2 + f p.1 dq.2 = L dq
    rw [← e₁ dq.1, ← e₂ dq.2, ← L.map_add]
    congr 1
    simp
  rw [hLe]
  exact hF

theorem hasFDerivAt_from_fderiv
    {f : E → F} {x₀ : E}
    {f'} (deriv : f' = fderiv 𝕜 f x₀)
    (diff : Differentiable 𝕜 f := by fun_prop) :
    HasFDerivAt f f' x₀ := by
  rw [deriv]; exact (diff x₀).hasFDerivAt


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
  HasFDerivAt.comp x hf hg

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
      (fun dx =>L[K] n*x^(n-1)*dx) x := by
  refine hasFDerivAt_from_hasFDerivAt (hasDerivAt_pow n x).hasFDerivAt ?_
  refine ContinuousLinearMap.ext fun dx => ?_
  simp [mul_comm]

-- #check Scalar.pow
-- @[data_synth]
-- theorem HPow.hPow.arg_a0.HasFDerivAt_simple_rule (xy : K×K) (h : xy.1 ∈ Scalar.slitPlane) :
--     HasFDerivAt (fun xy : K×K => (Scalar.pow (R:=R) xy.1 xy.2))
--       (fun dx =>L[K] (xy.2)*xy.1^(xy.2-1)*dx) xy := sorry_proof

open ComplexConjugate in
@[data_synth]
theorem HDiv.hDiv.arg_a0a1.HasFDerivAt_simp_rule (xy : K×K) (h : xy.2 ≠ 0) :
    HasFDerivAt (fun x : K×K => x.1 / x.2)
      (fun dx =>L[K] (xy.2 * dx.1 - xy.1 * dx.2) / (xy.2 ^ 2)) xy := by
  have hc : HasFDerivAt (fun x : K×K => x.1) (ContinuousLinearMap.fst K K K) xy :=
    (hasFDerivAt_id (𝕜:=K) xy).fst
  have hd : HasFDerivAt (fun x : K×K => x.2) (ContinuousLinearMap.snd K K K) xy :=
    (hasFDerivAt_id (𝕜:=K) xy).snd
  have hinv : HasFDerivAt (fun x : K×K => x.2⁻¹)
      ((ContinuousLinearMap.toSpanSingleton K (-(xy.2^2)⁻¹)).comp
        (ContinuousLinearMap.snd K K K)) xy :=
    HasFDerivAt.comp (𝕜:=K) xy ((hasDerivAt_inv h).hasFDerivAt) hd
  simp only [div_eq_mul_inv]
  refine hasFDerivAt_from_hasFDerivAt (HasFDerivAt.fun_mul hc hinv) ?_
  refine ContinuousLinearMap.ext fun dx => ?_
  simp [ContinuousLinearMap.toSpanSingleton_apply]
  field_simp
  ring

@[data_synth]
theorem Inv.inv.arg_a0.HasFDerivAt_simp_rule (x : K) (h : x ≠ 0) :
    HasFDerivAt (fun x : K => x⁻¹)
      (fun dx =>L[K] -dx / x^2) x := by
  refine hasFDerivAt_from_hasFDerivAt (hasDerivAt_inv h).hasFDerivAt ?_
  refine ContinuousLinearMap.ext fun dx => ?_
  simp [div_eq_mul_inv]

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
      (fun dx =>L[R] ⟪dx.1,xy.2⟫[K] + ⟪xy.1,dx.2⟫[K]) xy := by
  -- the inner product is a bounded bilinear map, hence the remainder `⟪dx.1,dx.2⟫` is `o(‖dx‖)`
  obtain ⟨C, hC, hCle⟩ := AdjointSpace.exists_norm_inner_le (𝕜:=K) (E:=X)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hrem : (fun h : X×X => ⟪(xy+h).1, (xy+h).2⟫[K] - ⟪xy.1,xy.2⟫[K]
        - ((fun dx =>L[R] ⟪dx.1,xy.2⟫[K] + ⟪xy.1,dx.2⟫[K]) h))
      = fun h : X×X => ⟪h.1,h.2⟫[K] := by
    funext h
    simp only [ContinuousLinearMap.mk'_eval, Prod.fst_add, Prod.snd_add,
      AdjointSpace.inner_add_left, AdjointSpace.inner_add_right]
    abel
  rw [hrem, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [Metric.ball_mem_nhds (0 : X×X) (by positivity : 0 < c/C)] with h hh
  have hh' : ‖h‖ < c/C := by simpa [dist_eq_norm] using hh
  have h1 : ‖h.1‖ ≤ ‖h‖ := le_max_left _ _
  have h2 : ‖h.2‖ ≤ ‖h‖ := le_max_right _ _
  calc ‖⟪h.1,h.2⟫[K]‖ ≤ C * (‖h.1‖ * ‖h.2‖) := hCle _ _
    _ ≤ C * (‖h‖ * ‖h‖) := by
        have := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left this hC.le
    _ ≤ c * ‖h‖ := by
        have : C * ‖h‖ ≤ c := by
          rw [← le_div_iff₀' hC]
          exact hh'.le
        nlinarith [norm_nonneg h]

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
      (fun dy =>L[K] ⟪x,dy⟫[K]) y :=
  hasFDerivAt_from_isContinuousLinearMap (by fun_prop)

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
  case simp =>
    ext u
    rfl

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
    ext u
    dsimp
    have hconj : (starRingEnd R) ⟪u, x⟫[R] = ⟪x, u⟫[R] := by
      simpa using (@AdjointSpace.conj_symm R X _ _ inferInstance x u)
    have hux : ⟪u, x⟫[R] = ⟪x, u⟫[R] := by
      simpa [conj_for_real_scalar] using hconj
    simp [two_mul, hux]
