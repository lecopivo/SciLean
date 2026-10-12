module

public import SciLean.Analysis.Calculus.HasFDeriv
public import SciLean.Analysis.Calculus.FwdFDeriv
public import SciLean.Logic.Function.Constant
public import SciLean.Data.Nat

@[expose] public section


namespace SciLean


variable
  {K : Type*} [RCLike K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace K Z]

variable (K) in
@[data_synth out f' in f]
structure HasFwdFDeriv (f : X → Y) (f' : X → X → Y×Y) where
  val : ∀ x dx, (f' x dx).1 = f x
  deriv : ∃ df : X → X →L[K] Y,
      (∀ x, HasFDerivAt f (df x) x)
      ∧
      (∀ x dx, df x dx = (f' x dx).2)


----------------------------------------------------------------------------------------------------
-- API for constructing and deconstructing HasFwdFDeriv -----------------------------------
----------------------------------------------------------------------------------------------------

theorem hasFwdFDeriv_from_hasFDerivAt {f : X → Y}
    {df : X → X →L[K] Y} (deriv : ∀ x, HasFDerivAt (𝕜:=K) f (df x) x)
    {f' : X → X → Y×Y} (simp : ∀ x dx, f' x dx = (f x, df x dx)) :
    HasFwdFDeriv K f f' := by
  constructor
  case val =>
    simp[simp]
  case deriv =>
    apply Exists.intro df
    simp_all


-- @[to_data_synth_simproc] -- this attribute should automatically generate the following simproc
theorem fwdFDeriv_from_hasFwdFDeriv
  {f : X → Y} {f'} (hf : HasFwdFDeriv K f f') :
  fwdFDeriv K f = f' := by
  obtain ⟨val, df, hd, hd'⟩ := hf
  funext x dx
  simp only [fwdFDeriv, (hd x).fderiv]
  exact Prod.ext (val x dx).symm (hd' x dx)

simproc_decl fwdFDeriv_simproc (fwdFDeriv _ _) :=
  mkDataSynthSimproc `fwdFDeriv_simproc ``fwdFDeriv_from_hasFwdFDeriv

theorem hasFwdFDeriv_from_hasFwdFDeriv {f : X → Y}
    {f'} (deriv : HasFwdFDeriv K f f')
    {f''} (simp : f'' = f') :
    HasFwdFDeriv K f f'' := by rw[simp]; exact deriv



----------------------------------------------------------------------------------------------------
-- Lambda Theorems ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasFwdFDeriv

@[data_synth]
theorem id_rule : HasFwdFDeriv K (fun x : X => x) (λ x dx => (x, dx)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv =>
    intro x
    apply hasFDerivAt_id
  case simp => simp

theorem const_rule (c : Y) : HasFwdFDeriv K (fun _ : X => c) (λ _ _ => (c, 0)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv =>
    intro x
    apply hasFDerivAt_const
  case simp => simp

theorem comp_rule {g : X → Y} {f : Y → Z} {g' : X → X → Y×Y} {f' : Y → Y → Z×Z}
    (hf : HasFwdFDeriv K f f') (hg : HasFwdFDeriv K g g') :
    HasFwdFDeriv K
      (fun x => f (g x))
      (fun x dx =>
        let' (y, dy) := g' x dx;
        let' (z, dz) := f' y dy;
        (z, dz)) := by
  obtain ⟨hfv,df,hfd,hfd'⟩ := hf
  obtain ⟨hgv,dg,hgd,hgd'⟩ := hg
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv =>
    intro x
    exact (hfd (g x)).comp x (hgd x)
  case simp =>
    intros
    simp_all

theorem let_rule {g : X → Y} {f : Y → X → Z} {f' g'}
    (hg : HasFwdFDeriv K g g') (hf : HasFwdFDeriv K (fun yx : Y×X => f yx.1 yx.2) f') :
    HasFwdFDeriv K
      (fun x =>
        let y := g x
        f y x)
      (fun x dx =>
        let' (y, dy) := g' x dx
        let' (z, dz) := f' (y,x) (dy,dx)
        (z, dz)) := by
  obtain ⟨hfv,df,hfd,hfd'⟩ := hf
  obtain ⟨hgv,dg,hgd,hgd'⟩ := hg
  have hg' : HasFwdFDeriv K
    (fun x => (g x, x))
    (fun x dx => let' (y,dy) := g' x dx; ((y,x),(dy,dx))) := by
    apply hasFwdFDeriv_from_hasFDerivAt (df := fun x => (dg x).prod (ContinuousLinearMap.id K X))
    case deriv => intro x; exact (hgd x).prodMk (hasFDerivAt_id x)
    case simp => intros; simp_all
  obtain ⟨hgv',dg',hgd',hgd''⟩ := hg'
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv =>
    intro x
    exact (hfd (g x,x)).comp x (f:=fun x => (g x, x)) (hgd' x)
  case simp =>
    intros
    simp_all

@[data_synth]
theorem apply_rule {I} [IndexType I NI] [DecidableEq I] (i : I) :
    HasFwdFDeriv K (fun x : I → X => x i)
      (fun x dx =>
        (x i, dx i)) where
  val := by intros; rfl
  deriv := ⟨fun _ => ContinuousLinearMap.proj i,
            fun _ => (ContinuousLinearMap.proj (R:=K) (φ:=fun _ : I => X) i).hasFDerivAt,
            by intros; rfl⟩

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I} [IndexType I NI] [DecidableEq I] (i : I) :
    HasFwdFDeriv K (fun x : (I → X)×Y => x.1 i)
      (fun x dx =>
        (x.1 i, dx.1 i)) where
  val := by intros; rfl
  deriv :=
    let df := (ContinuousLinearMap.proj (R:=K) (φ:=fun _ : I => X) i).comp
                (ContinuousLinearMap.fst K (I → X) Y)
    ⟨fun _ => df, fun _ => df.hasFDerivAt, by intros; rfl⟩

theorem pi_rule {I : Type*} [IndexType I NI]
    {f : X → I → Y} {f' : I → _} (hf : ∀ i, HasFwdFDeriv K (f · i) (f' i)) :
    HasFwdFDeriv K f
      (fun x dx =>
        Equiv.arrowProdEquivProdArrow _ _ _ (fun i => f' i x dx)) := by
  have hval := fun i => (hf i).val
  choose df hd hd' using fun i => (hf i).deriv
  apply hasFwdFDeriv_from_hasFDerivAt (df := fun x => ContinuousLinearMap.pi (fun i => df i x))
  case deriv => intro x; exact hasFDerivAt_pi'.2 (fun i => hd i x)
  case simp => intros x dx; simp_all [Equiv.arrowProdEquivProdArrow]

set_option linter.unusedVariables false in
theorem proj_rule
    {X₁ : Type*} [NormedAddCommGroup X₁] [NormedSpace K X₁]
    {X₂ : Type*} [NormedAddCommGroup X₂] [NormedSpace K X₂]
    (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
    (hg : HasFwdFDeriv K g g') (hf : f = fun x => g (p₁ x) := by rfl)
    (hp₁ : IsContinuousLinearMap K p₁ := by fun_prop) /- (hdec : Decomposition p₁ p₂ q) -/ :
    HasFwdFDeriv K f
      (fun x dx =>
        let x₁ := p₁ x
        let dx₁ := p₁ dx
        let ydy := g' x₁ dx₁
        ydy) := by
  obtain ⟨hv,dg,hd,hd'⟩ := hg
  subst hf
  apply hasFwdFDeriv_from_hasFDerivAt
    (df := fun x => (dg (p₁ x)).comp (fun x =>L[K] p₁ x))
  case deriv => intro x; exact (hd (p₁ x)).comp x (fun x =>L[K] p₁ x).hasFDerivAt
  case simp => intros; exact Prod.ext (hv _ _) (hd' _ _).symm

set_option linter.unusedVariables false in
theorem let_skip_rule
    {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    {g : X → α} {f : α → X → Z} {f' : α → _}
    (hf : ∀ a, HasFwdFDeriv K (f a) (f' a))
    (hg : g.IsConstant) :
    HasFwdFDeriv K
      (fun x =>
        let y := g x
        f y x)
      (fun x dx =>
        let a := g x
        let' (z, dz) := f' a x dx
        (z, dz)) := by
  have h1 : (fun x => let y := g x; f y x) = (fun x => f (g 0) x) := by
    funext x; dsimp only; rw [hg x 0]
  have h2 : (fun x dx => let a := g x; let' (z, dz) := f' a x dx; (z, dz))
            = (fun x dx => f' (g 0) x dx) := by
    funext x dx; dsimp only; rw [hg x 0]
  rw [h1, h2]
  exact hf (g 0)


open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFwdFDeriv,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFwdFDeriv, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFwdFDeriv,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFwdFDeriv,``pi_rule⟩, .pi
      (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFwdFDeriv,``proj_rule⟩, .proj
      (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
      (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
      (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasFwdFDeriv,``let_skip_rule⟩, .letSkip
      (← getConstArgId ``let_skip_rule `g) (← getConstArgId ``let_skip_rule `f)
      (← getConstArgId ``let_skip_rule `hf)⟩

end HasFwdFDeriv
end SciLean
open SciLean


variable
  {K : Type*} [RCLike K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace K Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace K W]



@[data_synth]
theorem Prod.mk.arg_a0a1.HasFwdFDeriv_comp_rule
    {f : X → Y} {g : X → Z} {f' g'}
    (hf : HasFwdFDeriv K f f') (hg : HasFwdFDeriv K g g') :
    HasFwdFDeriv K
      (fun x => (f x, g x))
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        ((y, z), (dy, dz))) := by
  have ⟨_,_,_,_⟩ := hf
  have ⟨_,_,_,_⟩ := hg
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all


@[data_synth]
theorem Prod.fst.arg_self.HasFwdFDeriv_proj_rule :
    HasFwdFDeriv K
      (fun xy : X×Y => xy.1)
      (fun x dx => (x.1,dx.1)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all

@[data_synth]
theorem Prod.snd.arg_self.HasFwdFDeriv_proj_rule :
    HasFwdFDeriv K
      (fun xy : X×Y => xy.2)
      (fun x dx => (x.2,dx.2)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all

@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasFwdFDeriv_comp_rule
    {f : X → Y} {g : X → Y} {f' g'}
    (hf : HasFwdFDeriv K f f') (hg : HasFwdFDeriv K g g') :
    HasFwdFDeriv K
      (fun x => f x + g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y + z, dy + dz)) := by
  have ⟨_,_,_,_⟩ := hf
  have ⟨_,_,_,_⟩ := hg
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all

@[data_synth]
theorem HSub.hSub.arg_a0a1.HasFwdFDeriv_comp_rule
    {f : X → Y} {g : X → Y} {f' g'}
    (hf : HasFwdFDeriv K f f') (hg : HasFwdFDeriv K g g') :
    HasFwdFDeriv K
      (fun x => f x - g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y - z, dy - dz)) := by
  have ⟨_,_,_,_⟩ := hf
  have ⟨_,_,_,_⟩ := hg
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all

@[data_synth]
theorem Neg.neg.arg_a0.HasFwdFDeriv_comp_rule
    {f : X → Y} {f'}
    (hf : HasFwdFDeriv K f f') :
    HasFwdFDeriv K
      (fun x => - f x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        (- y, - dy)) := by
  have ⟨_,_,_,_⟩ := hf
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all

@[data_synth]
theorem Neg.neg.arg_a0.HasFwdFDeriv_simple_rule :
    HasFwdFDeriv K
      (fun x : X => - x)
      (fun x dx => (- x, - dx)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all

@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasFwdFDeriv_comp_rule
    {f : X → K} {g : X → Y} {f' g'}
    (hf : HasFwdFDeriv K f f') (hg : HasFwdFDeriv K g g') :
    HasFwdFDeriv K
      (fun x => f x • g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y • z, y • dz + dy • z)) := by
  have ⟨_,_,_,_⟩ := hf
  have ⟨_,_,_,_⟩ := hg
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all

@[data_synth]
theorem HMul.hMul.arg_a0a1.HasFwdFDeriv_comp_rule
    {f g : X → K} {f' g'}
    (hf : HasFwdFDeriv K f f') (hg : HasFwdFDeriv K g g') :
    HasFwdFDeriv K
      (fun x => f x * g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y * z, y * dz + z * dy)) := by
  have ⟨_,_,_,_⟩ := hf
  have ⟨_,_,_,_⟩ := hg
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all

@[data_synth]
theorem HDiv.hDiv.arg_a0a1.HasFwdFDeriv_comp_rule
    {f g : X → K} {f' g'}
    (hf : HasFwdFDeriv K f f') (hg : HasFwdFDeriv K g g')
    (hg' : ∀ x, g x ≠ 0) :
    HasFwdFDeriv K
      (fun x => f x / g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y / z, (z * dy - y * dz) / z^2)) := by
  have ⟨_,_,_,_⟩ := hf
  have ⟨_,_,_,_⟩ := hg
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth (disch:=aesop)
  case simp => intros; simp_all

@[data_synth]
theorem HDiv.hDiv.arg_a0.HasFwdFDeriv_comp_rule
    {f : X → K} (c : K) {f'}
    (hf : HasFwdFDeriv K f f')  :
    HasFwdFDeriv K
      (fun x => f x / c)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        (y / c, dy / c)) := by
  obtain ⟨hv,df,hd,hd'⟩ := hf
  apply hasFwdFDeriv_from_hasFDerivAt (df := fun x => c⁻¹ • df x)
  case deriv =>
    intro x
    simp only [div_eq_mul_inv, mul_comm _ c⁻¹]
    exact (hd x).const_mul c⁻¹
  case simp => intros; simp_all [div_eq_mul_inv, mul_comm]


@[data_synth]
theorem HInv.hInv.arg_a0.HasFwdFDeriv_comp_rule
    {f : X → K} {f'}
    (hf : HasFwdFDeriv K f f')
    (hf' : ∀ x, f x ≠ 0) :
    HasFwdFDeriv K
      (fun x => (f x)⁻¹)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let iy := y⁻¹
        (iy, - iy^2 • dy)) := by
  have ⟨_,_,_,_⟩ := hf
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth (disch:=aesop)
  case simp => intros; simp_all; ring

@[data_synth]
theorem HPow.hPow.arg_a0.HasFwdFDeriv_rule_nat
    {f : X → K} {f'}
    (hf : HasFwdFDeriv K f f') (n : ℕ) :
    HasFwdFDeriv K
      (fun x => (f x)^n)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        (y^n, n • y^(n-1) • dy)) := by
  have ⟨_,_,_,_⟩ := hf
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all; ring

set_option linter.unusedVariables false in
@[data_synth]
theorem SciLean.sum.arg_f.HasFwdFDeriv_rule
    {I : Type*} [IndexType I NI] [Fold I]
    {f : X → I → Y} {f' : I → _}
    (hf : ∀ i, HasFwdFDeriv K (f · i) (f' i)) :
    HasFwdFDeriv K
      (fun x => ∑ᴵ i, f x i)
      (fun x dx =>
        ∑ᴵ i,
          let ydy := f' i x dx
          ydy) := by
  simp only [IndexType.sum_eq_finset_sum]
  have hval := fun i => (hf i).val
  choose df hd hd' using fun i => (hf i).deriv
  apply hasFwdFDeriv_from_hasFDerivAt (df := fun x => ∑ i, df i x)
  case deriv => intro x; exact HasFDerivAt.fun_sum (fun i _ => hd i x)
  case simp =>
    intros x dx
    refine Prod.ext ?_ ?_ <;> simp_all [Prod.fst_sum, Prod.snd_sum]

@[data_synth]
theorem Finset.sum.arg_f.HasFwdFDeriv_rule
    {I : Type*} (A : Finset I)
    {f : X → I → Y} {f' : I → _}
    (hf : ∀ i, HasFwdFDeriv K (f · i) (f' i)) :
    HasFwdFDeriv K
      (fun x => ∑ i ∈ A, f x i)
      (fun x dx =>
        ∑ i ∈ A,
          let ydy := f' i x dx
          ydy) := by
  have hval := fun i => (hf i).val
  choose df hd hd' using fun i => (hf i).deriv
  apply hasFwdFDeriv_from_hasFDerivAt (df := fun x => ∑ i ∈ A, df i x)
  case deriv => intro x; exact HasFDerivAt.fun_sum (fun i _ => hd i x)
  case simp =>
    intros x dx
    refine Prod.ext ?_ ?_ <;> simp_all [Prod.fst_sum, Prod.snd_sum]

variable (K) in
structure DifferentiableCondition (c : W → Prop) (f g : W → X) : Prop where
  values : ∀ w ∈ frontier {w | c w}, f w = g w
  deriv  : ∀ w ∈ frontier {w | c w}, fderiv K f w = fderiv K g w

theorem differentiableCondition_const (c : Prop) (f g : W → X) :
    DifferentiableCondition K (fun _ => c) f g := by
  by_cases c <;> constructor <;> simp_all

/-- If two functions have the same derivative and the same value at a point then any function
that is pointwise equal to one of them has this derivative too. -/
theorem hasFDerivAt_ite {c : W → Prop} [dec : ∀ w, Decidable (c w)]
    {f g : W → X} {L : W →L[K] X} {w : W}
    (hf : HasFDerivAt f L w) (hg : HasFDerivAt g L w) (hfg : f w = g w) :
    HasFDerivAt (fun w => if c w then f w else g w) L w := by
  have hw : (if c w then f w else g w) = f w := by split <;> simp [hfg]
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hf hg ⊢
  intro ε hε
  filter_upwards [hf hε, hg hε] with w' h1 h2
  by_cases hc : c w'
  · simpa [hc, hw] using h1
  · simpa [hc, hw, hfg] using h2

set_option linter.unusedVariables false in
@[data_synth]
theorem ite.arg_te.HasFwdFDeriv_rule
    (c : W → Prop) (dec : ∀ w, Decidable (c w))
    (f g : W → X) (f' g') (hf : HasFwdFDeriv K f f') (hg : HasFwdFDeriv K g g')
    (hc : DifferentiableCondition K c f g := by apply differentiableCondition_const) :
    HasFwdFDeriv K
      (fun w => if c w then f w else g w)
      (fun w => if c w then f' w else g' w) := by
  obtain ⟨hfval, df, hdf, hdf'⟩ := hf
  obtain ⟨hgval, dg, hdg, hdg'⟩ := hg
  apply hasFwdFDeriv_from_hasFDerivAt (df := fun w => if c w then df w else dg w)
  case deriv =>
    intro w
    by_cases hi : w ∈ interior {w | c w}
    · have hcw : c w := interior_subset hi
      rw [if_pos hcw]
      refine (hdf w).congr_of_eventuallyEq ?_
      filter_upwards [mem_interior_iff_mem_nhds.mp hi] with w' hw'
      have hcw' : c w' := hw'
      simp [hcw']
    · by_cases hi' : w ∈ interior {w | c w}ᶜ
      · have hcw : ¬ c w := interior_subset hi'
        rw [if_neg hcw]
        refine (hdg w).congr_of_eventuallyEq ?_
        filter_upwards [mem_interior_iff_mem_nhds.mp hi'] with w' hw'
        have hcw' : ¬ c w' := hw'
        simp [hcw']
      · have hfr : w ∈ frontier {w | c w} := by
          refine ⟨?_, hi⟩
          have h : w ∉ (closure {w | c w})ᶜ := by rwa [← interior_compl]
          exact not_not.mp h
        have hL : df w = dg w := by
          have h1 : fderiv K f w = df w := (hdf w).fderiv
          have h2 : fderiv K g w = dg w := (hdg w).fderiv
          rw [← h1, ← h2, hc.deriv w hfr]
        by_cases hcw : c w
        · rw [if_pos hcw]
          exact hasFDerivAt_ite (hdf w) (hL ▸ hdg w) (hc.values w hfr)
        · rw [if_neg hcw]
          exact hasFDerivAt_ite (hL ▸ hdf w) (hdg w) (hc.values w hfr)
  case simp =>
    intro w dx
    by_cases hcw : c w
    · simp only [if_pos hcw]
      exact Prod.ext (hfval w dx) (hdf' w dx).symm
    · simp only [if_neg hcw]
      exact Prod.ext (hgval w dx) (hdg' w dx).symm


@[data_synth]
theorem dite.arg_te.HasFwdFDeriv_rule (c : Prop) (dec : Decidable c)
    (f : c → W → X) (g : ¬c → W → X) (f' : c → _) (g' : ¬c → _)
    (hf : ∀ h, HasFwdFDeriv K (f h) (f' h)) (hg : ∀ h, HasFwdFDeriv K (g h) (g' h)) :
    HasFwdFDeriv K
      (fun w => if h : c then f h w else g h w)
      (fun w dx => if h : c then f' h w dx else g' h w dx) := by
  by_cases h : c
  · simp [h]; apply (hf h)
  · simp [h]; apply (hg h)



section OverReals

variable {R K : Type*} [RealScalar R] [Scalar R K] [ScalarSMul R K] [ScalarInner R K]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace R W] [CompleteSpace W]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y] [AdjointSpace K Y]

open ComplexConjugate

@[data_synth]
theorem Inner.inner.arg_a0a1.HasFwdFDeriv_comp_rule
    (f g : X → Y) (f' g')
    (hf : HasFwdFDeriv R f f') (hg : HasFwdFDeriv R g g') :
    HasFwdFDeriv R
      (fun x => ⟪f x, g x⟫[K])
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (⟪y, z⟫[K], ⟪dy, z⟫[K] + ⟪y, dz⟫[K])) := by
  have ⟨_,_,_,_⟩ := hf
  have ⟨_,_,_,_⟩ := hg
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all


@[data_synth]
theorem Norm2.norm2.arg_a0.HasFwdFDeriv_simple_rule :
    HasFwdFDeriv R
      (fun x : Y => ‖x‖₂²[K])
      (fun x dx => (‖x‖₂²[K],
        let z := ⟪x,dx⟫[K]
        conj z + z)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all

@[data_synth high]
theorem Norm2.norm2.arg_a0.HasFwdFDeriv_simple_rule_real :
    HasFwdFDeriv R
      (fun x : Y => ‖x‖₂²[R])
      (fun x dx => (‖x‖₂²[R],
        2 * ⟪x,dx⟫[R])) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp_all


set_option linter.unusedVariables false in
@[data_synth]
theorem SciLean.norm₂.arg_x.HasFwdFDeriv_comp_rule
    (f : X → Y) {f'} (hf : HasFwdFDeriv R f f') (hf' : ∀ x, f x ≠ 0) :
    HasFwdFDeriv R (fun x => ‖f x‖₂[K]) (fun x dx =>
      let' (y, dy) := f' x dx;
      let yn := ‖y‖₂[K]
      (yn, ⟪y, dy⟫[K] / yn)) := by
  have ⟨_,_,_,_⟩ := hf
  sorry_proof

end OverReals


----------------------------------------------------------------------------------------------------
-- Recursion theorems ------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

theorem hasFwdFDeriv_nat_induction
   {X : ℕ → Type*} [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace K (X n)]
   {Y : ℕ → Type*} [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace K (Y n)]
   (n : ℕ) (f : (n : ℕ) → X n → Y n)
   {f₀' : X 0 → X 0 → Y 0 × Y 0}
   {F' : {m : ℕ} → (X m →  X m → Y m × Y m) → X (m+1) → X (m+1) → Y (m+1) × Y (m+1)}
   (zero : HasFwdFDeriv K (f 0) (fun x dx => f₀' x dx))
   (succ : ∀ n (fn' : X n → X n → Y n×Y n),
             (HasFwdFDeriv K (f n) fn')
             →
             HasFwdFDeriv K (f (n+1)) (fun x dx => F' fn' x dx)) :
   HasFwdFDeriv K (f n)
     (fun x dx => natRecFun (n:=n) (X:=fun n => X n) F' f₀' x dx) := by
  induction n
  case zero => exact zero
  case succ n hn => exact succ n _ hn


theorem hasFwdFDeriv_nat_induction'
   {X : ℕ → Type*} [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace K (X n)]
   {Y : ℕ → Type*} [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace K (Y n)]
   (n : ℕ) (f : α → (n : ℕ) → X n → Y n)
   {f₀' : α → X 0 → X 0 → Y 0 × Y 0}
   {F' : {m : ℕ} → α → (X m →  X m → Y m × Y m) → X (m+1) → X (m+1) → Y (m+1) × Y (m+1)}
   (zero : ∀ a, HasFwdFDeriv K (f a 0) (fun x dx => f₀' a x dx))
   (succ : ∀ n (fn' : α → X n → X n → Y n×Y n),
             (∀ a, HasFwdFDeriv K (f a n) (fn' a))
             →
             (∀ a, HasFwdFDeriv K (f a (n+1)) (fun x dx => F' a (fn' a) x dx))) :
   ∀ a, HasFwdFDeriv K (f a n)
     (fun x dx => natRecFun (n:=n) (X:=fun n => X n) (F' a) (f₀' a) x dx) := by
  induction n
  case zero => exact zero
  case succ n hn => exact succ n _ hn
