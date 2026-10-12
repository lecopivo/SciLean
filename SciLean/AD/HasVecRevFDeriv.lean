module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

public import SciLean.Algebra.TensorProduct.Prod
public import SciLean.Algebra.TensorProduct.Pi
public import SciLean.Analysis.Calculus.HasRevFDeriv

@[expose] public section


set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace SciLean

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace 𝕜 W]
  {WX : Type*} [NormedAddCommGroup WX] [AdjointSpace 𝕜 WX]
  {WY : Type*} [NormedAddCommGroup WY] [AdjointSpace 𝕜 WY]
  {WZ : Type*} [NormedAddCommGroup WZ] [AdjointSpace 𝕜 WZ]
  [TensorProductType 𝕜 W X WX]
  [TensorProductType 𝕜 W Y WY]
  [TensorProductType 𝕜 W Z WZ]

set_default_scalar 𝕜

variable (𝕜 W) in
@[data_synth out f' in f]
structure HasVecRevFDeriv (f : X → Y) (f' : X → Y × (W ⊗ Y → W ⊗ X)) where
  val : ∀ x, (f' x).1 = f x
  deriv :
      ∃ df : X → X →L[𝕜] Y,
      (∀ x, HasFDerivAt f (df x) x)
      ∧
      ∃ df' : X → Y → X,
      (∀ x, HasAdjoint 𝕜 (df x) (df' x))
      ∧
      (∀ x (dy : Y) (w : W), w ⊗ (df' x dy) = (f' x).2 (w ⊗ dy))
  -- I think linearity is necessary requirement as we define `f'` only on inputs of the form
  -- `dx ⊗ w` which needs to be extended by linearity to all elements of `X ⊗ W`
  linear : ∀ x, IsContinuousLinearMap 𝕜 (f' x).2

variable (𝕜 W) in
@[data_synth out f' in f]
structure HasVecRevFDerivUpdate (f : X → Y) (f' : X → Y × (W ⊗ Y → W ⊗ X → W ⊗ X)) where
  val : ∀ x, (f' x).1 = f x
  deriv : HasVecRevFDeriv 𝕜 W f (fun x => let' (y,df') := f' x; (y, fun dy => df' dy 0))
  add_dx : ∀ x dy dx, (f' x).2 dy dx = dx + (f' x).2 dy 0


open Classical in
variable (𝕜 W) in
noncomputable
def vecRevFDeriv (f : X → Y) (x : X) : (Y × (W ⊗ Y → W ⊗ X)) :=
  if h : ∃ f', HasVecRevFDeriv 𝕜 W f f' then
    choose h x
  else
    (0,0)


set_option linter.unusedVariables false in
theorem vecRevFDeriv_from_hasVecRevFDeriv
    {f : X → Y} {f'} (hf : HasVecRevFDeriv 𝕜 W f f') :
    vecRevFDeriv 𝕜 W f = f' := by
  sorry_proof

simproc_decl vecRevFDeriv_simproc (vecRevFDeriv _ _ _) :=
  mkDataSynthSimproc `vecRevFDeriv_simproc ``vecRevFDeriv_from_hasVecRevFDeriv


----------------------------------------------------------------------------------------------------
-- API for constructing and deconstructing HasFwdFDeriv -----------------------------------
----------------------------------------------------------------------------------------------------

-- theorem hasFwdFDeriv_from_hasFDerivAt {f : X → Y}
--     {df : X → X →L[K] Y} (deriv : ∀ x, HasFDerivAt (𝕜:=K) f (df x) x)
--     {f' : X → X → Y×Y} (simp : ∀ x dx, f' x dx = (f x, df x dx)) :
--     HasFwdFDeriv K f f' := by
--   constructor
--   case val =>
--     simp[simp]
--   case deriv =>
--     apply Exists.intro df
--     simp_all


-- set_option linter.unusedVariables false in
-- -- @[to_data_synth_simproc] -- this attribute should automatically generate the following simproc
-- theorem fwdFDeriv_from_hasFwdFDeriv
--   {f : X → Y} {f'} (hf : HasFwdFDeriv K f f') :
--   fwdFDeriv K f = f' := sorry_proof

-- simproc_decl fwdFDeriv_simproc (fwdFDeriv _ _) :=
--   mkDataSynthSimproc `fwdFDeriv_simproc ``fwdFDeriv_from_hasFwdFDeriv

----------------------------------------------------------------------------------------------------
-- Lambda Theorems ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasVecRevFDeriv

@[data_synth]
theorem id_rule : HasVecRevFDeriv 𝕜 W (fun x : X => x) (λ x => (x, fun dx => dx)) := by
  sorry_proof

theorem const_rule (c : Y) : HasVecRevFDeriv 𝕜 W (fun _ : X => c) (λ _ => (c, fun dy => 0)) := by
  sorry_proof

theorem comp_rule {g : X → Y} {f : Y → Z} {g' f'}
    (hf : HasVecRevFDeriv 𝕜 W f f') (hg : HasVecRevFDeriv 𝕜 W g g') :
    HasVecRevFDeriv 𝕜 W
      (fun x => f (g x))
      (fun x =>
        let' (y, dg') := g' x
        let' (z, df') := f' y
        (z, fun dz =>
          let dy := df' dz
          let dx := dg' dy
          dx)) := by
  sorry_proof

theorem let_rule {g : X → Y} {f : Y → X → Z} {f' g'}
    (hg : HasVecRevFDerivUpdate 𝕜 W g g') (hf : HasVecRevFDeriv 𝕜 W (fun yx : Y×X => f yx.1 yx.2) f') :
    HasVecRevFDeriv 𝕜 W
      (fun x =>
        let y := g x
        f y x)
      (fun x =>
        let' (y, dg') := g' x
        let' (z, df') := f' (y,x)
        (z, fun dz =>
          let' (dy,dx) := df' dz
          let dx := dg' dy dx
          dx)) := by
  sorry_proof


@[data_synth]
theorem apply_rule {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecRevFDeriv 𝕜 W (fun x : I → X => x i)
      (fun x =>
        (x i, fun dx i => dx)) := sorry_proof

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecRevFDeriv 𝕜 W (fun x : (I → X)×Y => x.1 i)
      (fun x =>
        (x.1 i, fun dx => ⟨fun i => dx, 0⟩)) := sorry_proof

theorem pi_rule {I nI} [IndexType I nI] [Fold I] [Fold I] [Fold I]
    {f : X → I → Y} {f' : I → _} (hf : ∀ i, HasVecRevFDerivUpdate 𝕜 W (f · i) (f' i)) :
    HasVecRevFDeriv 𝕜 W f
      (fun x =>
        (fun i => f x i,
         fun dy =>
           IndexType.fold .full (init:=(0:WX)) (fun i dx =>
             let' (y,df') := f' i x
             let dyi := dy i
             let dx := df' dyi dx
             dx))) := by
  sorry_proof

-- set_option linter.unusedVariables false in
-- theorem proj_rule
--     {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace 𝕜 X₁]
--     {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace 𝕜 X₂]
--     (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
--     (hg : HasVecRevFDeriv 𝕜 W g g') (hf : f = fun x => g (p₁ x) := by rfl)
--     (hp₁ : IsContinuousLinearMap K p₁ := by fun_prop) /- (hdec : Decomposition p₁ p₂ q) -/ :
--     HasVecRevFDeriv 𝕜 W f
--       (fun x dx =>
--         let x₁ := p₁ x
--         let dx₁ := dx.map p₁
--         let ydy := g' x₁ dx₁
--         ydy) := by
--   sorry_proof

-- set_option linter.unusedVariables false in
-- theorem let_skip_rule
--     {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
--     {g : X → α} {f : α → X → Z} {f' : α → _}
--     (hf : ∀ a, HasVecRevFDeriv 𝕜 W (f a) (f' a))
--     (hg : g.IsConstant) :
--     HasVecRevFDeriv 𝕜 W
--       (fun x =>
--         let y := g x
--         f y x)
--       (fun x dx =>
--         let a := g x
--         let' (z, dz) := f' a x dx
--         (z, dz)) := by
--   sorry_proof


open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv,``pi_rule⟩, .pi
      (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv,``proj_rule⟩, .proj
   --    (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
   --    (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
   --    (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDeriv,``let_skip_rule⟩, .letSkip
   --    (← getConstArgId ``let_skip_rule `g) (← getConstArgId ``let_skip_rule `f)
   --    (← getConstArgId ``let_skip_rule `hf)⟩

end HasVecRevFDeriv


namespace HasVecRevFDerivUpdate

@[data_synth]
theorem id_rule : HasVecRevFDerivUpdate 𝕜 W (fun x : X => x) (λ x => (x, fun dx dx' => dx' + dx)) := by
  sorry_proof

theorem const_rule (c : Y) :
    HasVecRevFDerivUpdate 𝕜 W
      (fun _ : X => c)
      (fun _ => (c, fun dy dx => dx)) := by
  sorry_proof

theorem comp_rule {g : X → Y} {f : Y → Z} {g' f'}
    (hf : HasVecRevFDeriv 𝕜 W f f') (hg : HasVecRevFDerivUpdate 𝕜 W g g') :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => f (g x))
      (fun x =>
        let' (y, dg') := g' x
        let' (z, df') := f' y
        (z, fun dz dx =>
          let dy := df' dz
          let dx := dg' dy dx
          dx)) := by
  sorry_proof

theorem let_rule {g : X → Y} {f : Y → X → Z} {f' g'}
    (hg : HasVecRevFDerivUpdate 𝕜 W g g')
    (hf : HasVecRevFDerivUpdate 𝕜 W (fun yx : Y×X => f yx.1 yx.2) f') :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x =>
        let y := g x
        f y x)
      (fun x =>
        let' (y, dg') := g' x
        let' (z, df') := f' (y,x)
        (z, fun dz dx =>
          let' (dy,dx) := df' dz ⟨0,dx⟩
          let dx' := dg' dy dx
          dx' + dx)) := by
  sorry_proof


@[data_synth]
theorem apply_rule {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecRevFDerivUpdate 𝕜 W (fun x : I → X => x i)
      (fun x =>
        (x i, fun dx dx' i => dx' i + dx)) := sorry_proof

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecRevFDerivUpdate 𝕜 W (fun x : (I → X)×Y => x.1 i)
      (fun x =>
        (x.1 i, fun dx dx' => ⟨fun i => dx'.1 i + dx, dx'.2⟩)) := sorry_proof

theorem pi_rule {I nI} [IndexType I nI] [Fold I] [Fold I] [Fold I]
    {f : X → I → Y} {f' : I → _} (hf : ∀ i, HasVecRevFDerivUpdate 𝕜 W (f · i) (f' i)) :
    HasVecRevFDerivUpdate 𝕜 W f
      (fun x =>
        (fun i => f x i,
         fun dy dx =>
           IndexType.fold .full (init:=dx) (fun i dx =>
             let' (y,df') := f' i x
             let dyi := dy i
             let dx := df' dyi dx
             dx))) := by
  sorry_proof

-- set_option linter.unusedVariables false in
-- theorem proj_rule
--     {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace 𝕜 X₁]
--     {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace 𝕜 X₂]
--     (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
--     (hg : HasVecRevFDerivUpdate 𝕜 W g g') (hf : f = fun x => g (p₁ x) := by rfl)
--     (hp₁ : IsContinuousLinearMap K p₁ := by fun_prop) /- (hdec : Decomposition p₁ p₂ q) -/ :
--     HasVecRevFDerivUpdate 𝕜 W f
--       (fun x dx =>
--         let x₁ := p₁ x
--         let dx₁ := dx.map p₁
--         let ydy := g' x₁ dx₁
--         ydy) := by
--   sorry_proof

-- set_option linter.unusedVariables false in
-- theorem let_skip_rule
--     {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
--     {g : X → α} {f : α → X → Z} {f' : α → _}
--     (hf : ∀ a, HasVecRevFDerivUpdate 𝕜 W (f a) (f' a))
--     (hg : g.IsConstant) :
--     HasVecRevFDerivUpdate 𝕜 W
--       (fun x =>
--         let y := g x
--         f y x)
--       (fun x dx =>
--         let a := g x
--         let' (z, dz) := f' a x dx
--         (z, dz)) := by
--   sorry_proof


open Lean Meta
#eval show MetaM Unit from do
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate,``pi_rule⟩, .pi
      (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate,``proj_rule⟩, .proj
   --    (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
   --    (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
   --    (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecRevFDerivUpdate,``let_skip_rule⟩, .letSkip
   --    (← getConstArgId ``let_skip_rule `g) (← getConstArgId ``let_skip_rule `f)
   --    (← getConstArgId ``let_skip_rule `hf)⟩

end HasVecRevFDerivUpdate

end SciLean
open SciLean


variable
  {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace 𝕜 W]
  {WX : Type*} [NormedAddCommGroup WX] [AdjointSpace 𝕜 WX]
  {WY : Type*} [NormedAddCommGroup WY] [AdjointSpace 𝕜 WY]
  {WZ : Type*} [NormedAddCommGroup WZ] [AdjointSpace 𝕜 WZ]
  [TensorProductType 𝕜 W X WX]
  [TensorProductType 𝕜 W Y WY]
  [TensorProductType 𝕜 W Z WZ]

set_default_scalar 𝕜

@[data_synth]
theorem Prod.mk.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    {f : X → Y} {g : X → Z} {f' g'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f') (hg : HasVecRevFDerivUpdate 𝕜 W g g') :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => (f x, g x))
      (fun x =>
        let' (y, df') := f' x
        let' (z, dg') := g' x
        ((y, z),
         fun dyz dx =>
           let' (dy,dz) := dyz
           dg' dz (df' dy dx))) := by
  sorry_proof


@[data_synth]
theorem Prod.fst.arg_self.HasVecRevFDerivUpdate_proj_rule :
    HasVecRevFDerivUpdate 𝕜 W
      (fun xy : X×Y => xy.1)
      (fun x => (x.1, fun dx dxy => let' (dx',dy') := dxy; ⟨dx' + dx, dy'⟩)) := by
  sorry_proof

@[data_synth]
theorem Prod.snd.arg_self.HasVecRevFDerivUpdate_proj_rule :
    HasVecRevFDerivUpdate 𝕜 W
      (fun xy : X×Y => xy.2)
      (fun x => (x.2, fun dy dxy => let' (dx',dy') := dxy; ⟨dx', dy' + dy⟩)) := by
  sorry_proof

@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    {f : X → Y} {g : X → Y} {f' g'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f') (hg : HasVecRevFDerivUpdate 𝕜 W g g') :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => f x + g x)
      (fun x =>
        let' (y, df') := f' x
        let' (z, dg') := g' x
        (y + z, fun dy dx =>
          let dx := df' dy dx
          let dx := dg' dy dx
          dx)) := by
  sorry_proof


@[data_synth]
theorem HSub.hSub.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    {f : X → Y} {g : X → Y} {f' g'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f') (hg : HasVecRevFDerivUpdate 𝕜 W g g') :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => f x - g x)
      (fun x =>
        let' (y, df') := f' x
        let' (z, dg') := g' x
        (y - z, fun dy dx =>
          let dx := df' dy dx
          let dx := dg' (-dy) dx
          dx)) := by
  sorry_proof


@[data_synth]
theorem Neg.neg.arg_a0.HasVecRevFDerivUpdate_comp_rule :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : X => - x)
      (fun x =>
        (- y, fun dx' dx =>
          let dx := dx - dx'
          dx)) := by
  sorry_proof

set_default_scalar 𝕜
open ComplexConjugate TensorProductType


@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W] :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : 𝕜 × X => x.1 • x.2)
      (fun x =>
        (x.1 • x.2, fun dx' dwx =>
          let' (dw,dx) := dwx
          ⟨matVecMulAdd (1:𝕜) dx' x.2 1 dw,
           dx + x.1 • dx'⟩)) := by
  sorry_proof

@[data_synth]
theorem HMul.hMul.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W] :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : 𝕜 × 𝕜 => x.1 * x.2)
      (fun x =>
        (x.1 * x.2, fun dw' dw =>
          let' (dw₁, dw₂) := dw
          ⟨dw₁ + x.2 • dx',
           dw₂ + x.1 • dx'⟩)) := by
  sorry_proof


@[data_synth]
theorem HDiv.hDiv.arg_a0a1.HasVecRevFDerivUpdate_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    {f g : X → 𝕜} {f' g'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f') (hg : HasVecRevFDerivUpdate 𝕜 W g g')
    (hg' : ∀ x, g x ≠ 0) :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => f x / g x)
      (fun x =>
        let' (y, df') := f' x
        let' (z, dg') := g' x
        let iz := z⁻¹
        (iz • y, fun dw dx =>
          let s := ((conj z)^2)⁻¹
          let dw₁ := (-s * (conj y)) • dw
          let dw₂ := (s * (conj z)) • dw
          let dx := dg' dw₁ dx
          let dx := df' dw₂ dx
          dx)) := by
  sorry_proof

  -- apply HasVecRevFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth (disch:=aesop)
  -- case simp => intros; simp_all

@[data_synth]
theorem HDiv.hDiv.arg_a0.HasVecRevFDerivUpdate_comp_rule [Module 𝕜ᵐᵒᵖ W] [Star W]
    (y : 𝕜) :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : 𝕜 => x / c)
      (fun x =>
        let ic := c⁻¹
        (ic * y, fun dw' dw =>
          let dw := dw + (conj ic) • dw'
          dw)) := by
  sorry_proof


@[data_synth]
theorem HInv.hInv.arg_a0.HasVecRevFDeriv_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    {f : X → 𝕜} {f'}
    (hf : HasVecRevFDeriv 𝕜 W f f')
    (hf' : ∀ x, f x ≠ 0) :
    HasVecRevFDeriv 𝕜 W
      (fun x => (f x)⁻¹)
      (fun x =>
        let' (y, df') := f' x
        let iy := y⁻¹
        (iy, fun dw =>
          let s := ((conj y)^2)⁻¹
          let dw := -s • dw
          let dx := df' dw
          dx)) := by
  sorry_proof

@[data_synth]
theorem HInv.hInv.arg_a0.HasVecRevFDerivUpdate_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    {f : X → 𝕜} {f'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f')
    (hf' : ∀ x, f x ≠ 0) :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => (f x)⁻¹)
      (fun x =>
        let' (y, df') := f' x
        let iy := y⁻¹
        (iy, fun dw dx =>
          let s := ((conj y)^2)⁻¹
          let dw := -s • dw
          let dx := df' dw dx
          dx)) := by
  sorry_proof

@[data_synth]
theorem HPow.hPow.arg_a0.HasVecRevFDeriv_rule_nat
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    {f : X → 𝕜} {f'}
    (hf : HasVecRevFDeriv 𝕜 W f f') (n : ℕ) :
    HasVecRevFDeriv 𝕜 W
      (fun x => (f x)^n)
      (fun x =>
        let' (y, df') := f' x
        (y^n,  fun dw =>
          let dw := (n • y^(n-1)) • dw
          let dx := df' dw
          dx)) := by
  sorry_proof

@[data_synth]
theorem HPow.hPow.arg_a0.HasVecRevFDerivUpdate_rule_nat
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    {f : X → 𝕜} {f'}
    (hf : HasVecRevFDerivUpdate 𝕜 W f f') (n : ℕ) :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => (f x)^n)
      (fun x =>
        let' (y, df') := f' x
        (y^n,  fun dw dx =>
          let dw := (n • y^(n-1)) • dw
          let dx := df' dw dx
          dx)) := by
  sorry_proof


set_option linter.unusedVariables false in
@[data_synth]
theorem SciLean.IndexType.sum.arg_f.HasVecRevFDeriv_rule
    {I : Type*} {nI} [IndexType I nI] [Fold I] [Fold I]
    {f : X → I → Y} {f' : I → _}
    (hf : ∀ i, HasVecRevFDerivUpdate 𝕜 W (f · i) (f' i)) :
    HasVecRevFDeriv 𝕜 W
      (fun x => ∑ᴵ i, f x i)
      (fun x =>
        (∑ᴵ i, f x i,
         fun dy =>
           IndexType.fold .full (init:=(0 : W⊗X)) fun i dx =>
             let dx := (f' i x).2 dy dx
             dx)) := by
  sorry_proof

set_option linter.unusedVariables false in
@[data_synth]
theorem SciLean.IndexType.sum.arg_f.HasVecRevFDerivUpdate_rule
    {I : Type*} {nI} [IndexType I nI] [Fold I] [Fold I]
    {f : X → I → Y} {f' : I → _}
    (hf : ∀ i, HasVecRevFDerivUpdate 𝕜 W (f · i) (f' i)) :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x => ∑ᴵ i, f x i)
      (fun x =>
        (∑ᴵ i, f x i,
         fun dy dx =>
           IndexType.fold .full (init:=dx) fun i dx =>
             let dx := (f' i x).2 dy dx
             dx)) := by
  sorry_proof


section OverReals

variable
  {𝕜 : Type*} [RealScalar 𝕜]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace 𝕜 W]
  {WX : Type*} [NormedAddCommGroup WX] [AdjointSpace 𝕜 WX]
  {WY : Type*} [NormedAddCommGroup WY] [AdjointSpace 𝕜 WY]
  {WZ : Type*} [NormedAddCommGroup WZ] [AdjointSpace 𝕜 WZ]
  [TensorProductType 𝕜 W X WX] [TensorProductGetYX 𝕜 W X WX]
  [TensorProductType 𝕜 W Y WY] [TensorProductGetYX 𝕜 W Y WY]
  [TensorProductType 𝕜 W Z WZ] [TensorProductGetYX 𝕜 W Z WZ]


open ComplexConjugate TensorProductType

set_default_scalar 𝕜

@[data_synth]
theorem Inner.inner.arg_a0a1.HasVecRevFDeriv_simple_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W] :
    HasVecRevFDeriv 𝕜 W
      (fun x : X×X => ⟪x.1, x.2⟫[𝕜])
      (fun x =>
        (⟪x.1, x.2⟫[𝕜], fun dw =>
          ⟨dw ⊗ x.2, dw ⊗ x.1⟩)) := by
  sorry_proof

@[data_synth]
theorem Inner.inner.arg_a0a1.HasVecRevFDerivUpdate_simple_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W] :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : X×X => ⟪x.1, x.2⟫[𝕜])
      (fun x =>
        (⟪x.1, x.2⟫[𝕜], fun dw dx =>
          let' (dx₁,dx₂) := dx
          ⟨tmulAdd (1:𝕜) dw x.2 dx₁, tmulAdd (1:𝕜) dw x.1 dx₂⟩)) := by
  sorry_proof

@[data_synth]
theorem Norm2.norm2.arg_a0.HasVecRevFDerivUpdate_simple_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W] :
    HasVecRevFDerivUpdate 𝕜 W
      (fun x : X => ‖x‖₂²[𝕜])
      (fun x =>
        (‖x‖₂²[𝕜], fun dw' dw =>
          let dw := tmulAdd (2:𝕜) dw' x dw
          dw)) := by
  sorry_proof

@[data_synth]
theorem SciLean.norm₂.arg_x.HasVecRevFDeriv_comp_rule
    [Module 𝕜ᵐᵒᵖ W] [Star W]
    (f : X → Y) {f'} (hf : HasVecRevFDeriv 𝕜 W f f') (hf' : ∀ x, f x ≠ 0) :
    HasVecRevFDeriv 𝕜 W (fun x => ‖f x‖₂[𝕜])
      (fun x =>
        let' (y, df') := f' x
        let yn := ‖y‖₂[𝕜]
        (yn, fun dw : W =>
          let dir := yn⁻¹ • y
          let dx := df' (dw ⊗ dir)
          dx)) := by
  sorry_proof

end OverReals
