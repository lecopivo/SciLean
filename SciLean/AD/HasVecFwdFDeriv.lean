module

public import SciLean.Algebra.TensorProduct.Prod
public import SciLean.Algebra.TensorProduct.Pi
public import SciLean.Algebra.TensorProduct.Self
public import SciLean.Algebra.TensorProduct.Util
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
  {XW : Type*} [NormedAddCommGroup XW] [AdjointSpace 𝕜 XW]
  {YW : Type*} [NormedAddCommGroup YW] [AdjointSpace 𝕜 YW]
  {ZW : Type*} [NormedAddCommGroup ZW] [AdjointSpace 𝕜 ZW]
  [TensorProductType 𝕜 X W XW]
  [TensorProductType 𝕜 Y W YW]
  [TensorProductType 𝕜 Z W ZW]


set_default_scalar 𝕜

variable (𝕜 W) in
@[data_synth out f' in f]
structure HasVecFwdFDeriv (f : X → Y) (f' : X → X ⊗ W → Y × (Y ⊗ W)) where
  val : ∀ x dx, (f' x dx).1 = f x
  deriv : ∃ df : X → X →L[𝕜] Y,
      (∀ x, HasFDerivAt f (df x) x)
      ∧
      (∀ x (dx : X) (w : W), df x dx ⊗ w = (f' x (dx ⊗ w)).2)
  -- I think linearity is necessary requirement as we define `f'` only on inputs of the form
  -- `dx ⊗ w` which needs to be extended by linearity to all elements of `X ⊗ W`
  linear : ∀ x, IsContinuousLinearMap 𝕜 (fun dx => (f' x dx).2)

variable (𝕜 W) in
@[data_synth out f' in f]
structure HasVecFwdFDerivUpdate (f : X → Y) (f' : X → X ⊗ W → Y × (Y ⊗ W → Y ⊗ W)) where
  val : ∀ x dx, (f' x dx).1 = f x
  deriv : HasVecFwdFDeriv 𝕜 W f (fun x dx => let' (y,df) := f' x dx; (y, df 0))
  add_dy : ∀ x dx dy, (f' x dx).2 dy = dy + (f' x dx).2 0


open Classical in
variable (𝕜 W) in
noncomputable
def vecFwdFDeriv (f : X → Y) (x : X) (dx : X ⊗ W) : (Y × (Y ⊗ W)) :=
  if h : ∃ f', HasVecFwdFDeriv 𝕜 W f f' then
    choose h x dx
  else
    (0,0)


set_option linter.unusedVariables false in
theorem vecFwdFDeriv_from_hasVecFwdFDeriv
    {f : X → Y} {f'} (hf : HasVecFwdFDeriv 𝕜 W f f') :
    vecFwdFDeriv 𝕜 W f = f' := by
  sorry_proof

simproc_decl vecFwdFDeriv_simproc (vecFwdFDeriv _ _ _) :=
  mkDataSynthSimproc `vecFwdFDeriv_simproc ``vecFwdFDeriv_from_hasVecFwdFDeriv

section Jacobian

variable
  [SMul (𝕜ᵐᵒᵖ) X] [Star X]
  {XX : Type*} [NormedAddCommGroup XX] [AdjointSpace 𝕜 XX]
  {YX : Type*} [NormedAddCommGroup YX] [AdjointSpace 𝕜 YX]
  [TensorProductType 𝕜 Y X YX]
  [TensorProductType 𝕜 X X XX] [TensorProductSelf 𝕜 X XX]

variable (𝕜) in
noncomputable
def jacobianMat (f : X → Y) (x : X) : Y⊗X :=
  (vecFwdFDeriv 𝕜 X f x (𝐈[𝕜,X])).2

/--
Express `jacobianMat` with vector forward mode AD `vecFwdFDeriv`
-/
theorem jacobian_vector_mode (f : X → Y) :
  jacobianMat 𝕜 f = fun x => (vecFwdFDeriv 𝕜 X f x (𝐈[𝕜,X])).2 := by rfl

/--
Express `jacobianMat` with reverse mode AD `revFDeriv`
-/
theorem jacobian_reverse_mode (f : X → 𝕜) :
  jacobianMat 𝕜 f = fun x => (revFDeriv 𝕜 f x).2 1 := by sorry_proof


end Jacobian


----------------------------------------------------------------------------------------------------
-- API for constructing and deconstructing HasFwdFDeriv --------------------------------------------
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

namespace HasVecFwdFDeriv

@[data_synth]
theorem id_rule : HasVecFwdFDeriv 𝕜 W (fun x : X => x) (λ x dx => (x, dx)) := by
  sorry_proof

theorem const_rule (c : Y) : HasVecFwdFDeriv 𝕜 W (fun _ : X => c) (λ _ _ => (c, 0)) := by
  sorry_proof

theorem comp_rule {g : X → Y} {f : Y → Z} {g' f'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => f (g x))
      (fun x dx =>
        let' (y, dy) := g' x dx;
        let' (z, dz) := f' y dy;
        (z, dz)) := by
  sorry_proof

theorem let_rule {g : X → Y} {f : Y → X → Z} {f' g'}
    (hg : HasVecFwdFDeriv 𝕜 W g g') (hf : HasVecFwdFDeriv 𝕜 W (fun yx : Y×X => f yx.1 yx.2) f') :
    HasVecFwdFDeriv 𝕜 W
      (fun x =>
        let y := g x
        f y x)
      (fun x dx =>
        let' (y, dy) := g' x dx
        let' (z, dz) := f' (y,x) ⟨dy,dx⟩
        (z, dz)) := by
  sorry_proof

@[data_synth]
theorem apply_rule {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecFwdFDeriv 𝕜 W (fun x : I → X => x i)
      (fun x dx =>
        (x i, dx i)) := sorry_proof

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecFwdFDeriv 𝕜 W (fun x : (I → X)×Y => x.1 i)
      (fun x dx =>
        (x.1 i, dx.1 i)) := sorry_proof

theorem pi_rule {I nI} [IndexType I nI] [Fold I] [Fold I]
    {f : X → I → Y} {f' : I → _} (hf : ∀ i, HasVecFwdFDeriv 𝕜 W (f · i) (f' i)) :
    HasVecFwdFDeriv 𝕜 W f
      (fun x dx => (fun i => f x i, fun i => (f' i x dx).2)) := by
  sorry_proof


-- theorem proj_rule
--     {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace 𝕜 X₁]
--     {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace 𝕜 X₂]
--     {XW₁ : Type*} [NormedAddCommGroup XW₁] [AdjointSpace 𝕜 XW₁]
--     [TensorProductType 𝕜 X₁ W XW₁]
--     (f : X → Y) (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) {g'}
--     (hg : HasVecFwdFDeriv 𝕜 W g g') (hf : f = fun x => g (p₁ x) := by rfl)
--     (hp₁ : IsContinuousLinearMap 𝕜 p₁ := by fun_prop) /- (hdec : Decomposition p₁ p₂ q) -/ :
--     HasVecFwdFDeriv 𝕜 W f
--       (fun x dx =>
--         let x₁ := p₁ x
--         let dx₁ := tmap (fun x =>L[𝕜] p₁ x) (fun w : W =>L[𝕜] w) dx
--         let ydy := g' x₁ dx₁
--         ydy) := by
--   sorry_proof

-- set_option linter.unusedVariables false in
-- theorem let_skip_rule
--     {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
--     {g : X → α} {f : α → X → Z} {f' : α → _}
--     (hf : ∀ a, HasVecFwdFDeriv 𝕜 W (f a) (f' a))
--     (hg : g.IsConstant) :
--     HasVecFwdFDeriv 𝕜 W
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
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv,``const_rule⟩, .const⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv,``pi_rule⟩, .pi
      (← getConstArgId ``pi_rule `f) (← getConstArgId ``pi_rule `hf)⟩
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv,``proj_rule⟩, .proj
   --    (← getConstArgId ``proj_rule `f) (← getConstArgId ``proj_rule `g)
   --    (← getConstArgId ``proj_rule `p₁) (← getConstArgId ``proj_rule `p₂)
   --    (← getConstArgId ``proj_rule `q) (← getConstArgId ``proj_rule `hg)⟩
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasVecFwdFDeriv,``let_skip_rule⟩, .letSkip
   --    (← getConstArgId ``let_skip_rule `g) (← getConstArgId ``let_skip_rule `f)
   --    (← getConstArgId ``let_skip_rule `hf)⟩

end HasVecFwdFDeriv
end SciLean
open SciLean


variable
  {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace 𝕜 W] [SMul (𝕜ᵐᵒᵖ) W] [Star W]
  {XW : Type*} [NormedAddCommGroup XW] [AdjointSpace 𝕜 XW]
  {YW : Type*} [NormedAddCommGroup YW] [AdjointSpace 𝕜 YW]
  {ZW : Type*} [NormedAddCommGroup ZW] [AdjointSpace 𝕜 ZW]
  [TensorProductType 𝕜 X W XW]
  [TensorProductType 𝕜 Y W YW]
  [TensorProductType 𝕜 Z W ZW]



@[data_synth]
theorem Prod.mk.arg_a0a1.HasVecFwdFDeriv_comp_rule
    {f : X → Y} {g : X → Z} {f' g'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => (f x, g x))
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        ((y, z), ⟨dy,dz⟩)) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf
  -- have ⟨_,_,_,_⟩ := hg
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem Prod.fst.arg_self.HasVecFwdFDeriv_proj_rule
    (f : X → Y×Z) (hf : HasVecFwdFDeriv 𝕜 W f f') :
    HasVecFwdFDeriv 𝕜 W
      (fun x : X => (f x).1)
      (fun x dx =>
        let' ((y,z),(dy,dz)) := f' x dx
        (y, dy)) := by
  sorry_proof
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem Prod.snd.arg_self.HasVecFwdFDeriv_proj_rule
    (f : X → Y×Z) (hf : HasVecFwdFDeriv 𝕜 W f f') :
    HasVecFwdFDeriv 𝕜 W
      (fun x : X => (f x).2)
      (fun x dx =>
        let' ((y,z),(dy,dz)) := f' x dx
        (z, dz)) := by
  sorry_proof
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasVecFwdFDeriv_comp_rule
    {f : X → Y} {g : X → Y} {f' g'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => f x + g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y + z, dy + dz)) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf
  -- have ⟨_,_,_,_⟩ := hg
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem HSub.hSub.arg_a0a1.HasVecFwdFDeriv_comp_rule
    {f : X → Y} {g : X → Y} {f' g'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => f x - g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y - z, dy - dz)) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf
  -- have ⟨_,_,_,_⟩ := hg
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all

@[data_synth]
theorem Neg.neg.arg_a0.HasVecFwdFDeriv_comp_rule
    {f : X → Y} {f'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => - f x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        (- y, -dy)) := by
  sorry_proof
  -- have ⟨_,_,_,_⟩ := hf
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth
  -- case simp => intros; simp_all


set_default_scalar 𝕜

@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasVecFwdFDeriv_comp_rule
    {f : X → 𝕜} {g : X → Y} {f' g'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => f x • g x)
      (fun x dx =>
        let' (y, dy) := f' x dx
        let' (z, dz) := g' x dx
        (y • z, y • dz + z ⊗ dy)) := by
  sorry_proof

@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasVecFwdFDeriv_rule_nat
    {g : X → Y} {g'} (n : ℕ)
    (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => n • g x)
      (fun x dx =>
        let' (z, dz) := g' x dx
        (n • z, n • dz)) := by
  sorry_proof

@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasVecFwdFDeriv_rule_int
    {g : X → Y} {g'} (n : ℤ)
    (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => n • g x)
      (fun x dx =>
        let' (z, dz) := g' x dx
        (n • z, n • dz)) := by
  sorry_proof

@[data_synth]
theorem HMul.hMul.arg_a0a1.HasVecFwdFDeriv_comp_rule
    {f g : X → 𝕜} {f' g'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => f x * g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y * z, y ⊗ dz + z ⊗ dy)) := by
  sorry_proof

-- ugh really? can't this be simpler?
@[data_synth]
theorem SciLean.tmul.arg_yx.HasVecFwdFDeriv_comp_rule
    {YZ} [NormedAddCommGroup YZ] [AdjointSpace 𝕜 YZ] [TensorProductType 𝕜 Y Z YZ]
    {WZ} [NormedAddCommGroup WZ] [AdjointSpace 𝕜 WZ] [TensorProductType 𝕜 W Z WZ]
    {YZ_W} [NormedAddCommGroup YZ_W] [AdjointSpace 𝕜 YZ_W] [TensorProductType 𝕜 YZ W YZ_W]
    {Y_ZW} [NormedAddCommGroup Y_ZW] [AdjointSpace 𝕜 Y_ZW] [TensorProductType 𝕜 Y ZW Y_ZW]
    {YW_Z} [NormedAddCommGroup YW_Z] [AdjointSpace 𝕜 YW_Z] [TensorProductType 𝕜 YW Z YW_Z]
    {Y_WZ} [NormedAddCommGroup Y_WZ] [AdjointSpace 𝕜 Y_WZ] [TensorProductType 𝕜 Y WZ Y_WZ]
    [TensorProductGetRXY 𝕜 Y WZ Y_WZ] [TensorProductGetRXY 𝕜 W Z WZ]
    [TensorProductGetRXY 𝕜 YW Z YW_Z] [TensorProductGetRXY 𝕜 Y W YW]
    [TensorProductGetRXY 𝕜 Y ZW Y_ZW] [TensorProductGetRXY 𝕜 Z W ZW]
    {f : X → Y} {g : X → Z} {f' g'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => f x ⊗ g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        (y ⊗ z,
          let y_dz : (Y ⊗ Z) ⊗ W := tassocl (y ⊗ dz)
          let asdf := dy ⊗ z
          let dy_z : (Y ⊗ Z) ⊗ W := tassocl (tswapRight (tassocr (dy ⊗ z)))
          y_dz + dy_z)) := by
  sorry_proof


set_option linter.overlappingInstances false in
@[data_synth]
theorem HDiv.hDiv.arg_a0a1.HasVecFwdFDeriv_comp_rule
    [SMul (𝕜ᵐᵒᵖ) W] [Star W]
    {f g : X → 𝕜} {f' g'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') (hg : HasVecFwdFDeriv 𝕜 W g g')
    (hg' : ∀ x, g x ≠ 0) :
    HasVecFwdFDeriv 𝕜 W
      (fun x => f x / g x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        let iz := z⁻¹
        (iz • y, iz^2 • (y ⊗ dz - z ⊗ dy))) := by
  sorry_proof
  -- apply HasVecFwdFDeriv_from_hasFDerivAt
  -- case deriv => intros; data_synth (disch:=aesop)
  -- case simp => intros; simp_all

@[data_synth]
theorem HDiv.hDiv.arg_a0.HasVecFwdFDeriv_comp_rule
    {f : X → 𝕜} (c : 𝕜) {f'}
    (hf : HasVecFwdFDeriv 𝕜 W f f')  :
    HasVecFwdFDeriv 𝕜 W
      (fun x => f x / c)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let ic := c⁻¹
        (ic * y, ic • dy)) := by
  sorry_proof


@[data_synth]
theorem HInv.hInv.arg_a0.HasVecFwdFDeriv_comp_rule
    {f : X → 𝕜} {f'}
    (hf : HasVecFwdFDeriv 𝕜 W f f')
    (hf' : ∀ x, f x ≠ 0) :
    HasVecFwdFDeriv 𝕜 W
      (fun x => (f x)⁻¹)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let iy := y⁻¹
        (iy, - iy^2 • dy)) := by
  sorry_proof

@[data_synth]
theorem HPow.hPow.arg_a0.HasVecFwdFDeriv_rule_nat
    {f : X → 𝕜} {f'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') (n : ℕ) :
    HasVecFwdFDeriv 𝕜 W
      (fun x => (f x)^n)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        (y^n,  n • y^(n-1) • dy)) := by
  sorry_proof

set_option linter.unusedVariables false in
@[data_synth]
theorem SciLean.IndexType.sum.arg_f.HasVecFwdFDeriv_rule
    {I : Type*} {nI} [IndexType I nI] [Fold I] [Fold I]
    {f : X → I → Y} {f' : I → _}
    (hf : ∀ i, HasVecFwdFDeriv 𝕜 W (f · i) (f' i)) :
    HasVecFwdFDeriv 𝕜 W
      (fun x => ∑ᴵ i, f x i)
      (fun x dx =>
        ∑ᴵ i,
          let ydy := f' i x dx
          ydy) := by
  sorry_proof



section OverReals

variable
  {𝕜 : Type*} [RealScalar 𝕜]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace 𝕜 W] [SMul (𝕜ᵐᵒᵖ) W] [Star W]
  {XW : Type*} [NormedAddCommGroup XW] [AdjointSpace 𝕜 XW]
  {YW : Type*} [NormedAddCommGroup YW] [AdjointSpace 𝕜 YW]
  {ZW : Type*} [NormedAddCommGroup ZW] [AdjointSpace 𝕜 ZW]
  [TensorProductType 𝕜 X W XW] [TensorProductGetYX 𝕜 X W XW]
  [TensorProductType 𝕜 Y W YW] [TensorProductGetYX 𝕜 Y W YW]
  [TensorProductType 𝕜 Z W ZW] [TensorProductGetYX 𝕜 Z W ZW]

set_default_scalar 𝕜

open ComplexConjugate TensorProductType

@[data_synth]
theorem Inner.inner.arg_a0a1.HasVecFwdFDeriv_comp_rule
    (f g : X → Y) (f' g')
    (hf : HasVecFwdFDeriv 𝕜 W f f') (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => ⟪f x, g x⟫[𝕜])
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        -- ⟪dy[i], z⟫[K] + ⟪y, dz[i]⟫[K]
        (⟪y, z⟫[𝕜], vecMatMulAdd (1:𝕜) z dy (0:𝕜) (vecMatMulAdd (1:𝕜) y dz (0:𝕜) 0))) := by
  sorry_proof


@[data_synth]
theorem Norm2.norm2.arg_a0.HasVecFwdFDeriv_simple_rule :
    HasVecFwdFDeriv 𝕜 W
      (fun x : Y => ‖x‖₂²[𝕜])
      (fun x dx =>
        (‖x‖₂²[𝕜], vecMatMulAdd (2:𝕜) x dx (0:𝕜) 0)) := by
  sorry_proof

@[data_synth]
theorem SciLean.norm₂.arg_x.HasVecFwdFDeriv_comp_rule
    (f : X → Y) {f'} (hf : HasVecFwdFDeriv 𝕜 W f f') (hf' : ∀ x, f x ≠ 0) :
    HasVecFwdFDeriv 𝕜 W (fun x => ‖f x‖₂[𝕜]) (fun x dx =>
      let' (y, dy) := f' x dx;
      let yn := ‖y‖₂[𝕜]
      let iyn := yn⁻¹
      (yn, vecMatMulAdd iyn x dx (0:𝕜) 0)) := by
  sorry_proof

end OverReals
