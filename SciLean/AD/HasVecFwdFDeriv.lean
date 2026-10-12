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


theorem HasVecFwdFDeriv.unique {f : X → Y} {f' f'' : X → X ⊗ W → Y × (Y ⊗ W)}
    (h1 : HasVecFwdFDeriv 𝕜 W f f') (h2 : HasVecFwdFDeriv 𝕜 W f f'') : f' = f'' := by
  obtain ⟨df1, hd1, ht1⟩ := h1.deriv
  obtain ⟨df2, hd2, ht2⟩ := h2.deriv
  funext x
  have hdf : df1 x = df2 x := (hd1 x).unique (hd2 x)
  have hsnd : (fun dx => (f' x dx).2) = (fun dx => (f'' x dx).2) :=
    tmul_ext (Y:=X) (X:=W) (h1.linear x).linear (h2.linear x).linear
      (fun dx w => by rw [← ht1 x dx w, ← ht2 x dx w, hdf])
  funext dx
  exact Prod.ext ((h1.val x dx).trans (h2.val x dx).symm) (congrFun hsnd dx)

theorem vecFwdFDeriv_from_hasVecFwdFDeriv
    {f : X → Y} {f'} (hf : HasVecFwdFDeriv 𝕜 W f f') :
    vecFwdFDeriv 𝕜 W f = f' := by
  have h : ∃ g, HasVecFwdFDeriv 𝕜 W f g := ⟨f', hf⟩
  funext x dx
  simp only [vecFwdFDeriv, h, ↓reduceDIte]
  rw [(Classical.choose_spec h).unique hf]

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
theorem id_rule : HasVecFwdFDeriv 𝕜 W (fun x : X => x) (λ x dx => (x, dx)) where
  val := by intros; rfl
  deriv := ⟨fun _ => ContinuousLinearMap.id 𝕜 X, fun x => hasFDerivAt_id x, by intros; rfl⟩
  linear := by intro x; fun_prop

theorem const_rule (c : Y) : HasVecFwdFDeriv 𝕜 W (fun _ : X => c) (λ _ _ => (c, 0)) where
  val := by intros; rfl
  deriv := ⟨fun _ => 0, fun x => hasFDerivAt_const c x, by intros; simp⟩
  linear := by intro x; fun_prop

theorem comp_rule {g : X → Y} {f : Y → Z} {g' f'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => f (g x))
      (fun x dx =>
        let' (y, dy) := g' x dx;
        let' (z, dz) := f' y dy;
        (z, dz)) := by
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  obtain ⟨dg, hdg, htg⟩ := hg.deriv
  have hgval := hg.val
  constructor
  case val => intro x dx; simp [hg.val, hf.val]
  case deriv =>
    refine ⟨fun x => (df (g x)).comp (dg x), fun x => (hdf (g x)).comp x (hdg x), ?_⟩
    intro x dx w
    simp only [hgval, ← htg x dx w, ← htf]
    rfl
  case linear =>
    intro x
    simp only [hgval]
    exact IsContinuousLinearMap.comp_rule _ (hg.linear x) _ (hf.linear (g x))

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
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  obtain ⟨dg, hdg, htg⟩ := hg.deriv
  have hgval := hg.val
  constructor
  case val => intro x dx; simp [hgval, hf.val]
  case deriv =>
    refine ⟨fun x => (df (g x, x)).comp ((dg x).prod (ContinuousLinearMap.id 𝕜 X)),
            fun x => ?_, ?_⟩
    · have hinner : HasFDerivAt (fun x : X => (g x, x))
          ((dg x).prod (ContinuousLinearMap.id 𝕜 X)) x := (hdg x).prodMk (hasFDerivAt_id x)
      exact HasFDerivAt.comp (𝕜:=𝕜) (f := fun x : X => (g x, x)) (x := x) (hdf (g x, x)) hinner
    intro x dx w
    have h : ((((dg x) dx, dx) : Y×X) ⊗[𝕜] w : ProdMatrixCol YW XW)
           = ⟨(dg x) dx ⊗[𝕜] w, dx ⊗[𝕜] w⟩ := rfl
    simp only [hgval, ← htg x dx w, ← h]
    exact htf (g x, x) ((dg x) dx, dx) w
  case linear =>
    intro x
    simp only [hgval]
    exact IsContinuousLinearMap.comp_rule
      (fun dx => (⟨(g' x dx).2, dx⟩ : ProdMatrixCol YW XW))
      (ProdMatrixCol.mk.arg_A₁A₂.IsContinuousLinearMap_rule _ _ (hg.linear x)
        (IsContinuousLinearMap.id_rule ..))
      (fun t => (f' (g x, x) t).2) (hf.linear (g x, x))

@[data_synth]
theorem apply_rule {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecFwdFDeriv 𝕜 W (fun x : I → X => x i)
      (fun x dx =>
        (x i, dx i)) where
  val := by intros; rfl
  deriv := ⟨fun _ => ContinuousLinearMap.proj i,
           fun x => (ContinuousLinearMap.proj (R:=𝕜) (φ:=fun _ : I => X) i).hasFDerivAt,
           by intros; rfl⟩
  linear := by intro x; fun_prop

-- this should not be necessary if once we improve function decomposition in `data_synth` tactic
@[data_synth]
theorem apply_rule' {I nI} [IndexType I nI] [Fold I] [Fold I] (i : I) :
    HasVecFwdFDeriv 𝕜 W (fun x : (I → X)×Y => x.1 i)
      (fun x dx =>
        (x.1 i, dx.1 i)) where
  val := by intros; rfl
  deriv := ⟨fun _ => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst 𝕜 (I → X) Y),
           fun x => ((ContinuousLinearMap.proj (R:=𝕜) (φ:=fun _ : I => X) i).comp
             (ContinuousLinearMap.fst 𝕜 (I → X) Y)).hasFDerivAt,
           by intros; rfl⟩
  linear := by
    intro x
    exact IsContinuousLinearMap.comp_rule _ ProdMatrixCol.A₁.arg_A.IsContinuousLinearMap_rule
      (fun dx : IndexedMatrixCol I XW => dx i) (by fun_prop)

theorem pi_rule {I nI} [IndexType I nI] [Fold I] [Fold I]
    {f : X → I → Y} {f' : I → _} (hf : ∀ i, HasVecFwdFDeriv 𝕜 W (f · i) (f' i)) :
    HasVecFwdFDeriv 𝕜 W f
      (fun x dx => (fun i => f x i, fun i => (f' i x dx).2)) := by
  choose df hdf htf using fun i => (hf i).deriv
  constructor
  case val => intro x dx; rfl
  case deriv =>
    refine ⟨fun x => ContinuousLinearMap.pi (fun i => df i x), fun x => ?_, ?_⟩
    · exact hasFDerivAt_pi.2 (fun i => hdf i x)
    · intro x dx w
      show (fun i => (df i x) dx) ⊗[𝕜] w = _
      funext i
      exact htf i x dx w
  case linear =>
    intro x
    exact IsContinuousLinearMap.pi_rule _ (fun i => (hf i).linear x)


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
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  obtain ⟨dg, hdg, htg⟩ := hg.deriv
  constructor
  case val => intro x dx; simp [hf.val, hg.val]
  case deriv =>
    refine ⟨fun x => (df x).prod (dg x), fun x => (hdf x).prodMk (hdg x), ?_⟩
    intro x dx w
    have h : ((((df x) dx, (dg x) dx) : Y×Z) ⊗[𝕜] w : ProdMatrixCol YW ZW)
           = ⟨(df x) dx ⊗[𝕜] w, (dg x) dx ⊗[𝕜] w⟩ := rfl
    show ((((df x) dx, (dg x) dx) : Y×Z) ⊗[𝕜] w : ProdMatrixCol YW ZW) = _
    rw [h, htf x dx w, htg x dx w]
  case linear =>
    intro x
    exact ProdMatrixCol.mk.arg_A₁A₂.IsContinuousLinearMap_rule _ _ (hf.linear x) (hg.linear x)

@[data_synth]
theorem Prod.fst.arg_self.HasVecFwdFDeriv_proj_rule
    (f : X → Y×Z) (hf : HasVecFwdFDeriv 𝕜 W f f') :
    HasVecFwdFDeriv 𝕜 W
      (fun x : X => (f x).1)
      (fun x dx =>
        let' ((y,z),(dy,dz)) := f' x dx
        (y, dy)) := by
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  constructor
  case val => intro x dx; simp [hf.val]
  case deriv =>
    refine ⟨fun x => (ContinuousLinearMap.fst 𝕜 Y Z).comp (df x), fun x => (hdf x).fst, ?_⟩
    intro x dx w
    exact congrArg ProdMatrixCol.A₁ (htf x dx w)
  case linear =>
    intro x
    exact IsContinuousLinearMap.comp_rule _ (hf.linear x) _
      ProdMatrixCol.A₁.arg_A.IsContinuousLinearMap_rule

@[data_synth]
theorem Prod.snd.arg_self.HasVecFwdFDeriv_proj_rule
    (f : X → Y×Z) (hf : HasVecFwdFDeriv 𝕜 W f f') :
    HasVecFwdFDeriv 𝕜 W
      (fun x : X => (f x).2)
      (fun x dx =>
        let' ((y,z),(dy,dz)) := f' x dx
        (z, dz)) := by
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  constructor
  case val => intro x dx; simp [hf.val]
  case deriv =>
    refine ⟨fun x => (ContinuousLinearMap.snd 𝕜 Y Z).comp (df x), fun x => (hdf x).snd, ?_⟩
    intro x dx w
    exact congrArg ProdMatrixCol.A₂ (htf x dx w)
  case linear =>
    intro x
    exact IsContinuousLinearMap.comp_rule _ (hf.linear x) _
      ProdMatrixCol.A₂.arg_A.IsContinuousLinearMap_rule

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
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  obtain ⟨dg, hdg, htg⟩ := hg.deriv
  constructor
  case val => intro x dx; simp [hf.val, hg.val]
  case deriv =>
    refine ⟨fun x => df x + dg x, fun x => (hdf x).add (hdg x), ?_⟩
    intro x dx w
    simp only [add_apply, add_tmul, htf, htg]
  case linear =>
    intro x
    exact HAdd.hAdd.arg_a0a1.IsContinuousLinearMap_rule _ _ (hf.linear x) (hg.linear x)

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
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  obtain ⟨dg, hdg, htg⟩ := hg.deriv
  constructor
  case val => intro x dx; simp [hf.val, hg.val]
  case deriv =>
    refine ⟨fun x => df x - dg x, fun x => (hdf x).sub (hdg x), ?_⟩
    intro x dx w
    simp only [sub_apply, sub_tmul, htf, htg]
  case linear =>
    intro x
    exact HSub.hSub.arg_a0a1.IsContinuousLinearMap_rule _ _ (hf.linear x) (hg.linear x)

@[data_synth]
theorem Neg.neg.arg_a0.HasVecFwdFDeriv_comp_rule
    {f : X → Y} {f'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => - f x)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        (- y, -dy)) := by
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  constructor
  case val => intro x dx; simp [hf.val]
  case deriv =>
    refine ⟨fun x => - df x, fun x => (hdf x).neg, ?_⟩
    intro x dx w
    simp only [neg_apply, neg_tmul, htf]
  case linear =>
    intro x
    exact Neg.neg.arg_a0.IsContinuousLinearMap_rule _ (hf.linear x)


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
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  obtain ⟨dg, hdg, htg⟩ := hg.deriv
  have hfval := hf.val
  have hgval := hg.val
  constructor
  case val => intro x dx; simp [hfval, hgval]
  case deriv =>
    refine ⟨fun x => f x • dg x + (df x).smulRight (g x), fun x => (hdf x).smul (hdg x), ?_⟩
    intro x dx w
    show ((f x • dg x) dx + (df x) dx • g x) ⊗[𝕜] w = _
    simp only [hfval, hgval, ← htf x dx w, ← htg x dx w, add_tmul, smul_tmul,
      smul_apply, tmul_scalar_left, tmul_smul]
  case linear =>
    intro x
    have h1 := hf.linear x
    have h2 := hg.linear x
    simp only [hfval, hgval]
    fun_prop

@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasVecFwdFDeriv_rule_nat
    {g : X → Y} {g'} (n : ℕ)
    (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => n • g x)
      (fun x dx =>
        let' (z, dz) := g' x dx
        (n • z, n • dz)) := by
  obtain ⟨dg, hdg, htg⟩ := hg.deriv
  constructor
  case val => intro x dx; simp [hg.val]
  case deriv =>
    refine ⟨fun x => n • dg x, fun x => (hdg x).const_smul n, ?_⟩
    intro x dx w
    simp only [smul_apply, nsmul_tmul, htg]
  case linear =>
    intro x
    have h : (fun dx => n • (g' x dx).2) = fun dx => ((n:𝕜) • (g' x dx).2) := by
      funext dx; rw [Nat.cast_smul_eq_nsmul]
    rw [h]
    exact HSMul.hSMul.arg_a1.IsContinuousLinearMap_rule _ _ (hg.linear x)

@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasVecFwdFDeriv_rule_int
    {g : X → Y} {g'} (n : ℤ)
    (hg : HasVecFwdFDeriv 𝕜 W g g') :
    HasVecFwdFDeriv 𝕜 W
      (fun x => n • g x)
      (fun x dx =>
        let' (z, dz) := g' x dx
        (n • z, n • dz)) := by
  obtain ⟨dg, hdg, htg⟩ := hg.deriv
  constructor
  case val => intro x dx; simp [hg.val]
  case deriv =>
    refine ⟨fun x => n • dg x, fun x => (hdg x).const_smul n, ?_⟩
    intro x dx w
    simp only [smul_apply, zsmul_tmul, htg]
  case linear =>
    intro x
    have h : (fun dx => n • (g' x dx).2) = fun dx => ((n:𝕜) • (g' x dx).2) := by
      funext dx; rw [Int.cast_smul_eq_zsmul]
    rw [h]
    exact HSMul.hSMul.arg_a1.IsContinuousLinearMap_rule _ _ (hg.linear x)

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
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  obtain ⟨dg, hdg, htg⟩ := hg.deriv
  have hfval := hf.val
  have hgval := hg.val
  constructor
  case val => intro x dx; simp [hfval, hgval]
  case deriv =>
    refine ⟨fun x => f x • dg x + g x • df x, fun x => (hdf x).mul (hdg x), ?_⟩
    intro x dx w
    show (f x • (dg x) dx + g x • (df x) dx) ⊗[𝕜] w = _
    simp only [hfval, hgval, ← htf x dx w, ← htg x dx w, tmul_scalar_left, add_smul, smul_smul,
      smul_eq_mul]
  case linear =>
    intro x
    have h1 := hf.linear x
    have h2 := hg.linear x
    simp only [hfval, hgval]
    fun_prop

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


-- note: the statement below is not provable as it stands, the sign of the derivative is flipped.
-- The quotient rule gives `(z * dy - y * dz) / z^2`, i.e. `iz^2 • (z ⊗ dy - y ⊗ dz)`,
-- compare with `HDiv.hDiv.arg_a0a1.HasFwdFDeriv_comp_rule` in `SciLean/AD/HasFwdFDeriv.lean`.
-- The corrected statement is proved below, after the rule for the inverse it is derived from.
-- set_option linter.overlappingInstances false in
-- @[data_synth]
-- theorem HDiv.hDiv.arg_a0a1.HasVecFwdFDeriv_comp_rule
--     [SMul (𝕜ᵐᵒᵖ) W] [Star W]
--     {f g : X → 𝕜} {f' g'}
--     (hf : HasVecFwdFDeriv 𝕜 W f f') (hg : HasVecFwdFDeriv 𝕜 W g g')
--     (hg' : ∀ x, g x ≠ 0) :
--     HasVecFwdFDeriv 𝕜 W
--       (fun x => f x / g x)
--       (fun x dx =>
--         let' (y, dy) := f' x dx;
--         let' (z, dz) := g' x dx;
--         let iz := z⁻¹
--         (iz • y, iz^2 • (y ⊗ dz - z ⊗ dy))) := by
--   sorry_proof

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
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  have hfval := hf.val
  constructor
  case val => intro x dx; simp [hfval, div_eq_inv_mul]
  case deriv =>
    refine ⟨fun x => c⁻¹ • df x, fun x => ?_, ?_⟩
    · simp only [div_eq_mul_inv]
      refine ((hdf x).mul (hasFDerivAt_const c⁻¹ x)).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun dx => ?_
      simp
    · intro x dx w
      show (c⁻¹ • (df x) dx) ⊗[𝕜] w = _
      simp only [← htf x dx w, tmul_scalar_left, smul_smul, smul_eq_mul]
  case linear =>
    intro x
    exact HSMul.hSMul.arg_a1.IsContinuousLinearMap_rule _ _ (hf.linear x)


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
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  have hfval := hf.val
  constructor
  case val => intro x dx; simp [hfval]
  case deriv =>
    refine ⟨fun x => (-(f x ^ 2)⁻¹) • df x, fun x => ?_, ?_⟩
    · have h := HasFDerivAt.comp (𝕜:=𝕜) x ((hasDerivAt_inv (hf' x)).hasFDerivAt) (hdf x)
      refine h.congr_fderiv (ContinuousLinearMap.ext fun dx => ?_)
      simp [smul_eq_mul, mul_comm]
    · intro x dx w
      show ((-(f x ^ 2)⁻¹) • (df x) dx) ⊗[𝕜] w = _
      simp only [hfval, ← htf x dx w, tmul_scalar_left, smul_smul, smul_eq_mul, inv_pow, neg_mul,
        neg_smul]
  case linear =>
    intro x
    simp only [hfval]
    exact HSMul.hSMul.arg_a1.IsContinuousLinearMap_rule _ _ (hf.linear x)

set_option linter.overlappingInstances false in
/-- Forward mode derivative of division.

This is the original `HDiv.hDiv.arg_a0a1.HasVecFwdFDeriv_comp_rule` with the sign of the
derivative corrected; it is derived from the rules for multiplication and for the inverse. -/
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
        (iz • y, iz^2 • (z ⊗ dy - y ⊗ dz))) := by
  have h := HMul.hMul.arg_a0a1.HasVecFwdFDeriv_comp_rule hf
              (HInv.hInv.arg_a0.HasVecFwdFDeriv_comp_rule hg hg')
  have hgval := hg.val
  have hfun :
      (fun x dx =>
        let' (y, dy) := f' x dx;
        let' (z, dz) := g' x dx;
        let iz := z⁻¹
        (iz • y, iz^2 • (z ⊗ dy - y ⊗ dz)))
      =
      (fun (x : X) (dx : X ⊗ W) =>
        let' (y, dy) := f' x dx;
        let' (z, dz) :=
          (let' (z, dz) := g' x dx
           let iz := z⁻¹
           (iz, - iz^2 • dz));
        (y * z, y ⊗ dz + z ⊗ dy)) := by
    funext x dx
    have hz' : (g' x dx).1 ≠ 0 := by rw [hgval]; exact hg' x
    refine Prod.ext ?_ ?_
    · show (g' x dx).1⁻¹ • (f' x dx).1 = (f' x dx).1 * (g' x dx).1⁻¹
      rw [smul_eq_mul, mul_comm]
    · show ((g' x dx).1⁻¹)^2 • ((g' x dx).1 ⊗ (f' x dx).2 - (f' x dx).1 ⊗ (g' x dx).2)
           = (f' x dx).1 ⊗ (-((g' x dx).1⁻¹)^2 • (g' x dx).2)
             + (g' x dx).1⁻¹ ⊗ (f' x dx).2
      have hzz : (g' x dx).1⁻¹^2 * (g' x dx).1 = (g' x dx).1⁻¹ := by
        field_simp [pow_two]
      simp only [tmul_scalar_left, smul_sub, smul_smul]
      rw [hzz, mul_neg, neg_smul, mul_comm ((f' x dx).1)]
      abel
  rw [hfun]
  simpa only [div_eq_mul_inv] using h

@[data_synth]
theorem HPow.hPow.arg_a0.HasVecFwdFDeriv_rule_nat
    {f : X → 𝕜} {f'}
    (hf : HasVecFwdFDeriv 𝕜 W f f') (n : ℕ) :
    HasVecFwdFDeriv 𝕜 W
      (fun x => (f x)^n)
      (fun x dx =>
        let' (y, dy) := f' x dx;
        (y^n,  n • y^(n-1) • dy)) := by
  obtain ⟨df, hdf, htf⟩ := hf.deriv
  have hfval := hf.val
  constructor
  case val => intro x dx; simp [hfval]
  case deriv =>
    refine ⟨fun x => (n • f x ^ (n-1)) • df x, fun x => (hdf x).pow n, ?_⟩
    intro x dx w
    show ((n • f x ^ (n-1)) • (df x) dx) ⊗[𝕜] w = _
    simp only [hfval, ← htf x dx w, tmul_scalar_left, smul_smul, smul_eq_mul, nsmul_eq_mul,
      mul_assoc]
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
  case linear =>
    intro x
    simp only [hfval]
    have h : (fun dx => n • (f x)^(n-1) • (f' x dx).2)
           = fun dx => ((n:𝕜) * (f x)^(n-1)) • (f' x dx).2 := by
      funext dx; rw [mul_smul, Nat.cast_smul_eq_nsmul]
    rw [h]
    exact HSMul.hSMul.arg_a1.IsContinuousLinearMap_rule _ _ (hf.linear x)

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
  choose df hdf htf using fun i => (hf i).deriv
  constructor
  case val =>
    intro x dx
    simp only [IndexType.sum_eq_finset_sum, Prod.fst_sum, (hf _).val]
  case deriv =>
    refine ⟨fun x => ∑ i : I, df i x, fun x => ?_, ?_⟩
    · simp only [IndexType.sum_eq_finset_sum]
      exact HasFDerivAt.fun_sum (fun i _ => hdf i x)
    · intro x dx w
      rw [IndexType.sum_eq_finset_sum, Prod.snd_sum, sum_apply]
      have hlin : (∑ i : I, df i x dx) ⊗ w = ∑ i : I, (df i x dx ⊗ w : YW) :=
        map_sum (IsLinearMap.mk' _ (tmul.arg_y.IsLinearMap_rule (R:=𝕜) (YX:=YW) w))
          (fun i => df i x dx) Finset.univ
      rw [hlin]
      exact Finset.sum_congr rfl fun i _ => htf i x dx w
  case linear =>
    intro x
    have he : (fun dx : XW => (∑ᴵ i, f' i x dx).2)
        = ⇑(∑ i : I, ContinuousLinearMap.mk' 𝕜 (fun dx : XW => (f' i x dx).2) ((hf i).linear x)) := by
      funext dx; rw [IndexType.sum_eq_finset_sum, Prod.snd_sum, sum_apply]; rfl
    rw [he]
    fun_prop



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
