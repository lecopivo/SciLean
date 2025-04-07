import SciLean
-- import SciLean.Analysis.Calculus.HasVecFwdFDeriv
-- import SciLean.Data.DataArray.TensorProduct

open SciLean


set_default_scalar Float


/-- info: fun x dx => (x, dx) : Float^[3] → Float^[3, 3] → Float^[3] × Float^[3, 3] -/
#guard_msgs in
#check (vecFwdFDeriv Float (Float^[3]) (fun x : Float^[3] => x))
  rewrite_by
    lsimp -zeta only [simp_core, ↓vecFwdFDeriv_simproc]

-- todo: make these instances general
instance {I nI} [IndexType I nI]  : SMul Floatᵐᵒᵖ (Float^[I]) := ⟨fun x v => x.1 • v⟩
instance {I nI} [IndexType I nI]  : Star (Float^[I]) := ⟨fun x => x⟩

/--
info: fun x dx => (‖x‖₂², vecMatMulAdd 2 x dx 0 0) : Float^[3] → Float^[3, 3] → Float × Float^[3]
-/
#guard_msgs in
#check (vecFwdFDeriv Float (Float^[3]) (fun x : Float^[3] => ‖x‖₂²))
  rewrite_by
    lsimp -zeta only [simp_core, ↓vecFwdFDeriv_simproc]


/--
info: fun x dx =>
  let x₁ := ⊞[1.0, 2, 3];
  (⟪x, x₁⟫, vecMatMulAdd 1 x₁ dx 0 0) : Float^[3] → Float^[3, 3] → Float × Float^[3]
-/
#guard_msgs in
#check (vecFwdFDeriv Float (Float^[3]) (fun x : Float^[3] => ⟪x, ⊞[1.0,2,3]⟫))
  rewrite_by
    lsimp -zeta only [simp_core, ↓vecFwdFDeriv_simproc]

/--
info: fun x =>
  let x₁ := ⊞[1.0, 2, 3];
  x₁ : Float^[3] → Float^[3]
-/
#guard_msgs in
#check (
    let f' := vecFwdFDeriv Float (Float^[3]) (fun x : Float^[3] => ⟪x, ⊞[1.0,2,3]⟫)
    fun x => (f' x 𝐈).2 )
  rewrite_by
    lsimp -zeta only [simp_core, ↓vecFwdFDeriv_simproc]


/--
info: fun x =>
  let x₁ := ⊞[1.0, 2, 3];
  let x₁_1 := ⟪x, x₁⟫;
  let x₁_2 := ‖x‖₂²;
  let x₂ := 2 • x;
  let x₁_3 := x₁_1 * x₁_2;
  let x₂ := x₁_1 • x₂ + x₁_2 • x₁;
  x₁_3 • 𝐈 + x ⊗ x₂ : Float^[3] → Float^[3, 3]
-/
#guard_msgs in
#check (
    let f' := vecFwdFDeriv Float (Float^[3]) (fun x : Float^[3] => (⟪x, ⊞[1.0,2,3]⟫ * ‖x‖₂²)•x)
    fun x => (f' x 𝐈).2 )
  rewrite_by
    lsimp -zeta only [simp_core, ↓vecFwdFDeriv_simproc]


/--
info: fun x =>
  let yn := ‖x‖₂;
  let iyn := yn⁻¹;
  iyn • x : Float^[3] → Float^[3]
-/
#guard_msgs in
#check (∇ (fun x : Float^[3] => ‖x‖₂))
  rewrite_by
    autodiff (disch:=unsafeAD)


@[simp, simp_core]
theorem tmap_fst_id
  {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
  -- [NormedAddCommGroup X'] [AdjointSpace 𝕜 X']
  -- [NormedAddCommGroup Y'] [AdjointSpace 𝕜 Y']
  {XZ : Type*} [NormedAddCommGroup XZ] [AdjointSpace 𝕜 XZ] [TensorProductType 𝕜 X Z XZ]
  {YZ : Type*} [NormedAddCommGroup YZ] [AdjointSpace 𝕜 YZ] [TensorProductType 𝕜 Y Z YZ]
  -- {XZ'} [NormedAddCommGroup XZ'] [AdjointSpace 𝕜 XZ'] [TensorProductType 𝕜 X' Z XZ']
  -- {YZ'} [NormedAddCommGroup YZ'] [AdjointSpace 𝕜 YZ'] [TensorProductType 𝕜 Y' Z YZ']
  -- (f : X →L[𝕜] X') (g : Y →L[𝕜] X')
  (x : (X×Y)⊗[𝕜]Z) :
  tmap (fun xy : X×Y =>L[𝕜] xy.1) (fun z : Z =>L[𝕜] z) x = x.1 := sorry_proof

@[simp, simp_core]
theorem tmap_snd_id
  {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
  [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
  [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
  -- [NormedAddCommGroup X'] [AdjointSpace 𝕜 X']
  -- [NormedAddCommGroup Y'] [AdjointSpace 𝕜 Y']
  {XZ : Type*} [NormedAddCommGroup XZ] [AdjointSpace 𝕜 XZ] [TensorProductType 𝕜 X Z XZ]
  {YZ : Type*} [NormedAddCommGroup YZ] [AdjointSpace 𝕜 YZ] [TensorProductType 𝕜 Y Z YZ]
  -- {XZ'} [NormedAddCommGroup XZ'] [AdjointSpace 𝕜 XZ'] [TensorProductType 𝕜 X' Z XZ']
  -- {YZ'} [NormedAddCommGroup YZ'] [AdjointSpace 𝕜 YZ'] [TensorProductType 𝕜 Y' Z YZ']
  -- (f : X →L[𝕜] X') (g : Y →L[𝕜] X')
  (x : (X×Y)⊗[𝕜]Z) :
  tmap (fun xy : X×Y =>L[𝕜] xy.2) (fun z : Z =>L[𝕜] z) x = x.2 := sorry_proof

-- @[simp, simp_core]
-- theorem tmap_snd_id
--   {𝕜 X Y Z : Type*} [RCLike 𝕜]
--   [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
--   [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
--   [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
--   -- [NormedAddCommGroup X'] [AdjointSpace 𝕜 X']
--   -- [NormedAddCommGroup Y'] [AdjointSpace 𝕜 Y']
--   {XZ : Type*} [NormedAddCommGroup XZ] [AdjointSpace 𝕜 XZ] [TensorProductType 𝕜 X Z XZ]
--   {YZ : Type*} [NormedAddCommGroup YZ] [AdjointSpace 𝕜 YZ] [TensorProductType 𝕜 Y Z YZ]
--   -- {XZ'} [NormedAddCommGroup XZ'] [AdjointSpace 𝕜 XZ'] [TensorProductType 𝕜 X' Z XZ']
--   -- {YZ'} [NormedAddCommGroup YZ'] [AdjointSpace 𝕜 YZ'] [TensorProductType 𝕜 Y' Z YZ']
--   -- (f : X →L[𝕜] X') (g : Y →L[𝕜] X')
--   (x : (X×Y)⊗[𝕜]Z) :
--   tmap (fun xy : X×Y =>L[𝕜] xy.2) (fun z : Z =>L[𝕜] z) x = x.2 := sorry_proof


/-- info: fun x => -(‖x‖₂ ^ 3)⁻¹ • x ⊗ x + ‖x‖₂⁻¹ • 𝐈 : Float^[3] → Float^[3, 3] -/
#guard_msgs in
#check (∇ (∇ (fun x : Float^[3] => ‖x‖₂)))
  rewrite_by
    autodiff (disch:=unsafeAD)
    simp only [vector_optimize]
    norm_num
    simp only [tmulAdd_spec]




/--
info: fun x =>
  𝐈 ⊗ (-‖x‖₂⁻¹ ^ 2 • ‖x‖₂⁻¹ • x) +
    ((x ⊗
            (-‖x‖₂⁻¹ ^ 2 • (‖x‖₂⁻¹ • 𝐈 + x ⊗ (-‖x‖₂⁻¹ ^ 2 • ‖x‖₂⁻¹ • x)) +
              (‖x‖₂⁻¹ • x) ⊗ (-(2 • ‖x‖₂⁻¹ • -‖x‖₂⁻¹ ^ 2 • ‖x‖₂⁻¹ • x)))).reshape
        ((Idx 3 × Idx 3) × Idx 3) ⋯ +
      (tswapRight ((𝐈 ⊗ (-‖x‖₂⁻¹ ^ 2 • ‖x‖₂⁻¹ • x)).reshape (Idx 3 × Idx 3 × Idx 3) ⋯)).reshape
        ((Idx 3 × Idx 3) × Idx 3) ⋯) : Float^[3] → Float^[[3, 3], 3]
-/
#guard_msgs in
#check (∇ (∇ (∇ (fun x : Float^[3] => ‖x‖₂))))
  rewrite_by
    autodiff +zetaDelta (disch:=unsafeAD)



/--
info: fun x =>
  let x₁ := ‖x‖₂²;
  let x₂ := 2 • x;
  let x₁_1 := x₁ • x;
  let x₂ := x₁ • 𝐈 + x ⊗ x₂;
  let y_dz := (x ⊗ x₂).reshape ((Idx 3 × Idx 3) × Idx 3) ⋯;
  let dy_z := (tswapRight ((𝐈 ⊗ x₁_1).reshape (Idx 3 × Idx 3 × Idx 3) ⋯)).reshape ((Idx 3 × Idx 3) × Idx 3) ⋯;
  y_dz + dy_z : Float^[3] → Float^[[3, 3], 3]
-/
#guard_msgs in
#check (∇ x : Float^[3], x ⊗ (‖x‖₂²•x))
  rewrite_by
    autodiff
