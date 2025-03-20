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


noncomputable
def jac (R) [RCLike R]
    {X} [NormedAddCommGroup X] [AdjointSpace R X]
    {Y} [NormedAddCommGroup Y] [AdjointSpace R Y]
    {YX} [NormedAddCommGroup YX] [AdjointSpace R YX]
    {XX} [NormedAddCommGroup XX] [AdjointSpace R XX]
    [TensorProductType R Y X YX] [TensorProductType R X X XX] [TensorProductSelf R X XX]
    (f : X → Y) (x : X) : YX :=
  (vecFwdFDeriv R X f x 𝐈[R,X]).2


/--
info: fun x =>
  let yn := ‖x‖₂[Float];
  yn⁻¹ • x : Float^[3] → Float^[3]
-/
#guard_msgs in
#check (jac Float (fun x : Float^[3] => ‖x‖₂))
  rewrite_by
    unfold jac
    lsimp -zeta (disch:=unsafeAD) only [simp_core, ↓vecFwdFDeriv_simproc]



/--
info: fun x => ‖x‖₂[Float]⁻¹ • 𝐈 + x ⊗ (-(‖x‖₂²⁻¹ • ‖x‖₂[Float]⁻¹ • x)) : Float^[3] → Float^[3, 3]
-/
#guard_msgs in
#check (jac Float (jac Float (fun x : Float^[3] => ‖x‖₂)))
  rewrite_by
    unfold jac
    conv in (occs := 2) (vecFwdFDeriv _ _ _) =>
      lsimp -zeta (disch:=unsafeAD) only [simp_core, ↓vecFwdFDeriv_simproc]
    conv in (occs := 1) (vecFwdFDeriv _ _ _) =>
      enter [x]
      simp -zeta
      lsimp -zeta (disch:=unsafeAD) only [simp_core, ↓vecFwdFDeriv_simproc]
    simp


/--
info: fun x =>
  (vecFwdFDeriv Float (Float^[3]) (fun x => ‖x‖₂[Float]⁻¹ • 𝐈 + x ⊗ (-(‖x‖₂²⁻¹ • ‖x‖₂[Float]⁻¹ • x))) x
      𝐈).2 : Float^[3] → Float^[[3, 3], 3]
-/
#guard_msgs in
#check (jac Float (jac Float (jac Float (fun x : Float^[3] => ‖x‖₂))))
  rewrite_by
    unfold jac
    conv in (occs := 3) (vecFwdFDeriv _ _ _) =>
      lsimp -zeta (disch:=unsafeAD) only [simp_core, ↓vecFwdFDeriv_simproc]
    simp -zeta
    conv in (occs := 2) (vecFwdFDeriv _ _ _) =>
      enter [x]
      lsimp -zeta (disch:=unsafeAD) only [simp_core, ↓vecFwdFDeriv_simproc]
    simp

    conv in (occs := 1) (vecFwdFDeriv _ _ _) =>
      enter [x]
      simp -zeta
      lsimp -zeta (disch:=unsafeAD) only [simp_core, ↓vecFwdFDeriv_simproc]
    simp



/--
info: fun x =>
  let x₁ := ‖x‖₂²;
  let x₂ := 2 • x;
  let x₁_1 := x₁ • x;
  let x₂ := x₁ • 𝐈 + x ⊗ x₂;
  let y_dz := tmulAssoc.symm (x ⊗ x₂);
  let dy_z := tmulAssoc.symm (tswapRight (tmulAssoc (𝐈 ⊗ x₁_1)));
  y_dz + dy_z : Float^[3] → Float^[[3, 3], 3]
-/
#guard_msgs in
#check (jac Float (fun x : Float^[3] => x ⊗ (‖x‖₂²•x)))
  rewrite_by
    unfold jac
    lsimp -zeta (disch:=unsafeAD) only [simp_core, ↓vecFwdFDeriv_simproc]
