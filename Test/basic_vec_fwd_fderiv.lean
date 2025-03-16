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
info: fun x dx => (‖x‖₂², matHVecMulAdd 2 dx x 0 0) : Float^[3] → Float^[3, 3] → Float × Float^[3]
-/
#guard_msgs in
#check (vecFwdFDeriv Float (Float^[3]) (fun x : Float^[3] => ‖x‖₂²))
  rewrite_by
    lsimp -zeta only [simp_core, ↓vecFwdFDeriv_simproc]


/--
info: fun x dx =>
  let x₁ := ⊞[1.0, 2, 3];
  (⟪x, x₁⟫, matHVecMulAdd 1 dx x₁ 0 0) : Float^[3] → Float^[3, 3] → Float × Float^[3]
-/
#guard_msgs in
#check (vecFwdFDeriv Float (Float^[3]) (fun x : Float^[3] => ⟪x, ⊞[1.0,2,3]⟫))
  rewrite_by
    lsimp -zeta only [simp_core, ↓vecFwdFDeriv_simproc]

-- /--
-- info: fun x =>
--   let x₁ := ⊞[1.0, 2, 3];
--   x₁ : Float^[3] → Float^[3]
-- -/
-- #guard_msgs in
-- #check (
--     let f' := vecFwdFDeriv Float (Float^[3]) (fun x : Float^[3] => ⟪x, ⊞[1.0,2,3]⟫)
--     fun x => (f' x 𝐈).2 )
--   rewrite_by
--     lsimp -zeta only [simp_core, ↓vecFwdFDeriv_simproc]
