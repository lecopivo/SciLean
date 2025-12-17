import SciLean
import SciLean.Data.ArrayOperations.Operations.MapIdxMonoAcc

open SciLean


set_default_scalar Float


noncomputable
def foo := ((<∂ (x:= ⊞[1.0,2,3,4]), IndexType.fold .full (init:=1.0) (fun i s => s * x[i]))).2 1


-- Note: In Lean 4.26, #eval on noncomputable defs fails even after rewrite_by
-- The rewrite produces the correct value but computability check happens first
/-- error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'adjoint', which is 'noncomputable' -/
#guard_msgs in
#eval foo
  rewrite_by
    unfold foo
    lsimp -zeta only [simp_core, ↓revFDeriv_simproc]

attribute [data_synth high] SciLean.IndexType.fold.arg_initf.HasRevFDeriv_scalar_rule


/-- error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'adjoint', which is 'noncomputable' -/
#guard_msgs in
#eval foo
  rewrite_by
    unfold foo
    lsimp -zeta only [simp_core, ↓revFDeriv_simproc]


/--
info: fun x =>
  let x₁ := x + x;
  let x₁_1 := ⊞ i => x₁[i] ^ 2;
  let r := ArrayOps.mapIdxMonoAcc (fun idx xi x => x * xi) (fun idx => x₁_1[idx]) x₁;
  (r, fun dz =>
    let dw :=
      IndexType.fold IndexType.Range.full 0 fun i dw =>
        let xi := x₁[i];
        let dyi := dz[i];
        let x₁ := x₁_1[i];
        let dy₁ := xi * dyi;
        let dy₂ := x₁ * dyi;
        let dx₁ := dw.1;
        let dx₂ := dw.2;
        let xi := dx₁[i];
        let x := setElem dx₁ i (xi + dy₁) True.intro;
        let xi := dx₂[i];
        let x_1 := setElem dx₂ i (xi + dy₂) True.intro;
        (x, x_1);
    let dy := dw.1;
    let dx := dw.2;
    let dx :=
      IndexType.fold IndexType.Range.full dx fun i dx =>
        let x₁ := x₁[i];
        let dxi := dy[i];
        let xi := dx[i];
        let x := setElem dx i (xi + 2 * (x₁ * dxi)) True.intro;
        x;
    let dx := dx + dx;
    dx) : Float^[10] → Float^[10] × (Float^[10] → Float^[10])
-/
#guard_msgs in
#check (<∂ x : Float^[10],
     let x := x + x
     let y := ⊞ i => x[i]^2
     x.rmap2 (·*·) y)
  rewrite_by
    unfold DataArrayN.rmap2
    lsimp -zeta only [simp_core, ↓revFDeriv_simproc]


/--
info: fun w =>
  let xs := w.1;
  let r :=
    ArrayOps.mapIdxMonoAcc
      (fun i x y =>
        let i := i.1;
        y ^ 2 * w.2[i])
      (fun x => ()) xs;
  (r, fun dy =>
    let dw :=
      IndexType.fold IndexType.Range.full 0 fun i dw =>
        let xi := xs[i];
        let dyi := dy[i];
        let x₁ := xi ^ 2;
        let x₁_1 := w.2;
        let x₁_2 := x₁_1[i.1];
        let dy₁ := x₁ * dyi;
        let dy₂ := x₁_2 * dyi;
        let x' := setElem 0 i.1 dy₁ True.intro;
        let dx' := dw.1;
        let dy' := dw.2;
        let dx₂ := dy' + x';
        let dx := 2 * (xi * dy₂);
        let xi := dx'[i];
        let x := setElem dx' i (xi + dx) True.intro;
        (x, dx₂);
    dw) : Float^[10] × Float^[10] → Float^[10] × (Float^[10] → Float^[10] × Float^[10])
-/
#guard_msgs in
#check (<∂ x : Float^[10]×Float^[10],
     let' (x,y) := x
     x.rmapIdx (fun i _ xi => xi^2*y[i]))
  rewrite_by
    unfold DataArrayN.rmap2
    unfold DataArrayN.rmapIdx
    unfold ArrayOps.mapIdxMono
    -- unfold ArrayOps.mapIdxMono2
    lsimp only
    lsimp -zeta only [simp_core, ↓revFDeriv_simproc,fromIdx]


/--
info: fun w =>
  let xs := w.1;
  let r := ArrayOps.mapIdxMonoAcc (fun idx xi x => x / xi) (fun idx => w.2[idx]) xs;
  (r, fun dy =>
    let dw :=
      IndexType.fold IndexType.Range.full 0 fun i dw =>
        let xi := xs[i];
        let dyi := dy[i];
        let x₁ := w.2;
        let x₁ := x₁[i];
        let s := (x₁ ^ 2)⁻¹;
        let dy₁ := -(s * (xi * dyi));
        let dy₂ := s * (x₁ * dyi);
        let dx₁ := dw.2;
        let dx₂ := dw.1;
        let xi := dx₁[i];
        let x := setElem dx₁ i (xi + dy₁) True.intro;
        let xi := dx₂[i];
        let x_1 := setElem dx₂ i (xi + dy₂) True.intro;
        (x_1, x);
    dw) : Float^[10] × Float^[10] → Float^[10] × (Float^[10] → Float^[10] × Float^[10])
-/
#guard_msgs in
#check (<∂ x : Float^[10]×Float^[10],
       x.1.rmap2 (·/·) x.2)
  rewrite_by
    unfold DataArrayN.rmap2; dsimp
    lsimp -zeta (disch:=unsafeAD) only [simp_core, ↓revFDeriv_simproc,fromIdx]



-- This code is bad because of `setElem (0 : Float^[10]) i dyi`
-- This is the reason why `mapIdxMono2 exists
-- If you change `(fun i zi => x[i]*y[i] + zi)` to `(fun i zi => x[i]*y[i] + zi + x[i])` then
-- you get bad code.
/--
info: fun x =>
  let x₁ := x.1;
  let x₁_1 := x.2;
  let r := ArrayOps.mapIdxMonoAcc (fun i x y => x₁[i] + y) (fun x => ()) x₁_1;
  (r, fun dz =>
    let dw :=
      IndexType.fold IndexType.Range.full 0 fun i dw =>
        let dyi := dz[i];
        let x' := setElem 0 i dyi True.intro;
        let dx' := dw.1;
        let dy' := dw.2;
        let dx₂ := dy' + x';
        let xi := dx'[i];
        let x := setElem dx' i (xi + dyi) True.intro;
        (x, dx₂);
    let dx₁ := dw.1;
    let dx₂₁ := dw.2;
    (dx₂₁, dx₁)) : Float^[10] × Float^[10] → Float^[10] × (Float^[10] → Float^[10] × Float^[10])
-/
#guard_msgs in
#check (<∂ x : Float^[10]×Float^[10],
     let' (x,y) := x
     ArrayOps.mapIdxMono (fun i xi => x[i] + xi) y)
  rewrite_by
    lsimp -zeta only [simp_core, ↓revFDeriv_simproc,fromIdx]


-- for some unknown reason to me this actually produces good code without using `mapIdxMono2`
-- I don't fully understand why
/--
info: fun x =>
  let x₁ := x.1;
  let x₁_1 := x.2;
  let r := ArrayOps.mapIdxMonoAcc (fun i x y => x₁[i] * x₁_1[i] + y) (fun x => ()) x₁_1;
  (r, fun dz =>
    let dw :=
      IndexType.fold IndexType.Range.full 0 fun i dw =>
        let dyi := dz[i];
        let x₁ := x₁[i];
        let x₁_2 := x₁_1[i];
        let dy₁ := x₁ * dyi;
        let dy₂ := x₁_2 * dyi;
        let dx₁ := dw.1;
        let dx₂ := dw.2;
        let xi := dx₁[i];
        let x := setElem dx₁ i (xi + dy₁) True.intro;
        let xi := dx₂[i];
        let x_1 := setElem dx₂ i (xi + dy₂) True.intro;
        let xi := x[i];
        let x := setElem x i (xi + dyi) True.intro;
        (x, x_1);
    let dx₁ := dw.1;
    let dx₂₁ := dw.2;
    (dx₂₁, dx₁)) : Float^[10] × Float^[10] → Float^[10] × (Float^[10] → Float^[10] × Float^[10])
-/
#guard_msgs in
#check (<∂ x : Float^[10]×Float^[10],
       let' (x,y) := x
       ArrayOps.mapIdxMono (fun i zi => x[i]*y[i] + zi) y)
  rewrite_by
    lsimp -zeta only [simp_core, ↓revFDeriv_simproc,fromIdx]


/--
info: fun x =>
  let x₁ := x.1;
  let x₁₁ := x.2.1;
  let x₁₂ := x.2.2;
  let r := ArrayOps.mapIdxMonoAcc (fun x x_1 zi => x_1.1 * x_1.2 + zi) (fun i => (x₁[i], x₁₁[i])) x₁₂;
  (r, fun dz =>
    let dw :=
      IndexType.fold IndexType.Range.full 0 fun i dw =>
        let dyi := dz[i];
        let x₁ := x₁[i];
        let x₁_1 := x₁₁[i];
        let dy₁ := x₁ * dyi;
        let dy₂ := x₁_1 * dyi;
        let dx₁₁ := dw.2.1;
        let dx₁₂ := dw.2.2;
        let dx₂ := dw.1;
        let xi := dx₁₂[i];
        let x := setElem dx₁₂ i (xi + dy₂) True.intro;
        let xi := dx₁₁[i];
        let x_1 := setElem dx₁₁ i (xi + dy₁) True.intro;
        let xi := dx₂[i];
        let x_2 := setElem dx₂ i (xi + dyi) True.intro;
        (x_2, x_1, x);
    let dx₁ := dw.1;
    let dx₂₁ := dw.2.1;
    let dx₂₂₁ := dw.2.2;
    (dx₂₂₁, dx₂₁,
      dx₁)) : Float^[10] × Float^[10] × Float^[10] → Float^[10] × (Float^[10] → Float^[10] × Float^[10] × Float^[10])
-/
#guard_msgs in
#check (<∂ x : Float^[10]×Float^[10]×Float^[10],
       let' (x,y,z) := x
       ArrayOps.mapIdxMonoAcc (fun _ (xi,yi) zi => xi*yi + zi) (fun i => (x[i],y[i])) z)
  rewrite_by
    unfold DataArrayN.rmap2
    lsimp -zeta (disch:=unsafeAD) only [simp_core, ↓revFDeriv_simproc,fromIdx]
