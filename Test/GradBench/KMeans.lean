import SciLean

open SciLean Scalar

set_default_scalar Float

def objective {n k d : ℕ} (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) :=
  ∑ᴵ i, minᴵ j, ‖points[i] - centroids[j]‖₂²


def direction {n k d : ℕ} [NeZero k] (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
  (let' ((_a,J),(_b,Hdiag)) :=
    ∂> (c:=centroids;⊞ (i : Idx k) => ⊞ (j : Idx d) =>(1:Float)),
      let' (y,df) := <∂ (objective points) c
      (y,df 1)
  J.rmap2 (·/·) Hdiag)
rewrite_by
  unfold objective
  autodiff (disch:=unsafeAD)


/--
info: def direction : {n k d : ℕ} → [NeZero k] → Float^[d]^[n] → Float^[d]^[k] → Float^[d]^[k] :=
fun {n k d} [NeZero k] points centroids =>
  let x :=
    IndexType.fold IndexType.Range.full (0, 0) fun i xdx =>
      let x := xdx.1;
      let dx := xdx.2;
      let a := argMinᴵ j, ‖points[i] - centroids[j]‖₂²;
      let ydy₁ := centroids[a];
      let ydy₂ := ⊞ j => 1;
      let x₁ := points[i];
      let ydy₁ := x₁ - ydy₁;
      let ydy₂ := -ydy₂;
      let ydy₁ := 2 • ydy₁;
      let ydy₂ := 2 • ydy₂;
      let ydy₁_1 := x[a];
      let ydy₂_1 := dx[a];
      let ydy₁ := -ydy₁;
      let ydy₂ := -ydy₂;
      let ydy₁ := ydy₁_1 + ydy₁;
      let ydy₂ := ydy₂_1 + ydy₂;
      let x₁ := setElem x a ydy₁ True.intro;
      let x₂ := setElem dx a ydy₂ True.intro;
      (x₁, x₂);
  let x_1 := x.1;
  let dx := x.2;
  DataArrayN.rmap2 (fun x1 x2 => x1 / x2) x_1 dx
-/
#guard_msgs in
#print direction


def objective' {n k d : ℕ} (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) :=
  ∑ᴵ (i : Idx n), minᴵ (j : Idx k), ∑ᴵ (l : Idx d), (points[i,l] - centroids[j,l])^2

def direction' {n k d : ℕ} [NeZero k] (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
  (let' ((_a,J),(_b,Hdiag)) :=
    ∂> (c:=centroids;⊞ (i : Idx k) => ⊞ (j : Idx d) => 1.0),
      let' (y,df) := <∂ (objective' points) c
      (y,df 1)
  J.rmap2 (·/·) Hdiag)
rewrite_by
  unfold objective'
  autodiff (disch:=unsafeAD)




/--
info: def direction' : {n k d : ℕ} → [NeZero k] → Float^[d]^[n] → Float^[d]^[k] → Float^[d]^[k] :=
fun {n k d} [NeZero k] points centroids =>
  let x :=
    IndexType.fold IndexType.Range.full (0, 0) fun i xdx =>
      let x := xdx.1;
      let dx := xdx.2;
      let a := argMinᴵ j, ∑ᴵ l, (points[(i, l)] - centroids[(j, l)]) ^ 2;
      let x :=
        IndexType.fold IndexType.Range.full (x, dx) fun i_1 xdx =>
          let x := xdx.1;
          let dx := xdx.2;
          let x₁ := centroids[(a, i_1)];
          let x₁_1 := points[(i, i_1)];
          let ydy₁ := x₁_1 - x₁;
          let ydy₂ := -1.0;
          let ydy₁_1 := x[(a, i_1)];
          let ydy₂_1 := dx[(a, i_1)];
          let x₁ := 2 * ydy₁;
          let x₂ := 2 * ydy₂;
          let ydy₁ := -x₁;
          let ydy₂ := -x₂;
          let ydy₁ := ydy₁_1 + ydy₁;
          let ydy₂ := ydy₂_1 + ydy₂;
          let x₁ := setElem x (a, i_1) ydy₁ True.intro;
          let x₂ := setElem dx (a, i_1) ydy₂ True.intro;
          (x₁, x₂);
      let x_1 := x.1;
      let dx := x.2;
      (x_1, dx);
  let x_1 := x.1;
  let dx := x.2;
  DataArrayN.rmap2 (fun x1 x2 => x1 / x2) x_1 dx
-/
#guard_msgs in
#print direction'



-- def objective_v3 {n k d : ℕ} (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) :=
--   ∑ᴵ (i : Idx n),
--     let dx := ⊞ (j : Idx k) => ∑ᴵ (l : Idx d), (points[i,l] - centroids[j,l])^2
--     minᴵ (j : Idx k), dx[j]

-- set_option trace.Meta.Tactic.data_synth true in
-- def direction_v3 {n k d : ℕ} [NeZero k] (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
--   (let' ((_a,J),(_b,Hdiag)) :=
--     ∂> (c:=centroids;⊞ (i : Idx k) => ⊞ (j : Idx d) => (1:Float)),
--       let' (y,df) := <∂ (objective_v3 points) c
--       (y,df 1)
--   J.rmap2 (·/·) Hdiag)
-- rewrite_by
--   unfold objective_v3
--   autodiff (disch:=unsafeAD)
--   lsimp [Equiv.arrowProdEquivProdArrow]
--   lsimp -zeta (disch:=unsafeAD) only [simp_core,↓revFDeriv_simproc]
--   lsimp -zeta (disch:=unsafeAD) only [simp_core,↓fwdFDeriv_simproc]
