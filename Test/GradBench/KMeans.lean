import SciLean

open SciLean Scalar

set_default_scalar Float

def objective {n k d : ℕ} (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) :=
  ∑ᴵ i, minᴵ j, ‖points[i] - centroids[j]‖₂²


noncomputable def direction {n k d : ℕ} [NeZero k] (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
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
  have x :=
    ∂> (c:=centroids;⊞ i => ⊞ j => 1),
      have x := <∂ (centroids:=c), ∑ᴵ i, minᴵ j, ‖points[i] - centroids[j]‖₂²;
      have y := x.1;
      have df := x.2;
      (y, df 1);
  have J := x.1.2;
  have Hdiag := x.2.2;
  DataArrayN.rmap2 (fun x1 x2 => x1 / x2) J Hdiag
-/
#guard_msgs in
#print direction


def objective' {n k d : ℕ} (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) :=
  ∑ᴵ (i : Idx n), minᴵ (j : Idx k), ∑ᴵ (l : Idx d), (points[i,l] - centroids[j,l])^2

noncomputable def direction' {n k d : ℕ} [NeZero k] (points : Float^[d]^[n]) (centroids : Float^[d]^[k]) : Float^[d]^[k] :=
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
  have x :=
    ∂> (c:=centroids;⊞ i => ⊞ j => 1.0),
      have x := <∂ (centroids:=c), ∑ᴵ i, minᴵ j, ∑ᴵ l, (points[(i, l)] - centroids[(j, l)]) ^ 2;
      have y := x.1;
      have df := x.2;
      (y, df 1);
  have J := x.1.2;
  have Hdiag := x.2.2;
  DataArrayN.rmap2 (fun x1 x2 => x1 / x2) J Hdiag
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
