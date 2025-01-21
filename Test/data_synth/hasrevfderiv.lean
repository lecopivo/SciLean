import SciLean.Tactic.DataSynth.HasRevFDeriv

open SciLean


variable {R : Type*} [RCLike R]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace R Z] [CompleteSpace Z]
  {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace R X₁] [CompleteSpace X₁]
  {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace R X₂] [CompleteSpace X₂]

variable (x₀ : X)

/-- info: HasRevFDeriv R (fun x => x) fun x => (x, fun dx => dx) : Prop -/
#guard_msgs in
#check (HasRevFDeriv R (fun x : X => x) _) rewrite_by data_synth

/-- info: HasRevFDeriv R (fun x => x₀) fun x => (x₀, fun x => 0) : Prop -/
#guard_msgs in
#check (HasRevFDeriv R (fun _ : X => x₀) _) rewrite_by data_synth

/--
info: HasRevFDeriv R
  (fun x =>
    let x_1 := 42;
    x)
  fun x => (x, fun dx => dx) : Prop
-/
#guard_msgs in
#check (HasRevFDeriv R (fun x : R => let _ : Nat := 42;x) _) rewrite_by data_synth

/--
info: HasRevFDeriv R
  (let c := 42;
  fun x => c * x)
  fun x =>
  let ydy₁ := 42;
  (ydy₁ * x, fun dx =>
    let dy := 0;
    (starRingEnd R) x • dy + (starRingEnd R) ydy₁ • dx) : Prop
-/
#guard_msgs in
#check (HasRevFDeriv R (let c : R := 42; fun x : R => (c:R)*x) _) rewrite_by data_synth


/--
info: HasRevFDeriv R
  (fun x =>
    let y := x ^ 2;
    y ^ 2 * x)
  fun x =>
  let ydy₁ := x ^ 2;
  let x₁ := ydy₁ ^ 2;
  let zdz₁ := x₁ * x;
  (zdz₁, fun dz =>
    let dz_1 := (↑2 * (starRingEnd R) ydy₁ ^ (2 - 1)) • dz;
    let dy₂ := 0;
    let dz₁ := 0;
    let dyx := (starRingEnd R) x • (dz_1, dy₂) + (starRingEnd R) x₁ • (dz₁, dz);
    let dx := dyx.2;
    let dy := dyx.1;
    let dx' := (↑2 * (starRingEnd R) x ^ (2 - 1)) • dy;
    dx + dx') : Prop
-/
#guard_msgs in
#check (HasRevFDeriv R (fun x : R => let y := x^2; (y^2)*x) _) rewrite_by data_synth


/--
info: HasRevFDeriv R
  (fun x =>
    let y := x₀ + x;
    x + y)
  fun x =>
  let ydy₁ := x₀ + x;
  let zdz₁ := x + ydy₁;
  (zdz₁, fun dz =>
    let dy₁ := 0;
    let dz₂ := 0;
    let dyx := (dy₁, dz) + (dz, dz₂);
    let dx := dyx.2;
    let dy := dyx.1;
    let dy_1 := 0;
    let dx' := dy_1 + dy;
    dx + dx') : Prop
-/
#guard_msgs in
#check (HasRevFDeriv R (fun x : X => let y := x₀+x; x+y) _) rewrite_by data_synth


/--
info: HasRevFDeriv R
  (fun x =>
    let x_1 := x;
    x)
  fun x => (x, fun dx => dx) : Prop
-/
#guard_msgs in
#check (HasRevFDeriv R (fun x : X => let _ := x; x) _) rewrite_by data_synth
