import SciLean.Analysis.Calculus.HasRevFDeriv

open SciLean


variable {R : Type*} [RCLike R]
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {Z : Type*} [NormedAddCommGroup Z] [AdjointSpace R Z] [CompleteSpace Z]
  {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace R X₁] [CompleteSpace X₁]
  {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace R X₂] [CompleteSpace X₂]

variable (x₀ : X)

/-- info: HasRevFDeriv R (fun x => x) fun x => (x, fun dy => dy) : Prop -/
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
  fun x => (x, fun dy => dy) : Prop
-/
#guard_msgs in
#check (HasRevFDeriv R (fun x : R => let _ : Nat := 42;x) _) rewrite_by data_synth

/--
info: HasRevFDeriv R
  (let c := 42;
  fun x => c * x)
  fun x =>
  have x₁ := 42;
  (x₁ * x, fun dy =>
    have dy₁ := (starRingEnd R) x₁ • dy;
    dy₁) : Prop
-/
#guard_msgs in
#check (HasRevFDeriv R (let c : R := 42; fun x : R => (c:R)*x) _) rewrite_by data_synth


/--
info: HasRevFDeriv R
  (fun x =>
    let y := x ^ 2;
    y ^ 2 * x)
  fun x =>
  have x₁ := x ^ 2;
  have x₁_1 := x₁ ^ 2;
  have x₁_2 := x₁_1 * x;
  (x₁_2, fun dz =>
    have dy₁ := (starRingEnd R) x₁_1 • dz;
    have dy₂ := (starRingEnd R) x • dz;
    have dx₁ := 0;
    have dx := dx₁ + ↑2 * (starRingEnd R) x₁ ^ (2 - 1) • dy₂;
    have dx := dy₁ + ↑2 * (starRingEnd R) x ^ (2 - 1) • dx;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDeriv R (fun x : R => let y := x^2; (y^2)*x) _) rewrite_by data_synth


/--
info: HasRevFDeriv R
  (fun x =>
    let y := x₀ + x;
    x + y)
  fun x =>
  have x₁ := x₀ + x;
  have x₁ := x + x₁;
  (x₁, fun dz =>
    have dx₁ := 0;
    have dx₁ := dx₁ + dz;
    have dx := dz + dx₁;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDeriv R (fun x : X => let y := x₀+x; x+y) _) rewrite_by data_synth


/--
info: HasRevFDeriv R
  (fun x =>
    let x_1 := x;
    x)
  fun x => (x, fun dy => dy) : Prop
-/
#guard_msgs in
#check (HasRevFDeriv R (fun x : X => let _ := x; x) _) rewrite_by data_synth
