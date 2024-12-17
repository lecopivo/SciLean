import SciLean


open SciLean

variable {R : Type} [RCLike R]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace R Z] [CompleteSpace Z]
  {X₁ : Type} [NormedAddCommGroup X₁] [AdjointSpace R X₁] [CompleteSpace X₁]
  {X₂ : Type} [NormedAddCommGroup X₂] [AdjointSpace R X₂] [CompleteSpace X₂]

variable (x₀ : X)

/-- info: HasRevFDerivUpdate R (fun x => x) fun x => (x, fun dx dx₀ => dx₀ + dx) : Prop -/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : X => x) _) rewrite_by data_synth

/-- info: HasRevFDerivUpdate R (fun x => x₀) fun x => (x₀, fun x dx => dx) : Prop -/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun _ : X => x₀) _) rewrite_by data_synth


/--
info: HasRevFDerivUpdate R
  (fun x =>
    let y := x₀ + x;
    x + y)
  fun x =>
  let x₁ := x₀ + x;
  let x₁ := x + x₁;
  (x₁, fun dz dx =>
    let dx₂ := 0;
    let dx₁ := dx + dz;
    let dx₁_1 := dx₂ + dz;
    dx₁ + dx₁_1) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : X => let y := x₀+x; x+y) _) rewrite_by data_synth


/--
info: HasRevFDerivUpdate R
  (fun x =>
    let x_1 := x;
    x)
  fun x =>
  (x, fun dz dx =>
    let dx₂ := 0;
    let dx₁ := dx + dz;
    dx₁ + dx₂) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : X => let _ := x; x) _) rewrite_by data_synth


/--
info: HasRevFDerivUpdate R
  (fun x =>
    let y := x;
    y)
  fun x =>
  (x, fun dz dx =>
    let dx₁ := 0;
    let dx₁ := dx₁ + dz;
    dx + dx₁) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : X => let y := x; y) _) rewrite_by data_synth


variable (f : X → X) (f') (hf : HasRevFDerivUpdate R f f')

/-- info: HasRevFDerivUpdate R (fun x => f x) f' : Prop -/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x => f x) _) rewrite_by data_synth

/--
info: HasRevFDerivUpdate R (fun x => f x + f x) fun x =>
  let x_1 := f' x;
  let y := x_1.1;
  let df := x_1.2;
  let x := f' x;
  let z := x.1;
  let dg := x.2;
  (y + z, fun dy dx =>
    let dx := df dy dx;
    dg dy dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x => (f x)+(f x)) _) rewrite_by data_synth

variable (g : X → Fin n → R) (g' : Fin n → _) (hf : ∀ i, HasRevFDerivUpdate R (g · i) (g' i))
         (i j : Fin n)


/-- info: HasRevFDerivUpdate R (fun x => g x i) (g' i) : Prop -/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x => (g x i)) _) rewrite_by data_synth


/-- info: HasRevFDerivUpdate R f f' : Prop -/
#guard_msgs in
#check (HasRevFDerivUpdate R f _) rewrite_by data_synth



/--
info: HasRevFDerivUpdate R (fun x => x * x * x * x * x) fun x =>
  let x₁ := x * x;
  let x₁_1 := x₁ * x;
  let x₁_2 := x₁_1 * x;
  (x₁_2 * x, fun dy dx =>
    let dy₁ := (starRingEnd R) x • dy;
    let dy₂ := (starRingEnd R) x₁_2 • dy;
    let dy₁_1 := (starRingEnd R) x • dy₁;
    let dy₂_1 := (starRingEnd R) x₁_1 • dy₁;
    let dy₁ := (starRingEnd R) x • dy₁_1;
    let dy₂_2 := (starRingEnd R) x₁ • dy₁_1;
    let dy₁_2 := (starRingEnd R) x • dy₁;
    let dy₂_3 := (starRingEnd R) x • dy₁;
    let dx := dx + dy₁_2;
    let dx := dx + dy₂_3;
    let dx := dx + dy₂_2;
    let dx := dx + dy₂_1;
    let dx := dx + dy₂;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R => x*x*x*x*x) _ )
  rewrite_by
    data_synth


/--
info: HasRevFDerivUpdate R (fun x => x.1 * x.2 * x.1 * x.1 * x.2) fun x =>
  let x₁ := x.1;
  let x₁_1 := x.2;
  let x₁_2 := x₁ * x₁_1;
  let x₁_3 := x.1;
  let x₁_4 := x₁_2 * x₁_3;
  let x₁_5 := x.1;
  let x₁_6 := x₁_4 * x₁_5;
  let x₁_7 := x.2;
  (x₁_6 * x₁_7, fun dy dx =>
    let dy₁ := (starRingEnd R) x₁_7 • dy;
    let dy₂ := (starRingEnd R) x₁_6 • dy;
    let dy₁_1 := (starRingEnd R) x₁_5 • dy₁;
    let dy₂_1 := (starRingEnd R) x₁_4 • dy₁;
    let dy₁ := (starRingEnd R) x₁_3 • dy₁_1;
    let dy₂_2 := (starRingEnd R) x₁_2 • dy₁_1;
    let dy₁_2 := (starRingEnd R) x₁_1 • dy₁;
    let dy₂_3 := (starRingEnd R) x₁ • dy₁;
    let dx₁ := dx.1;
    let dx₂ := dx.2;
    let dx₁ := dx₁ + dy₁_2;
    let dx₁_1 := dx₂ + dy₂_3;
    let dx₁ := dx₁ + dy₂_2;
    let dx₁ := dx₁ + dy₂_1;
    let dx₁_2 := dx₁_1 + dy₂;
    (dx₁, dx₁_2)) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R×R => x.1 * x.2 * x.1 * x.1 * x.2) _) rewrite_by
              data_synth



/--
info: HasRevFDerivUpdate R (fun x => x.1 * x.2.1) fun x =>
  let x₁₁ := x.1;
  let x₁₂ := x.2.1;
  let x₁ := x₁₁ * x₁₂;
  (x₁, fun dy dx =>
    let dx₁₁ := dx.1;
    let dx₁₂ := dx.2.1;
    let dx₂ := dx.2.2;
    let dy₁ := (starRingEnd R) x₁₂ • dy;
    let dy₂ := (starRingEnd R) x₁₁ • dy;
    let dx₁ := dx₁₁ + dy₁;
    let dx₁_1 := dx₁₂ + dy₂;
    (dx₁, dx₁_1, dx₂)) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R×R×R => x.1 * x.2.1) _) rewrite_by
  data_synth


/--
info: HasRevFDerivUpdate R
  (fun x =>
    let y := x;
    y + y)
  fun x =>
  let x₁ := x + x;
  (x₁, fun dz dx =>
    let dx₁ := 0;
    let dx_1 := dx₁ + dz;
    let dx₁ := dx_1 + dz;
    dx + dx₁) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R => let y := x; y+y) _ )
  rewrite_by
    data_synth




/--
info: HasRevFDerivUpdate R (fun x => x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x)
  fun x =>
  let x₁ := x * x;
  let x₁_1 := x₁ * x;
  let x₁_2 := x₁_1 * x;
  let x₁_3 := x₁_2 * x;
  let x₁_4 := x₁_3 * x;
  let x₁_5 := x₁_4 * x;
  let x₁_6 := x₁_5 * x;
  let x₁_7 := x₁_6 * x;
  let x₁_8 := x₁_7 * x;
  let x₁_9 := x₁_8 * x;
  let x₁_10 := x₁_9 * x;
  let x₁_11 := x₁_10 * x;
  let x₁_12 := x₁_11 * x;
  let x₁_13 := x₁_12 * x;
  let x₁_14 := x₁_13 * x;
  let x₁_15 := x₁_14 * x;
  let x₁_16 := x₁_15 * x;
  let x₁_17 := x₁_16 * x;
  let x₁_18 := x₁_17 * x;
  (x₁_18 * x, fun dy dx =>
    let dy₁ := (starRingEnd R) x • dy;
    let dy₂ := (starRingEnd R) x₁_18 • dy;
    let dy₁_1 := (starRingEnd R) x • dy₁;
    let dy₂_1 := (starRingEnd R) x₁_17 • dy₁;
    let dy₁ := (starRingEnd R) x • dy₁_1;
    let dy₂_2 := (starRingEnd R) x₁_16 • dy₁_1;
    let dy₁_2 := (starRingEnd R) x • dy₁;
    let dy₂_3 := (starRingEnd R) x₁_15 • dy₁;
    let dy₁ := (starRingEnd R) x • dy₁_2;
    let dy₂_4 := (starRingEnd R) x₁_14 • dy₁_2;
    let dy₁_3 := (starRingEnd R) x • dy₁;
    let dy₂_5 := (starRingEnd R) x₁_13 • dy₁;
    let dy₁ := (starRingEnd R) x • dy₁_3;
    let dy₂_6 := (starRingEnd R) x₁_12 • dy₁_3;
    let dy₁_4 := (starRingEnd R) x • dy₁;
    let dy₂_7 := (starRingEnd R) x₁_11 • dy₁;
    let dy₁ := (starRingEnd R) x • dy₁_4;
    let dy₂_8 := (starRingEnd R) x₁_10 • dy₁_4;
    let dy₁_5 := (starRingEnd R) x • dy₁;
    let dy₂_9 := (starRingEnd R) x₁_9 • dy₁;
    let dy₁ := (starRingEnd R) x • dy₁_5;
    let dy₂_10 := (starRingEnd R) x₁_8 • dy₁_5;
    let dy₁_6 := (starRingEnd R) x • dy₁;
    let dy₂_11 := (starRingEnd R) x₁_7 • dy₁;
    let dy₁ := (starRingEnd R) x • dy₁_6;
    let dy₂_12 := ⋯ • dy₁_6;
    let dy₁_7 := ⋯;
    ⋯) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R => x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x) _ )
  rewrite_by
    data_synth

/--
info: HasRevFDerivUpdate R (fun x => x.1) fun x =>
  let x₁ := x.1;
  (x₁, fun dy dx =>
    let dx₁ := dx.1;
    let dx₂₁ := dx.2.1;
    let dx₂₂₁ := dx.2.2.1;
    let dx₂₂₂ := dx.2.2.2;
    let dx₁ := dx₁ + dy;
    (dx₁, dx₂₁, dx₂₂₁, dx₂₂₂)) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R×R×R×R => x.1) _) rewrite_by
              data_synth



/--
info: HasRevFDerivUpdate R
  (fun x =>
    let y := x * x;
    let z := y * y;
    z)
  fun x =>
  let x₁ := x * x;
  let x₁_1 := x₁ * x₁;
  (x₁_1, fun dz dx =>
    let dx₁ := 0;
    let dx₁_1 := 0;
    let dx₁_2 := dx₁_1 + dz;
    let dy₁ := (starRingEnd R) x₁ • dx₁_2;
    let dy₂ := (starRingEnd R) x₁ • dx₁_2;
    let dx_1 := dx₁ + dy₁;
    let dx_2 := dx_1 + dy₂;
    let dy₁ := (starRingEnd R) x • dx_2;
    let dy₂ := (starRingEnd R) x • dx_2;
    let dx := dx + dy₁;
    let dx := dx + dy₂;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R =>
            let y := x * x
            let z := y * y
            z) _) rewrite_by
              data_synth


/--
info: HasRevFDerivUpdate R
  (fun x =>
    let x₁ := x * x;
    let x₂ := x * x₁;
    let x₃ := x * x₂;
    let x₄ := x * x₃;
    x * x₄)
  fun x =>
  let x₁ := x * x;
  let x₁_1 := x * x₁;
  let x₁_2 := x * x₁_1;
  let x₁_3 := x * x₁_2;
  let x₁_4 := x * x₁_3;
  (x₁_4, fun dz dx =>
    let dx₁₁ := 0;
    let dx₂ := 0;
    let dx₁₁_1 := 0;
    let dx₁₁_2 := 0;
    let dy₁ := (starRingEnd R) x₁_3 • dz;
    let dy₂ := (starRingEnd R) x • dz;
    let dx₁ := dx + dy₁;
    let dx₁_1 := dx₁₁_2 + dy₂;
    let dy₁ := (starRingEnd R) x₁_2 • dx₁_1;
    let dy₂ := (starRingEnd R) x • dx₁_1;
    let dx₁ := dx₁ + dy₁;
    let dx₁_2 := dx₁₁_1 + dy₂;
    let dy₁ := (starRingEnd R) x₁_1 • dx₁_2;
    let dy₂ := (starRingEnd R) x • dx₁_2;
    let dx₁ := dx₁ + dy₁;
    let dx₁_3 := dx₁₁ + dy₂;
    let dy₁ := (starRingEnd R) x₁ • dx₁_3;
    let dy₂ := (starRingEnd R) x • dx₁_3;
    let dx₁ := dx₁ + dy₁;
    let dx₁_4 := dx₂ + dy₂;
    let dy₁ := (starRingEnd R) x • dx₁_4;
    let dy₂ := (starRingEnd R) x • dx₁_4;
    let dx := dx₁ + dy₁;
    let dx := dx + dy₂;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R =>
            let x₁ := x*x
            let x₂ := x*x₁
            let x₃ := x*x₂
            let x₄ := x*x₃
            x*x₄) _) rewrite_by
              data_synth


/--
info: HasRevFDerivUpdate R
  (fun x =>
    let x₁ := x * x;
    let x₂ := x * x₁;
    let x₃ := x * x₁ * x₂;
    let x₄ := x * x₁ * x₂ * x₃;
    x * x₁ * x₂ * x₃ * x₄)
  fun x =>
  let x₁ := x * x;
  let x₁_1 := x * x₁;
  let x₁_2 := x * x₁;
  let x₁_3 := x₁_2 * x₁_1;
  let x₁_4 := x * x₁;
  let x₁_5 := x₁_4 * x₁_1;
  let x₁_6 := x₁_5 * x₁_3;
  let x₁_7 := x * x₁;
  let x₁_8 := x₁_7 * x₁_1;
  let x₁_9 := x₁_8 * x₁_3;
  let x₁_10 := x₁_9 * x₁_6;
  (x₁_10, fun dz dx =>
    let dy₁ := (starRingEnd R) x₁_6 • dz;
    let dy₂ := (starRingEnd R) x₁_9 • dz;
    let dx₁₁ := 0;
    let dx₁₂₁ := 0;
    let dx₁₂₂₁ := 0;
    let dx₂ := 0;
    let dy₁_1 := (starRingEnd R) x₁_3 • dy₁;
    let dy₂_1 := (starRingEnd R) x₁_8 • dy₁;
    let dy₁ := (starRingEnd R) x₁_1 • dy₁_1;
    let dy₂_2 := (starRingEnd R) x₁_7 • dy₁_1;
    let dy₁_2 := (starRingEnd R) x₁ • dy₁;
    let dy₂_3 := (starRingEnd R) x • dy₁;
    let dx₁ := dx + dy₁_2;
    let dx₁_1 := dx₁₂₂₁ + dy₂_3;
    let dx₁_2 := dx₁₂₁ + dy₂_2;
    let dx₁_3 := dx₁₁ + dy₂_1;
    let dx₁_4 := dx₂ + dy₂;
    let dy₁ := (starRingEnd R) x₁_3 • dx₁_4;
    let dy₂ := (starRingEnd R) x₁_5 • dx₁_4;
    let dy₁_3 := (starRingEnd R) x₁_1 • dy₁;
    let dy₂_4 := (starRingEnd R) x₁_4 • dy₁;
    let dy₁ := (starRingEnd R) x₁ • dy₁_3;
    let dy₂_5 := (starRingEnd R) x • dy₁_3;
    let dx₁ := dx₁ + dy₁;
    let dx₁_5 := dx₁_1 + dy₂_5;
    let dx₁_6 := dx₁_2 + dy₂_4;
    let dx₁_7 := dx₁_3 + dy₂;
    let dy₁ := (starRingEnd R) x₁_1 • dx₁_7;
    let dy₂ := (starRingEnd R) x₁_2 • dx₁_7;
    let dy₁_4 := (starRingEnd R) x₁ • dy₁;
    let dy₂_6 := (starRingEnd R) x • dy₁;
    let dx₁ := dx₁ + dy₁_4;
    let dx₁_8 := dx₁_5 + dy₂_6;
    let dx₁_9 := dx₁_6 + dy₂;
    let dy₁ := ⋯;
    ⋯) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R =>
            let x₁ := x*x
            let x₂ := x*x₁
            let x₃ := x*x₁*x₂
            let x₄ := x*x₁*x₂*x₃
            x*x₁*x₂*x₃*x₄) _) rewrite_by
              data_synth
