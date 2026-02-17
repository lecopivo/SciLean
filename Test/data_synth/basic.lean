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

/-- info: HasRevFDerivUpdate R (fun x => x) fun x => (x, fun dx dx' => dx' + dx) : Prop -/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : X => x) _) rewrite_by data_synth

/-- info: HasRevFDerivUpdate R (fun x => x₀) fun x => (x₀, fun x dx => dx) : Prop -/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun _ : X => x₀) _) rewrite_by data_synth

/--
info: HasRevFDerivUpdate R
  (fun x =>
    let x_1 := 42;
    x)
  fun x => (x, fun dx dx' => dx' + dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R => let _ : Nat := 42;x) _) rewrite_by data_synth

/--
info: HasRevFDerivUpdate R
  (let c := 42;
  fun x => c * x)
  fun x =>
  have x₁ := 42;
  (x₁ * x, fun dy dx =>
    have dy₁ := (starRingEnd R) x₁ • dy;
    have dx := dx + dy₁;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (let c : R := 42; fun x : R => (c:R)*x) _) rewrite_by data_synth

/--
info: HasRevFDerivUpdate R
  (fun x =>
    let y := x ^ 2;
    y ^ 2)
  fun x =>
  have x₁ := x ^ 2;
  have x₁_1 := x₁ ^ 2;
  (x₁_1, fun dz dx =>
    have dx_1 := ↑2 * (starRingEnd R) x₁ ^ (2 - 1) • dz;
    have dx := dx + ↑2 * (starRingEnd R) x ^ (2 - 1) • dx_1;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R => let y := x^2; y^2) _) rewrite_by data_synth


/--
info: HasRevFDerivUpdate R
  (fun x =>
    let y := x₀ + x;
    x + y)
  fun x =>
  have x₁ := x₀ + x;
  have x₁ := x + x₁;
  (x₁, fun dz dx =>
    have dx₂ := 0;
    have dx₁ := dx + dz;
    have dx₁_1 := dx₂ + dz;
    have dx := dx₁ + dx₁_1;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : X => let y := x₀+x; x+y) _) rewrite_by data_synth


/--
info: HasRevFDerivUpdate R
  (fun x =>
    let x_1 := x;
    x)
  fun x => (x, fun dx dx' => dx' + dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : X => let _ := x; x) _) rewrite_by data_synth



/--
info: HasRevFDerivUpdate R (fun x i => ↑(↑i).toNat • x) fun x =>
  (fun i => ↑(↑i).toNat • x, fun dy dx =>
    IndexType.fold IndexType.Range.full dx fun i dx =>
      have x₁ := ↑(↑i).toNat;
      have dyi := dy i;
      have dx := dx + (starRingEnd R) x₁ • dyi;
      dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun (x : X) (i : Idx 3) => (i.1.toNat:R)•x) _) rewrite_by
  data_synth


/--
info: HasRevFDerivUpdate R (fun x i j => ↑(↑i + ↑j).toNat • x) fun x =>
  (fun i j => ↑(↑i + ↑j).toNat • x, fun dy dx =>
    IndexType.fold IndexType.Range.full dx fun i dx =>
      have dyi := dy i;
      have dx :=
        IndexType.fold IndexType.Range.full dx fun i_1 dx =>
          have x₁ := ↑(↑i + ↑i_1).toNat;
          have dyi := dyi i_1;
          have dx := dx + (starRingEnd R) x₁ • dyi;
          dx;
      dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun (x : X) (i j : Idx 3) => ((i.1+j.1).toNat:R)•x) _) rewrite_by
  data_synth


/--
info: HasRevFDerivUpdate R
  (fun x =>
    let y := x;
    y)
  fun x => (x, fun dx dx' => dx' + dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : X => let y := x; y) _) rewrite_by data_synth


variable (f : X → X) (f') (hf : HasRevFDerivUpdate R f f')

/-- info: HasRevFDerivUpdate R (fun x => f x) f' : Prop -/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x => f x) _) rewrite_by data_synth

/--
info: HasRevFDerivUpdate R (fun x => f x + f x) fun x =>
  have x_1 := f' x;
  have y := x_1.1;
  have df := x_1.2;
  have x := f' x;
  have z := x.1;
  have dg := x.2;
  (y + z, fun dy dx =>
    have dx := df dy dx;
    have dx := dg dy dx;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x => (f x)+(f x)) _) rewrite_by data_synth

variable (g : X → Idx n → R) (g' : Idx n → _) (hf : ∀ i, HasRevFDerivUpdate R (g · i) (g' i))
         (i j : Idx n)


/-- info: HasRevFDerivUpdate R (fun x => g x i) (g' i) : Prop -/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x => (g x i)) _) rewrite_by data_synth


/-- info: HasRevFDerivUpdate R f f' : Prop -/
#guard_msgs in
#check (HasRevFDerivUpdate R f _) rewrite_by data_synth



/--
info: HasRevFDerivUpdate R (fun x => x * x * x * x * x) fun x =>
  have x₁ := x * x;
  have x₁_1 := x₁ * x;
  have x₁_2 := x₁_1 * x;
  (x₁_2 * x, fun dy dx =>
    have dy₁ := (starRingEnd R) x₁_2 • dy;
    have dy₂ := (starRingEnd R) x • dy;
    have dx := dx + dy₁;
    have dy₁ := (starRingEnd R) x₁_1 • dy₂;
    have dy₂ := (starRingEnd R) x • dy₂;
    have dx := dx + dy₁;
    have dy₁ := (starRingEnd R) x₁ • dy₂;
    have dy₂ := (starRingEnd R) x • dy₂;
    have dx := dx + dy₁;
    have dy₁ := (starRingEnd R) x • dy₂;
    have dy₂ := (starRingEnd R) x • dy₂;
    have dx := dx + dy₁;
    have dx := dx + dy₂;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R => x*x*x*x*x) _ )
  rewrite_by
    data_synth


/--
info: HasRevFDerivUpdate R (fun x => x.1 * x.2 * x.1 * x.1 * x.2) fun x =>
  have x₁ := x.1;
  have x₁_1 := x.2;
  have x₁_2 := x₁ * x₁_1;
  have x₁_3 := x.1;
  have x₁_4 := x₁_2 * x₁_3;
  have x₁_5 := x.1;
  have x₁_6 := x₁_4 * x₁_5;
  have x₁_7 := x.2;
  (x₁_6 * x₁_7, fun dy dx =>
    have dy₁ := (starRingEnd R) x₁_6 • dy;
    have dy₂ := (starRingEnd R) x₁_7 • dy;
    have dx₁ := dx.2;
    have dx₂ := dx.1;
    have dx₁ := dx₁ + dy₁;
    have dy₁ := (starRingEnd R) x₁_4 • dy₂;
    have dy₂ := (starRingEnd R) x₁_5 • dy₂;
    have dx₁_1 := dx₂ + dy₁;
    have dy₁ := (starRingEnd R) x₁_2 • dy₂;
    have dy₂ := (starRingEnd R) x₁_3 • dy₂;
    have dx₁_2 := dx₁_1 + dy₁;
    have dy₁ := (starRingEnd R) x₁ • dy₂;
    have dy₂ := (starRingEnd R) x₁_1 • dy₂;
    have dx₁ := dx₁ + dy₁;
    have dx₁_3 := dx₁_2 + dy₂;
    (dx₁_3, dx₁)) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R×R => x.1 * x.2 * x.1 * x.1 * x.2) _) rewrite_by
              data_synth



/--
info: HasRevFDerivUpdate R (fun x => x.1 * x.2.1) fun x =>
  have x₁₁ := x.1;
  have x₁₂ := x.2.1;
  have x₁ := x₁₁ * x₁₂;
  (x₁, fun dy dx =>
    have dx₁₁ := dx.1;
    have dx₁₂ := dx.2.1;
    have dx₂ := dx.2.2;
    have dy₁ := (starRingEnd R) x₁₁ • dy;
    have dy₂ := (starRingEnd R) x₁₂ • dy;
    have dx₁ := dx₁₂ + dy₁;
    have dx₁_1 := dx₁₁ + dy₂;
    (dx₁_1, dx₁, dx₂)) : Prop
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
  (x + x, fun dy dx =>
    have dx := dx + dy;
    have dx := dx + dy;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R => let y := x; y+y) _ )
  rewrite_by
    data_synth




/--
info: HasRevFDerivUpdate R (fun x => x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x)
  fun x =>
  have x₁ := x * x;
  have x₁_1 := x₁ * x;
  have x₁_2 := x₁_1 * x;
  have x₁_3 := x₁_2 * x;
  have x₁_4 := x₁_3 * x;
  have x₁_5 := x₁_4 * x;
  have x₁_6 := x₁_5 * x;
  have x₁_7 := x₁_6 * x;
  have x₁_8 := x₁_7 * x;
  have x₁_9 := x₁_8 * x;
  have x₁_10 := x₁_9 * x;
  have x₁_11 := x₁_10 * x;
  have x₁_12 := x₁_11 * x;
  have x₁_13 := x₁_12 * x;
  have x₁_14 := x₁_13 * x;
  have x₁_15 := x₁_14 * x;
  have x₁_16 := x₁_15 * x;
  have x₁_17 := x₁_16 * x;
  have x₁_18 := x₁_17 * x;
  (x₁_18 * x, fun dy dx =>
    have dy₁ := (starRingEnd R) x₁_18 • dy;
    have dy₂ := (starRingEnd R) x • dy;
    have dx := dx + dy₁;
    have dy₁ := (starRingEnd R) x₁_17 • dy₂;
    have dy₂ := (starRingEnd R) x • dy₂;
    have dx := dx + dy₁;
    have dy₁ := (starRingEnd R) x₁_16 • dy₂;
    have dy₂ := (starRingEnd R) x • dy₂;
    have dx := dx + dy₁;
    have dy₁ := (starRingEnd R) x₁_15 • dy₂;
    have dy₂ := (starRingEnd R) x • dy₂;
    have dx := dx + dy₁;
    have dy₁ := (starRingEnd R) x₁_14 • dy₂;
    have dy₂ := (starRingEnd R) x • dy₂;
    have dx := dx + dy₁;
    have dy₁ := (starRingEnd R) x₁_13 • dy₂;
    have dy₂ := (starRingEnd R) x • dy₂;
    have dx := dx + dy₁;
    have dy₁ := (starRingEnd R) x₁_12 • dy₂;
    have dy₂ := (starRingEnd R) x • dy₂;
    have dx := dx + dy₁;
    have dy₁ := (starRingEnd R) x₁_11 • dy₂;
    have dy₂ := (starRingEnd R) x • dy₂;
    have dx := dx + dy₁;
    have dy₁ := (starRingEnd R) x₁_10 • dy₂;
    have dy₂ := (starRingEnd R) x • dy₂;
    have dx := dx + dy₁;
    have dy₁ := ⋯;
    ⋯) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R => x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x) _ )
  rewrite_by
    data_synth

/--
info: HasRevFDerivUpdate R (fun x => x.1) fun x =>
  have x₁ := x.1;
  (x₁, fun dy dx =>
    have dx₁ := dx.1;
    have dx₂₁ := dx.2.1;
    have dx₂₂₁ := dx.2.2.1;
    have dx₂₂₂ := dx.2.2.2;
    have dx₁ := dx₁ + dy;
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
  have x₁ := x * x;
  have x₁_1 := x₁ * x₁;
  (x₁_1, fun dz dx =>
    have dy₁ := (starRingEnd R) x₁ • dz;
    have dy₂ := (starRingEnd R) x₁ • dz;
    have dx_1 := dy₁ + dy₂;
    have dy₁ := (starRingEnd R) x • dx_1;
    have dy₂ := (starRingEnd R) x • dx_1;
    have dx := dx + dy₁;
    have dx := dx + dy₂;
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
  have x₁ := x * x;
  have x₁_1 := x * x₁;
  have x₁_2 := x * x₁_1;
  have x₁_3 := x * x₁_2;
  have x₁_4 := x * x₁_3;
  (x₁_4, fun dz dx =>
    have dx₁₁ := 0;
    have dx₂ := 0;
    have dx₁₁_1 := 0;
    have dx₁₁_2 := 0;
    have dy₁ := (starRingEnd R) x • dz;
    have dy₂ := (starRingEnd R) x₁_3 • dz;
    have dx₁ := dx₁₁_2 + dy₁;
    have dx₁_1 := dx + dy₂;
    have dy₁ := (starRingEnd R) x • dx₁;
    have dy₂ := (starRingEnd R) x₁_2 • dx₁;
    have dx₁ := dx₁₁_1 + dy₁;
    have dx₁_2 := dx₁_1 + dy₂;
    have dy₁ := (starRingEnd R) x • dx₁;
    have dy₂ := (starRingEnd R) x₁_1 • dx₁;
    have dx₁ := dx₁₁ + dy₁;
    have dx₁_3 := dx₁_2 + dy₂;
    have dy₁ := (starRingEnd R) x • dx₁;
    have dy₂ := (starRingEnd R) x₁ • dx₁;
    have dx₁ := dx₂ + dy₁;
    have dx₁_4 := dx₁_3 + dy₂;
    have dy₁ := (starRingEnd R) x • dx₁;
    have dy₂ := (starRingEnd R) x • dx₁;
    have dx := dx₁_4 + dy₁;
    have dx := dx + dy₂;
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
  have x₁ := x * x;
  have x₁_1 := x * x₁;
  have x₁_2 := x * x₁;
  have x₁_3 := x₁_2 * x₁_1;
  have x₁_4 := x * x₁;
  have x₁_5 := x₁_4 * x₁_1;
  have x₁_6 := x₁_5 * x₁_3;
  have x₁_7 := x * x₁;
  have x₁_8 := x₁_7 * x₁_1;
  have x₁_9 := x₁_8 * x₁_3;
  have x₁_10 := x₁_9 * x₁_6;
  (x₁_10, fun dz dx =>
    have dy₁ := (starRingEnd R) x₁_9 • dz;
    have dy₂ := (starRingEnd R) x₁_6 • dz;
    have dx₁ := 0;
    have dx₂₁ := 0;
    have dx₂₂₁ := 0;
    have dx₂₂₂₁ := 0;
    have dx₁ := dx₁ + dy₁;
    have dy₁ := (starRingEnd R) x₁_8 • dy₂;
    have dy₂ := (starRingEnd R) x₁_3 • dy₂;
    have dx₁_1 := dx₂₁ + dy₁;
    have dy₁ := (starRingEnd R) x₁_7 • dy₂;
    have dy₂ := (starRingEnd R) x₁_1 • dy₂;
    have dx₁_2 := dx₂₂₁ + dy₁;
    have dy₁ := (starRingEnd R) x • dy₂;
    have dy₂ := (starRingEnd R) x₁ • dy₂;
    have dx₁_3 := dx₂₂₂₁ + dy₁;
    have dx₁_4 := dx + dy₂;
    have dy₁ := (starRingEnd R) x₁_5 • dx₁;
    have dy₂ := (starRingEnd R) x₁_3 • dx₁;
    have dx₁ := dx₁_1 + dy₁;
    have dy₁ := (starRingEnd R) x₁_4 • dy₂;
    have dy₂ := (starRingEnd R) x₁_1 • dy₂;
    have dx₁_5 := dx₁_2 + dy₁;
    have dy₁ := (starRingEnd R) x • dy₂;
    have dy₂ := (starRingEnd R) x₁ • dy₂;
    have dx₁_6 := dx₁_3 + dy₁;
    have dx₁_7 := dx₁_4 + dy₂;
    have dy₁ := (starRingEnd R) x₁_2 • dx₁;
    have dy₂ := (starRingEnd R) x₁_1 • dx₁;
    have dx₁ := dx₁_5 + dy₁;
    have dy₁ := (starRingEnd R) x • dy₂;
    have dy₂ := (starRingEnd R) x₁ • dy₂;
    have dx₁_8 := dx₁_6 + dy₁;
    have dx₁_9 := dx₁_7 + dy₂;
    have dy₁ := ⋯ • dx₁;
    have dy₂ := ⋯;
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



/--
info: HasRevFDerivUpdate R
  (fun x =>
    let a := x.1 * x.2.2.2.2;
    let b := x.2.1 * x.2.2.2.2;
    let c := x.2.2.1 * x.2.2.2.2;
    let d := x.2.2.2.1 * x.2.2.2.2;
    a * b * c * d)
  fun x =>
  have x₁₁ := x.1;
  have x₁₂ := x.2.2.2.2;
  have x₁ := x₁₁ * x₁₂;
  have x₁₂₁ := x.2.1;
  have x₁₂₂₁ := x.2.2.1;
  have x₁₂₂₂₁ := x.2.2.2.1;
  have x₁₂₂₂₂ := x.2.2.2.2;
  have x₁_1 := x₁₂₁ * x₁₂₂₂₂;
  have x₁_2 := x₁₂₂₁ * x₁₂₂₂₂;
  have x₁_3 := x₁₂₂₂₁ * x₁₂₂₂₂;
  have x₁_4 := x₁ * x₁_1;
  have x₁_5 := x₁_4 * x₁_2;
  have x₁_6 := x₁_5 * x₁_3;
  (x₁_6, fun dz dx =>
    have dx₁₁ := 0;
    have dx₁₂₁ := dx.2.1;
    have dx₁₂₂₁ := dx.2.2.1;
    have dx₁₂₂₂₁ := dx.2.2.2.1;
    have dx₁₂₂₂₂ := dx.2.2.2.2;
    have dx₂ := dx.1;
    have dx₁₁_1 := 0;
    have dx₁₁_2 := 0;
    have dx₁₁_3 := 0;
    have dy₁ := (starRingEnd R) x₁_5 • dz;
    have dy₂ := (starRingEnd R) x₁_3 • dz;
    have dx₁ := dx₁₁_3 + dy₁;
    have dy₁ := (starRingEnd R) x₁_4 • dy₂;
    have dy₂ := (starRingEnd R) x₁_2 • dy₂;
    have dx₁_1 := dx₁₁_2 + dy₁;
    have dy₁ := (starRingEnd R) x₁ • dy₂;
    have dy₂ := (starRingEnd R) x₁_1 • dy₂;
    have dx₁_2 := dx₁₁_1 + dy₁;
    have dx₁_3 := dx₁₁ + dy₂;
    have dy₁ := (starRingEnd R) x₁₂₂₂₁ • dx₁;
    have dy₂ := (starRingEnd R) x₁₂₂₂₂ • dx₁;
    have dx₁ := dx₁₂₂₂₂ + dy₁;
    have dx₁_4 := dx₁₂₂₂₁ + dy₂;
    have dy₁ := (starRingEnd R) x₁₂₂₁ • dx₁_1;
    have dy₂ := (starRingEnd R) x₁₂₂₂₂ • dx₁_1;
    have dx₁ := dx₁ + dy₁;
    have dx₁_5 := dx₁₂₂₁ + dy₂;
    have dy₁ := (starRingEnd R) x₁₂₁ • dx₁_2;
    have dy₂ := (starRingEnd R) x₁₂₂₂₂ • dx₁_2;
    have dx₁ := dx₁ + dy₁;
    have dx₁_6 := dx₁₂₁ + dy₂;
    have dy₁ := (starRingEnd R) x₁₁ • dx₁_3;
    have dy₂ := ⋯ • dx₁_3;
    have dx₁ := ⋯;
    ⋯) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R×R×R×R×R =>
    let a := x.1 * x.2.2.2.2
    let b := x.2.1 * x.2.2.2.2
    let c := x.2.2.1 * x.2.2.2.2
    let d := x.2.2.2.1 * x.2.2.2.2
    a*b*c*d) _) rewrite_by data_synth




/--
info: HasRevFDerivUpdate R
  (fun x =>
    let a := x.1 * x.1 * x.2;
    let b := x.1 * x.2 * x.2;
    a * b)
  fun x =>
  have x₁ := x.1;
  have x₁_1 := x₁ * x₁;
  have x₁_2 := x.2;
  have x₁_3 := x₁_1 * x₁_2;
  have x₁₁ := x.1;
  have x₁₂ := x.2;
  have x₁_4 := x₁₁ * x₁₂;
  have x₁_5 := x₁_4 * x₁₂;
  have x₁_6 := x₁_3 * x₁_5;
  (x₁_6, fun dz dx =>
    have dx₁₁ := 0;
    have dx₁₂ := 0;
    have dx₂₁ := dx.1;
    have dx₂₂ := dx.2;
    have dy₁ := (starRingEnd R) x₁_3 • dz;
    have dy₂ := (starRingEnd R) x₁_5 • dz;
    have dx₁ := dx₁₁ + dy₁;
    have dx₁_1 := dx₁₂ + dy₂;
    have dy₁ := (starRingEnd R) x₁_4 • dx₁;
    have dy₂ := (starRingEnd R) x₁₂ • dx₁;
    have dx₁ := dx₂₂ + dy₁;
    have dy₁ := (starRingEnd R) x₁₁ • dy₂;
    have dy₂ := (starRingEnd R) x₁₂ • dy₂;
    have dx₁ := dx₁ + dy₁;
    have dx₁_2 := dx₂₁ + dy₂;
    have dy₁ := (starRingEnd R) x₁_1 • dx₁_1;
    have dy₂ := (starRingEnd R) x₁_2 • dx₁_1;
    have dx₁ := dx₁ + dy₁;
    have dy₁ := (starRingEnd R) x₁ • dy₂;
    have dy₂ := (starRingEnd R) x₁ • dy₂;
    have dx := dx₁_2 + dy₁;
    have dx := dx + dy₂;
    (dx, dx₁)) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R×R =>
    let a := x.1 * x.1 * x.2
    let b := x.1 * x.2 * x.2
    a*b) _) rewrite_by data_synth




/--
info: HasRevFDerivUpdate R (fun x => x.1.2.1) fun x =>
  have x₁ := x.1;
  have x₁ := x₁.2;
  have x₁ := x₁.1;
  (x₁, fun dy dx =>
    have dx₁ := dx.1;
    have dx₂ := dx.2;
    have dy₂ := 0;
    have dx' := dx₁.1;
    have dy' := dx₁.2;
    have dx₂_1 := dy' + (dy, dy₂);
    ((dx', dx₂_1), dx₂)) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R
          (fun x : (R×R×R)×R=> x.1.2.1)
          _) rewrite_by simp; data_synth



/--
info: HasRevFDerivUpdate R
  (fun x =>
    match x with
    | (w, x) => x + w.1 + w.2.2)
  fun x =>
  have x₁ := x.2;
  have x₁_1 := x.1;
  have x₁_2 := x₁_1.1;
  have x₁ := x₁ + x₁_2;
  have x₁_3 := x.1;
  have x₁_4 := x₁_3.2;
  have x₁_5 := x₁_4.2;
  have x₁ := x₁ + x₁_5;
  (x₁, fun dz dx =>
    have dx₂ := 0;
    have dx₁ := dx₂ + dz;
    have dx₁_1 := dx.2;
    have dx₂ := dx.1;
    have dx₁_2 := dx₁_1 + dz;
    have dx' := dx₂.1;
    have dy' := dx₂.2;
    have dx₁₁ := dx' + dz;
    have dy₁ := 0;
    have dx₂ := dy' + (dy₁, dx₁);
    ((dx₁₁, dx₂), dx₁_2)) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R
          (fun x : (R×R×R)×R=>
            match x with
            | (w, x) => x + w.1 + w.2.2)
          _) rewrite_by data_synth
