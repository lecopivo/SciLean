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
  let x₁ := 42;
  (x₁ * x, fun dy dx =>
    let dy₁ := (starRingEnd R) x₁ • dy;
    let dx := dx + dy₁;
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
  let x₁ := x ^ 2;
  let x₁_1 := x₁ ^ 2;
  (x₁_1, fun dz dx =>
    let dx_1 := ↑2 * (starRingEnd R) x₁ ^ (2 - 1) • dz;
    let dx := dx + ↑2 * (starRingEnd R) x ^ (2 - 1) • dx_1;
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
  let x₁ := x₀ + x;
  let x₁ := x + x₁;
  (x₁, fun dz dx =>
    let dx₂ := 0;
    let dx₁ := dx + dz;
    let dx₁_1 := dx₂ + dz;
    let dx := dx₁ + dx₁_1;
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
info: HasRevFDerivUpdate R (fun x i => ↑↑i • x) fun x =>
  (fun i => ↑↑i • x, fun dy dx =>
    IndexType.foldl
      (fun dx i =>
        let x₁ := ↑↑i;
        let dyi := dy i;
        let dx := dx + (starRingEnd R) x₁ • dyi;
        dx)
      dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun (x : X) (i : Fin 3) => (i.1:R)•x) _) rewrite_by
  data_synth


/--
info: HasRevFDerivUpdate R (fun x i j => (↑↑i + ↑↑j) • x) fun x =>
  (fun i j => (↑↑i + ↑↑j) • x, fun dy dx =>
    IndexType.foldl
      (fun dx i =>
        let dyi := dy i;
        let dx :=
          IndexType.foldl
            (fun dx i_1 =>
              let x₁ := ↑↑i + ↑↑i_1;
              let dyi := dyi i_1;
              let dx := dx + (starRingEnd R) x₁ • dyi;
              dx)
            dx;
        dx)
      dx) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun (x : X) (i j : Fin 3) => (i.1+j.1:R)•x) _) rewrite_by
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
  let x_1 := f' x;
  let y := x_1.1;
  let df := x_1.2;
  let x := f' x;
  let z := x.1;
  let dg := x.2;
  (y + z, fun dy dx =>
    let dx := df dy dx;
    let dx := dg dy dx;
    dx) : Prop
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
    let dy₁ := (starRingEnd R) x₁_2 • dy;
    let dy₂ := (starRingEnd R) x • dy;
    let dx := dx + dy₁;
    let dy₁ := (starRingEnd R) x₁_1 • dy₂;
    let dy₂ := (starRingEnd R) x • dy₂;
    let dx := dx + dy₁;
    let dy₁ := (starRingEnd R) x₁ • dy₂;
    let dy₂ := (starRingEnd R) x • dy₂;
    let dx := dx + dy₁;
    let dy₁ := (starRingEnd R) x • dy₂;
    let dy₂ := (starRingEnd R) x • dy₂;
    let dx := dx + dy₁;
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
    let dy₁ := (starRingEnd R) x₁_6 • dy;
    let dy₂ := (starRingEnd R) x₁_7 • dy;
    let dx₁ := dx.2;
    let dx₂ := dx.1;
    let dx₁ := dx₁ + dy₁;
    let dy₁ := (starRingEnd R) x₁_4 • dy₂;
    let dy₂ := (starRingEnd R) x₁_5 • dy₂;
    let dx₁_1 := dx₂ + dy₁;
    let dy₁ := (starRingEnd R) x₁_2 • dy₂;
    let dy₂ := (starRingEnd R) x₁_3 • dy₂;
    let dx₁_2 := dx₁_1 + dy₁;
    let dy₁ := (starRingEnd R) x₁ • dy₂;
    let dy₂ := (starRingEnd R) x₁_1 • dy₂;
    let dx₁ := dx₁ + dy₁;
    let dx₁_3 := dx₁_2 + dy₂;
    (dx₁_3, dx₁)) : Prop
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
    let dy₁ := (starRingEnd R) x₁₁ • dy;
    let dy₂ := (starRingEnd R) x₁₂ • dy;
    let dx₁ := dx₁₂ + dy₁;
    let dx₁_1 := dx₁₁ + dy₂;
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
    let dx := dx + dy;
    let dx := dx + dy;
    dx) : Prop
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
    let dy₁ := (starRingEnd R) x₁_18 • dy;
    let dy₂ := (starRingEnd R) x • dy;
    let dx := dx + dy₁;
    let dy₁ := (starRingEnd R) x₁_17 • dy₂;
    let dy₂ := (starRingEnd R) x • dy₂;
    let dx := dx + dy₁;
    let dy₁ := (starRingEnd R) x₁_16 • dy₂;
    let dy₂ := (starRingEnd R) x • dy₂;
    let dx := dx + dy₁;
    let dy₁ := (starRingEnd R) x₁_15 • dy₂;
    let dy₂ := (starRingEnd R) x • dy₂;
    let dx := dx + dy₁;
    let dy₁ := (starRingEnd R) x₁_14 • dy₂;
    let dy₂ := (starRingEnd R) x • dy₂;
    let dx := dx + dy₁;
    let dy₁ := (starRingEnd R) x₁_13 • dy₂;
    let dy₂ := (starRingEnd R) x • dy₂;
    let dx := dx + dy₁;
    let dy₁ := (starRingEnd R) x₁_12 • dy₂;
    let dy₂ := (starRingEnd R) x • dy₂;
    let dx := dx + dy₁;
    let dy₁ := (starRingEnd R) x₁_11 • dy₂;
    let dy₂ := (starRingEnd R) x • dy₂;
    let dx := dx + dy₁;
    let dy₁ := (starRingEnd R) x₁_10 • dy₂;
    let dy₂ := ⋯ • dy₂;
    let dx := ⋯;
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
    let dy₁ := (starRingEnd R) x₁ • dz;
    let dy₂ := (starRingEnd R) x₁ • dz;
    let dx_1 := dy₁ + dy₂;
    let dy₁ := (starRingEnd R) x • dx_1;
    let dy₂ := (starRingEnd R) x • dx_1;
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
    let dy₁ := (starRingEnd R) x • dz;
    let dy₂ := (starRingEnd R) x₁_3 • dz;
    let dx₁ := dx₁₁_2 + dy₁;
    let dx₁_1 := dx + dy₂;
    let dy₁ := (starRingEnd R) x • dx₁;
    let dy₂ := (starRingEnd R) x₁_2 • dx₁;
    let dx₁ := dx₁₁_1 + dy₁;
    let dx₁_2 := dx₁_1 + dy₂;
    let dy₁ := (starRingEnd R) x • dx₁;
    let dy₂ := (starRingEnd R) x₁_1 • dx₁;
    let dx₁ := dx₁₁ + dy₁;
    let dx₁_3 := dx₁_2 + dy₂;
    let dy₁ := (starRingEnd R) x • dx₁;
    let dy₂ := (starRingEnd R) x₁ • dx₁;
    let dx₁ := dx₂ + dy₁;
    let dx₁_4 := dx₁_3 + dy₂;
    let dy₁ := (starRingEnd R) x • dx₁;
    let dy₂ := (starRingEnd R) x • dx₁;
    let dx := dx₁_4 + dy₁;
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
    let dy₁ := (starRingEnd R) x₁_9 • dz;
    let dy₂ := (starRingEnd R) x₁_6 • dz;
    let dx₁ := 0;
    let dx₂₁ := 0;
    let dx₂₂₁ := 0;
    let dx₂₂₂₁ := 0;
    let dx₁ := dx₁ + dy₁;
    let dy₁ := (starRingEnd R) x₁_8 • dy₂;
    let dy₂ := (starRingEnd R) x₁_3 • dy₂;
    let dx₁_1 := dx₂₁ + dy₁;
    let dy₁ := (starRingEnd R) x₁_7 • dy₂;
    let dy₂ := (starRingEnd R) x₁_1 • dy₂;
    let dx₁_2 := dx₂₂₁ + dy₁;
    let dy₁ := (starRingEnd R) x • dy₂;
    let dy₂ := (starRingEnd R) x₁ • dy₂;
    let dx₁_3 := dx₂₂₂₁ + dy₁;
    let dx₁_4 := dx + dy₂;
    let dy₁ := (starRingEnd R) x₁_5 • dx₁;
    let dy₂ := (starRingEnd R) x₁_3 • dx₁;
    let dx₁ := dx₁_1 + dy₁;
    let dy₁ := (starRingEnd R) x₁_4 • dy₂;
    let dy₂ := (starRingEnd R) x₁_1 • dy₂;
    let dx₁_5 := dx₁_2 + dy₁;
    let dy₁ := (starRingEnd R) x • dy₂;
    let dy₂ := (starRingEnd R) x₁ • dy₂;
    let dx₁_6 := dx₁_3 + dy₁;
    let dx₁_7 := dx₁_4 + dy₂;
    let dy₁ := (starRingEnd R) x₁_2 • dx₁;
    let dy₂ := (starRingEnd R) x₁_1 • dx₁;
    let dx₁ := dx₁_5 + dy₁;
    let dy₁ := (starRingEnd R) x • dy₂;
    let dy₂ := (starRingEnd R) x₁ • dy₂;
    let dx₁_8 := dx₁_6 + dy₁;
    let dx₁_9 := dx₁_7 + dy₂;
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



/--
info: HasRevFDerivUpdate R
  (fun x =>
    let a := x.1 * x.2.2.2.2;
    let b := x.2.1 * x.2.2.2.2;
    let c := x.2.2.1 * x.2.2.2.2;
    let d := x.2.2.2.1 * x.2.2.2.2;
    a * b * c * d)
  fun x =>
  let x₁₁ := x.1;
  let x₁₂ := x.2.2.2.2;
  let x₁ := x₁₁ * x₁₂;
  let x₁₂₁ := x.2.1;
  let x₁₂₂₁ := x.2.2.1;
  let x₁₂₂₂₁ := x.2.2.2.1;
  let x₁₂₂₂₂ := x.2.2.2.2;
  let x₁_1 := x₁₂₁ * x₁₂₂₂₂;
  let x₁_2 := x₁₂₂₁ * x₁₂₂₂₂;
  let x₁_3 := x₁₂₂₂₁ * x₁₂₂₂₂;
  let x₁_4 := x₁ * x₁_1;
  let x₁_5 := x₁_4 * x₁_2;
  let x₁_6 := x₁_5 * x₁_3;
  (x₁_6, fun dz dx =>
    let dx₁₁ := 0;
    let dx₁₂₁ := dx.2.1;
    let dx₁₂₂₁ := dx.2.2.1;
    let dx₁₂₂₂₁ := dx.2.2.2.1;
    let dx₁₂₂₂₂ := dx.2.2.2.2;
    let dx₂ := dx.1;
    let dx₁₁_1 := 0;
    let dx₁₁_2 := 0;
    let dx₁₁_3 := 0;
    let dy₁ := (starRingEnd R) x₁_5 • dz;
    let dy₂ := (starRingEnd R) x₁_3 • dz;
    let dx₁ := dx₁₁_3 + dy₁;
    let dy₁ := (starRingEnd R) x₁_4 • dy₂;
    let dy₂ := (starRingEnd R) x₁_2 • dy₂;
    let dx₁_1 := dx₁₁_2 + dy₁;
    let dy₁ := (starRingEnd R) x₁ • dy₂;
    let dy₂ := (starRingEnd R) x₁_1 • dy₂;
    let dx₁_2 := dx₁₁_1 + dy₁;
    let dx₁_3 := dx₁₁ + dy₂;
    let dy₁ := (starRingEnd R) x₁₂₂₂₁ • dx₁;
    let dy₂ := (starRingEnd R) x₁₂₂₂₂ • dx₁;
    let dx₁ := dx₁₂₂₂₂ + dy₁;
    let dx₁_4 := dx₁₂₂₂₁ + dy₂;
    let dy₁ := (starRingEnd R) x₁₂₂₁ • dx₁_1;
    let dy₂ := (starRingEnd R) x₁₂₂₂₂ • dx₁_1;
    let dx₁ := dx₁ + dy₁;
    let dx₁_5 := dx₁₂₂₁ + dy₂;
    let dy₁ := (starRingEnd R) x₁₂₁ • dx₁_2;
    let dy₂ := (starRingEnd R) x₁₂₂₂₂ • dx₁_2;
    let dx₁ := dx₁ + dy₁;
    let dx₁_6 := dx₁₂₁ + dy₂;
    let dy₁ := ⋯ • dx₁_3;
    let dy₂ := ⋯;
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
  let x₁ := x.1;
  let x₁_1 := x₁ * x₁;
  let x₁_2 := x.2;
  let x₁_3 := x₁_1 * x₁_2;
  let x₁₁ := x.1;
  let x₁₂ := x.2;
  let x₁_4 := x₁₁ * x₁₂;
  let x₁_5 := x₁_4 * x₁₂;
  let x₁_6 := x₁_3 * x₁_5;
  (x₁_6, fun dz dx =>
    let dx₁₁ := 0;
    let dx₁₂ := 0;
    let dx₂₁ := dx.1;
    let dx₂₂ := dx.2;
    let dy₁ := (starRingEnd R) x₁_3 • dz;
    let dy₂ := (starRingEnd R) x₁_5 • dz;
    let dx₁ := dx₁₁ + dy₁;
    let dx₁_1 := dx₁₂ + dy₂;
    let dy₁ := (starRingEnd R) x₁_4 • dx₁;
    let dy₂ := (starRingEnd R) x₁₂ • dx₁;
    let dx₁ := dx₂₂ + dy₁;
    let dy₁ := (starRingEnd R) x₁₁ • dy₂;
    let dy₂ := (starRingEnd R) x₁₂ • dy₂;
    let dx₁ := dx₁ + dy₁;
    let dx₁_2 := dx₂₁ + dy₂;
    let dy₁ := (starRingEnd R) x₁_1 • dx₁_1;
    let dy₂ := (starRingEnd R) x₁_2 • dx₁_1;
    let dx₁ := dx₁ + dy₁;
    let dy₁ := (starRingEnd R) x₁ • dy₂;
    let dy₂ := (starRingEnd R) x₁ • dy₂;
    let dx := dx₁_2 + dy₁;
    let dx := dx + dy₂;
    (dx, dx₁)) : Prop
-/
#guard_msgs in
#check (HasRevFDerivUpdate R (fun x : R×R =>
    let a := x.1 * x.1 * x.2
    let b := x.1 * x.2 * x.2
    a*b) _) rewrite_by data_synth
