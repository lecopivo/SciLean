import SciLean

open SciLean

-- macro "Float^[" n:term "]" : term => `(FloatVector (Fin $n))


variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [AdjointSpace R X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace R Y]

def evalGrad (f : X → R) {f'} (hf : HasRevFDeriv R f f') (x : X) : X := (f' x).2 1

#exit
/--
info: [0.000000, 1.000000, 2.000000, 3.000000, 4.000000, 5.000000, 6.000000, 7.000000, 8.000000, 9.000000]
-/
#guard_msgs in
#eval evalGrad
         (fun x : Float^[10] =>
           IndexType.foldl (init:=(0:Float))
             (fun s i => s + 0.5 * (toVec x i)^2))
         (hf := by data_synth => conv => enter[3]; lsimp)
         (fromVec fun i => i.1.toFloat)



/--
info: [1.000000, 1.000000, 1.000000, 1.000000, 1.000000, 1.000000, 1.000000, 1.000000, 1.000000, 1.000000]
-/
#guard_msgs in
#eval evalGrad
         (fun x : Float^[10] =>
           IndexType.foldl (init:=(0:Float))
             (fun s i => s + (toVec x i)))
         (hf := by data_synth => conv => enter[3]; lsimp)
         (fromVec fun i => i.1.toFloat)






/--
info: HasRevFDeriv Float (fun x => IndexType.Range.full.foldl (fun x' x_1 => x' + x.1 + x.2.2) x.2.1) fun w =>
  let x₁ := w.2.1;
  let x :=
    IndexType.Range.full.foldl
      (fun xdf i =>
        let x := xdf.1;
        let x₁ := w.1;
        let x₁ := x + x₁;
        let x₁_1 := w.2;
        let x₁_2 := x₁_1.2;
        let x₁ := x₁ + x₁_2;
        (x₁, fun dx dw =>
          let dx' := dw.1;
          let dy' := dw.2;
          let dx₁₁ := dx' + dx;
          let dx₂ := dy' + (0, dx);
          let x := xdf.2 dx (dx₁₁, dx₂);
          let dw := x.1;
          let dx := x.2;
          (dw, dx)))
      (x₁, fun dx dw => (dx, dw));
  let y := x.1;
  (y, fun dx =>
    let x := x.2 dx 0;
    let dx := x.1;
    let dw := x.2;
    let dx₁ := dw.2.1;
    let dx₂₁ := dw.1;
    let dx₂₂ := dw.2.2;
    let dx₁ := dx₁ + dx;
    (dx₂₁, dx₁, dx₂₂)) : Prop
-/
#guard_msgs in
#check (HasRevFDeriv Float
  (fun x : Float×Float×Float =>
    IndexType.Range.full.foldl (fun x' (_ : Fin 10)  => x' + x.1 + x.2.2) (x.2.1)) _)
  rewrite_by data_synth; enter[3]; lsimp
