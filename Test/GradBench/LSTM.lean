import SciLean

open SciLean Scalar Lean ToJson FromJson

set_option pp.deepTerms true
set_option pp.proofs false

set_default_scalar Float

open Scalar in
def sigmoid {R} [RealScalar R] (x : R) : R := 1 / (1 + exp (-x))

abbrev_data_synth sigmoid in x : HasRevFDeriv R by
  unfold sigmoid
  data_synth (disch:=sorry_proof) => enter[3]; simp; to_ssa; to_ssa; lsimp

abbrev_data_synth sigmoid in x : HasRevFDerivUpdate R by
  unfold sigmoid
  data_synth (disch:=sorry_proof) => enter[3]; simp; to_ssa; to_ssa; lsimp


open Scalar in
abbrev_data_synth Scalar.tanh in x : HasRevFDeriv K by
  conv => enter[3]; assign (fun x : K =>
    let y := tanh x
    (y, fun dy => dy*(1 - y^2)))
  sorry_proof


@[simp,simp_core]
theorem VectorType.conj_real (x : Float^[n]) : VectorType.conj x = x := sorry_proof

open VectorType MatrixType in
def lstmModel {d : ℕ}
              (weight: Float^[4,d])
              (bias: Float^[4,d])
              (hidden: Float^[d])
              (cell: Float^[d])
              (input: Float^[d]) : Float^[d] × Float^[d] :=
  let forget  := input  |> (mul · (row weight 0)) |> (· + (row bias 0)) |> (map sigmoid ·)
  let ingate  := hidden |> (mul · (row weight 1)) |> (· + (row bias 1)) |> (map sigmoid ·)
  let outgate := input  |> (mul · (row weight 2)) |> (· + (row bias 2)) |> (map sigmoid ·)
  let change  := hidden |> (mul · (row weight 3)) |> (· + (row bias 3)) |> (map tanh ·)
  let t1s := mul cell forget
  let t2s := mul ingate change
  let cell2 := t1s + t2s
  let hidden2 := mul outgate (map tanh cell2)
  (hidden2, cell2)

set_option maxRecDepth 1000000

def_data_synth lstmModel in weight bias hidden cell input : HasRevFDeriv Float by
  unfold lstmModel VectorType.map; dsimp -zeta
  data_synth => enter[3]; lsimp

def_data_synth lstmModel in weight bias hidden cell input : HasRevFDerivUpdate Float by
  unfold lstmModel VectorType.map; dsimp -zeta
  data_synth => enter[3]; lsimp

open VectorType MatrixType in
def lstmPredict {slen d : ℕ}
                (mainParams: (Float^[4,d])^[slen,2])
                (extraParams: Float^[3,d])
                (state: (Float^[d])^[slen,2])
                (input: Float^[d]) : Float^[d] × Float^[d]^[slen,2] :=
  let x₀ := mul input (row extraParams 0)
  let state₀ : (Float^[d])^[slen,2] := 0

  let' (state',x') := IdxType.fold .full (init:=(state₀,x₀))
    (fun (i : Idx slen) sx =>
      let' (s,x) := sx
      let' (h,c) := lstmModel mainParams[i,0] mainParams[i,1] state[i,0] state[i,1] x
      let s := setElem s (i,(0:Idx 2)) h .intro
      let s := setElem s (i,(1:Idx 2)) c .intro
      (s,h))

  let v' := mul x' (row extraParams 1) + (row extraParams 2)
  (v', state')


def_data_synth lstmPredict in mainParams extraParams state : HasRevFDeriv Float by
  unfold lstmPredict; --dsimp -zeta
  data_synth => enter[3]; lsimp


open VectorType in
abbrev_data_synth Scalar.log in x : HasRevFDeriv K by
  conv => enter[3]; assign (fun x => (Scalar.log x, fun dx : K => dx/x))
  sorry_proof

abbrev_data_synth Scalar.log in x : HasRevFDerivUpdate K by
  conv => enter[3]; assign (fun x => (Scalar.log x, fun (dx : K) dx' => dx' + dx/x))
  sorry_proof


open VectorType MatrixType in
def lstmObjective {slen lenSeq d : ℕ}
                  (mainParams : (Float^[4,d])^[slen,2])
                  (extraParams : Float^[3,d])
                  (state : (Float^[d])^[slen, 2])
                  (sequence : Float^[d]^[lenSeq]) : Float :=
  -- state : [stlen][2][d]f64
  let' (_a, total) := IdxType.fold .full (init:=(state, (0:Float)))
    fun (i : Idx (lenSeq - 1)) st  =>
      let' (oldState, oldTotal) := st
      let' (y_pred, newState) := lstmPredict mainParams extraParams oldState sequence[⟨i.1,sorry_proof⟩]
      -- y_pred: DV [d]f64, newState: DM
      let tmp_sum := sum (exp y_pred)
      let tmp_log := - Scalar.log (tmp_sum + 2.0)
      let ynorm := scalAdd 1 tmp_log y_pred
      let newTotal := oldTotal + (⟪sequence[⟨i.1 + 1,sorry_proof⟩], ynorm⟫)
      (newState, newTotal)

  let count := d * (lenSeq - 1) |>.toFloat
  (-total * count⁻¹)


abbrev_data_synth lstmObjective in mainParams extraParams : HasRevFDeriv Float by
  unfold lstmObjective; --dsimp -zeta
  data_synth => enter[3]; lsimp


/--
info: lstmObjective.arg_mainParamsextraParams.HasRevFDeriv_simple_rule {slen lenSeq d : ℕ} (state : Float^[d]^[slen, 2])
  (sequence : Float^[d]^[lenSeq]) :
  HasRevFDeriv Float (fun x => lstmObjective x.1 x.2 state sequence) fun x =>
    let x :=
      IdxType.fold IndexType.Range.full ((state, 0), fun dx dw => (dx, dw)) fun i xdf =>
        let x_1 := xdf.1;
        let x₁₁ := x_1.1;
        let x₁₂ := x_1.2;
        let x₁ := x.1;
        let x₁₂_1 := x.2;
        let x :=
          lstmPredict.arg_mainParamsextraParamsstate.HasRevFDeriv_f' sequence[{ val := ↑i, isLt := ⋯ }]
            (x₁, x₁₂_1, x₁₁);
        let z := x.1;
        let x₁ := z.1;
        let x₁_1 := z.2;
        let a := VectorType.exp x₁;
        let x₁_2 := VectorType.sum a;
        let x₁_3 := x₁_2 + 2.0;
        let x₁_4 := Scalar.log x₁_3;
        let x₁_5 := -x₁_4;
        let a_1 := VectorType.scalAdd 1 x₁_5 x₁;
        let x₁ := sequence[{ val := ↑i + 1, isLt := ⋯ }];
        let x₁_6 := ⟪x₁, a_1⟫;
        let x₁_7 := x₁₂ + x₁_6;
        ((x₁_1, x₁_7), fun dx dw =>
          let dy := dx.1;
          let dz := dx.2;
          let dx := dz • x₁;
          let a_2 := VectorType.sum dx;
          let dy_1 := -a_2 / x₁_3;
          let dy_2 := VectorType.const dy_1;
          let a := VectorType.mul a dy_2;
          let dx := VectorType.axpby 1 dx 1 a;
          let dy := x.2 (dx, dy);
          let dy_3 := dy.1;
          let dz_1 := dy.2;
          let dx₁ := dw.1;
          let dx₂₂ := dw.2;
          let dx₁ := dx₁ + dy_3;
          let dy := dz_1.1;
          let dz_2 := dz_1.2;
          let dx₁_1 := dx₂₂ + dy;
          let x := xdf.2 (dz_2, dz) (dx₁, dx₁_1);
          let dw := x.1;
          let dx := x.2;
          (dw, dx));
    let x_1 := x.1;
    let x₁ := x_1.2;
    let x_2 := -x₁;
    let x₁ := (d * (lenSeq - 1)).toFloat⁻¹;
    let x₁_1 := x_2 * x₁;
    (x₁_1, fun dz =>
      let dy₂ := x₁ * dz;
      let dx := -dy₂;
      let x := x.2 (0, dx) 0;
      let dw := x.2;
      dw)
-/
#guard_msgs in
#check lstmObjective.arg_mainParamsextraParams.HasRevFDeriv_simple_rule
