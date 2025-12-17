import SciLean

open SciLean Scalar

set_option pp.deepTerms true
set_option pp.proofs false

set_default_scalar Float


/-- unlack `logdiag` and `lt` to lower triangular matrix -/
def unpackQ {d : Nat} (logdiag : Float^[d]) (lt : Float^[((d-1)*d/2)]) : Float^[d,d]  :=
  ⊞ (ij : Idx d × Idx d) =>
    let' (i,j) := ij
    if h : i < j then 0
       else if h' : i == j then exp (logdiag[i])
       else
         let idx : Idx ((d-1)*d/2) := ⟨d.toUSize*j.1 + i.1 - j.1 - 1 - (j.1 * (j.1+1))/2,
                                       have := h; have := h'; sorry_proof⟩
         (lt[idx])


abbrev_data_synth unpackQ in logdiag lt : HasRevFDeriv Float by
  unfold unpackQ; dsimp
  data_synth => enter[3]; lsimp [↓let_ite_normalize]

def logWishartPrior {k d : Nat} (Qs : Float^[d,d]^[k]) (qsums : Float^[k]) (wishartGamma : Float) (wishartM : Nat) :=
    let p := d
    let n := p + wishartM + 1
    let c := (n * p) * (log wishartGamma - 0.5 * log 2) - (logMultiGamma (0.5 * n.toFloat) p)
    let frobenius : Float := ‖Qs‖₂²
    let sumQs : Float := qsums.sum
    0.5 * wishartGamma * wishartGamma * frobenius - wishartM * sumQs - k * c


abbrev_data_synth logWishartPrior in Qs qsums : HasRevFDeriv Float by
  unfold logWishartPrior;
  data_synth => enter[3]; lsimp



def gmmObjective {d k n : Nat}
      (alphas: Float^[k]) (means: Float^[k,d])
      (logdiag : Float^[k,d]) (lt : Float^[k,((d-1)*d)/2])
      (x : Float^[n,d]) (wishartGamma : Float) (wishartM: Nat) :=
    let C := -(n * d * 0.5 * log (2 * π))

    -- qsAndSums
    let Qs := ⊞ i => unpackQ (logdiag.row i) (lt.row i)
    let qsums := logdiag.sumRows

    let slse : Float :=
      ∑ᴵ (i : Idx n),  (⊞ (j : Idx k) =>
          alphas[j]
          +
          qsums[j]
          -
          0.5 * ‖Qs[j] * ((x.row i) - (means.row j))‖₂²).logsumexp

    C + slse - n * alphas.logsumexp + logWishartPrior Qs qsums wishartGamma wishartM


abbrev_data_synth gmmObjective in alphas means logdiag lt : HasRevFDeriv Float by
  unfold gmmObjective
  data_synth => enter[3]; lsimp


/--
info: gmmObjective.arg_alphasmeanslogdiaglt.HasRevFDeriv_simple_rule {d k n : ℕ} (x : Float^[n, d]) (wishartGamma : Float)
  (wishartM : ℕ) :
  HasRevFDeriv Float (fun x_1 => gmmObjective x_1.1 x_1.2.1 x_1.2.2.1 x_1.2.2.2 x wishartGamma wishartM) fun x_1 =>
    let x₁₁ := x_1.2.2.1;
    let x₁₂ := x_1.2.2.2;
    let x₁ := ⊞ i => unpackQ (x₁₁.row i) (x₁₂.row i);
    let x₁₂₁ := x_1.1;
    let x₁₂₂₁ := x_1.2.1;
    let x₁₂₂₂ := x_1.2.2.1;
    let x₁_1 := x₁₂₂₂.sumRows;
    let s := ∑ᴵ i, (⊞ j => x₁₂₁[j] + x₁_1[j] - 0.5 * ‖x₁[j] * (x.row i - x₁₂₂₁.row j)‖₂²).logsumexp;
    let x₁_2 := -(↑n * ↑d * 0.5 * log (2 * π));
    let x₁_3 := x₁_2 + s;
    let x₁_4 := ↑n;
    let x_2 := x₁₂₁.logsumexpSoftmax;
    let w := x_2.1;
    let x' := x_2.2;
    let x₁_5 := x₁_4 * w;
    let x₁_6 := x₁_3 - x₁_5;
    let s := ‖x₁‖₂²;
    let x₁_7 := x₁_1.sum;
    let x₁_8 := 0.5 * wishartGamma * wishartGamma;
    let x₁_9 := x₁_8 * s;
    let x₁_10 := ↑wishartM;
    let x₁_11 := x₁_10 * x₁_7;
    let x₁_12 := x₁_9 - x₁_11;
    let x₁_13 :=
      ↑k *
        ((↑d + ↑wishartM + 1) * ↑d * (log wishartGamma - 0.5 * log 2) -
          logMultiGamma (0.5 * (d + wishartM + 1).toFloat) d);
    let x₁_14 := x₁_12 - x₁_13;
    let x₁_15 := x₁_6 + x₁_14;
    (x₁_15, fun dz =>
      let dy₁ := -(x₁_4 * dz);
      let dx := dy₁ • x';
      let dy₁ := x₁_8 * dz;
      let dy₁_1 := -(x₁_10 * dz);
      let dx₁ := DataArrayN.scalAdd 0 1 dy₁_1;
      let dx_1 := (2 * dy₁) • x₁;
      let dw :=
        IndexType.fold IndexType.Range.full (dx₁, dx_1, dx, 0) fun i dw =>
          let x₁_16 := ⊞ j => x₁₂₁[j] + x₁_1[j] - 0.5 * ‖x₁[j] * (x.row i - x₁₂₂₁.row j)‖₂²;
          let x_3 := x₁_16.logsumexpSoftmax;
          let x' := x_3.2;
          let dx := dz • x';
          let dx :=
            IndexType.fold IndexType.Range.full dw fun i_1 dx_2 =>
              let x₁ := x₁[i_1];
              let x₁_17 := x.row i;
              let x₁_18 := x₁₂₂₁.row i_1;
              let x₁_19 := x₁_17 - x₁_18;
              let x₁_20 := x₁ * x₁_19;
              let dxi := dx[i_1];
              let dx₁₁ := dx_2.1;
              let dx₁₂ := dx_2.2.2.1;
              let dx₂₁ := dx_2.2.1;
              let dx₂₂ := dx_2.2.2.2;
              let xi := dx₁₂[i_1];
              let x := setElem dx₁₂ i_1 (xi + dxi) True.intro;
              let xi := dx₁₁[i_1];
              let x_4 := setElem dx₁₁ i_1 (xi + dxi) True.intro;
              let dy₁ := -(0.5 * dxi);
              let dx := (2 * dy₁) • x₁_20;
              let dy₁ := dx ⊗ x₁_19;
              let dy₂ := dx * x₁;
              let xi := dx₂₁[i_1];
              let x_5 := setElem dx₂₁ i_1 (xi + dy₁) True.intro;
              let A := dx₂₂.curry;
              let ai := A[i_1];
              let A := (setElem A i_1 (ai + -dy₂) True.intro).uncurry;
              (x_4, x_5, x, A);
          dx;
      let dx₁ := dw.1;
      let dx₂₁ := dw.2.1;
      let dx₂₂₁ := dw.2.2.1;
      let dx₂₂₂₁ := dw.2.2.2;
      let dx₁ := DataArrayN.scalAddCols 0 1 dx₁;
      let dx :=
        IndexType.fold IndexType.Range.full (dx₁, 0) fun i dx =>
          let x₁ := x₁₁.row i;
          let dxi := dx₂₁[i];
          let dx_2 :=
            IndexType.fold IndexType.Range.full 0 fun i dx =>
              if h : i.1 < i.2 then dx
              else
                if h : i.1 = i.2 then
                  let x₁ := x₁[i.1];
                  let a := exp x₁;
                  let dxi := dxi[i];
                  let dx₁ := dx.1;
                  let dx₂ := dx.2;
                  let dy := dxi * a;
                  let xi := dx₁[i.1];
                  let x := setElem dx₁ i.1 (xi + dy) True.intro;
                  (x, dx₂)
                else
                  let dxi := dxi[i];
                  let dx₁ := dx.2;
                  let dx₂ := dx.1;
                  let xi := dx₁[{ val := USize.ofNat d * ↑i.2 + ↑i.1 - ↑i.2 - 1 - ↑i.2 * (↑i.2 + 1) / 2, isLt := ⋯ }];
                  let x :=
                    setElem dx₁ { val := USize.ofNat d * ↑i.2 + ↑i.1 - ↑i.2 - 1 - ↑i.2 * (↑i.2 + 1) / 2, isLt := ⋯ }
                      (xi + dxi) True.intro;
                  (dx₂, x);
          let dy := dx_2.1;
          let dz := dx_2.2;
          let dx₁ := dx.1;
          let dx₂ := dx.2;
          let A := dx₁.curry;
          let ai := A[i];
          let A := (setElem A i (ai + dy) True.intro).uncurry;
          let A_1 := dx₂.curry;
          let ai := A_1[i];
          let A_2 := (setElem A_1 i (ai + dz) True.intro).uncurry;
          (A, A_2);
      let dx₂₂₁_1 := dx.1;
      let dx₂₂₂ := dx.2;
      (dx₂₂₁, dx₂₂₂₁, dx₂₂₁_1, dx₂₂₂))
-/
#guard_msgs in
#check gmmObjective.arg_alphasmeanslogdiaglt.HasRevFDeriv_simple_rule




/-- info: -1788.051617 -/
#guard_msgs in
#eval show IO Unit from do

  let k := 3
  let d := 2
  let n := 5

  let alphas: Float^[k] := ⊞[1.023,34.35,34]
  let means: Float^[k,d] :=  ⊞[1.34,1;22,34;-34,32]
  let logdiag : Float^[k,d] := ⊞[1.23,0.12;0.23,0.23;-0.534,1.23]
  let lt : Float^[k,((d-1)*d)/2] := (⊞[2.0;3;3] : Float^[3,(1*2)/2])
  let x : Float^[n,d] := ⊞[0.23,3.23; 1.0,23; 0.23,12; 23,0.3; -10,20]
  let wishartGamma : Float := 1
  let wishartM: Nat := 1

  IO.println (gmmObjective alphas means logdiag lt x wishartGamma wishartM)
