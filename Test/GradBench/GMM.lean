import SciLean

open SciLean Scalar

set_option pp.deepTerms true
set_option pp.proofs false

set_default_scalar Float

open VectorType in
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
    let sumQs : Float := VectorType.sum qsums
    0.5 * wishartGamma * wishartGamma * frobenius - wishartM * sumQs - k * c


abbrev_data_synth logWishartPrior in Qs qsums : HasRevFDeriv Float by
  unfold logWishartPrior;
  data_synth => enter[3]; lsimp


open VectorType
def gmmObjective {d k n : Nat}
      (alphas: Float^[k]) (means: Float^[k,d])
      (logdiag : Float^[k,d]) (lt : Float^[k,((d-1)*d)/2])
      (x : Float^[n,d]) (wishartGamma : Float) (wishartM: Nat) :=
    let C := -(n * d * 0.5 * log (2 * π))

    -- qsAndSums
    let Qs := ⊞ i => unpackQ (MatrixType.row logdiag i) (MatrixType.row lt i)
    let qsums := ⊞ i => VectorType.sum (MatrixType.row logdiag i)

    let slse : Float :=
      ∑ᴵ (i : Idx n), logsumexp (VectorType.fromVec (X:=Float^[k])
        fun (j : Idx k) =>
          alphas[j]
          +
          qsums[j]
          -
          0.5 * ‖MatrixType.gemv 1 1 Qs[j] ((MatrixType.row x i) - (MatrixType.row means j)) 0‖₂²)

    C + slse - n * VectorType.logsumexp alphas + logWishartPrior Qs qsums wishartGamma wishartM


abbrev_data_synth gmmObjective in alphas means logdiag lt : HasRevFDeriv Float by
  unfold gmmObjective
  data_synth => enter[3]; lsimp


/--
info: gmmObjective.arg_alphasmeanslogdiaglt.HasRevFDeriv_simple_rule {d k n : ℕ} (x : Float^[n, d]) (wishartGamma : Float)
  (wishartM : ℕ) :
  HasRevFDeriv Float (fun x_1 => gmmObjective x_1.1 x_1.2.1 x_1.2.2.1 x_1.2.2.2 x wishartGamma wishartM) fun x_1 =>
    let x₁₁ := x_1.2.2.1;
    let x₁₂ := x_1.2.2.2;
    let x₁ := ⊞ i => unpackQ (MatrixType.row x₁₁ i) (MatrixType.row x₁₂ i);
    let x₁₂₁ := x_1.1;
    let x₁₂₂₁ := x_1.2.1;
    let x₁₂₂₂ := x_1.2.2.1;
    let x₁_1 := ⊞ i => VectorType.sum (MatrixType.row x₁₂₂₂ i);
    let
      s := ∑ᴵ i,
        logsumexp
          (fromVec fun j =>
            x₁₂₁[j] + x₁_1[j] - 0.5 * ‖MatrixType.gemv 1 1 x₁[j] (MatrixType.row x i - MatrixType.row x₁₂₂₁ j) 0‖₂²);
    let x₁_2 := -(↑n * ↑d * 0.5 * log (2 * π));
    let x₁_3 := x₁_2 + s;
    let x₁_4 := ↑n;
    let a := logsumexp x₁₂₁;
    let x₁_5 := x₁_4 * a;
    let x₁_6 := x₁_3 - x₁_5;
    let s := ‖x₁‖₂²;
    let x₁_7 := VectorType.sum x₁_1;
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
      let a := softmax x₁₂₁;
      let dx := scal dy₁ a;
      let dy₁ := x₁_8 * dz;
      let dy₁_1 := -(x₁_10 * dz);
      let dx₁ := const dy₁_1;
      let dx_1 := (2 * dy₁) • x₁;
      let dw :=
        IdxType.fold IndexType.Range.full (dx₁, dx_1, dx, 0) fun i dw =>
          let x₁_16 :=
            fromVec fun j =>
              x₁₂₁[j] + x₁_1[j] - 0.5 * ‖MatrixType.gemv 1 1 x₁[j] (MatrixType.row x i - MatrixType.row x₁₂₂₁ j) 0‖₂²;
          let a := softmax x₁_16;
          let dy := scal dz a;
          let dx :=
            IdxType.fold IndexType.Range.full dw fun i_1 dx =>
              let x₁ := x₁[i_1];
              let x₁_17 := MatrixType.row x i;
              let x₁_18 := MatrixType.row x₁₂₂₁ i_1;
              let x₁_19 := x₁_17 - x₁_18;
              let x := MatrixType.gemv 1 1 x₁ x₁_19 0;
              let dyi := dy[i_1];
              let dx₁₁ := dx.1;
              let dx₁₂ := dx.2.2.1;
              let dx₂₁ := dx.2.1;
              let dx₂₂ := dx.2.2.2;
              let xi := dx₁₂[i_1];
              let x_2 := setElem dx₁₂ i_1 (xi + dyi) True.intro;
              let xi := dx₁₁[i_1];
              let x_3 := setElem dx₁₁ i_1 (xi + dyi) True.intro;
              let dy₁ := -(0.5 * dyi);
              let dx := (2 * dy₁) • x;
              let y₁ := MatrixType.outerprodAdd 1 dx x₁_19 0;
              let x₁₁ := MatrixType.gemvH 1 1 x₁ dx 0;
              let xi := dx₂₁[i_1];
              let x := setElem dx₂₁ i_1 (xi + y₁) True.intro;
              let ri := MatrixType.row dx₂₂ i_1;
              let dx := MatrixType.updateRow dx₂₂ i_1 (ri + -x₁₁);
              (x_3, x, x_2, dx);
          dx;
      let dx₁ := dw.1;
      let dx₂₁ := dw.2.1;
      let dx₂₂₁ := dw.2.2.1;
      let dx₂₂₂₁ := dw.2.2.2;
      let dx :=
        IdxType.fold IndexType.Range.full 0 fun i dx =>
          let dxi := dx₁[i];
          let dy := const dxi;
          let ri := MatrixType.row dx i;
          let dx := MatrixType.updateRow dx i (ri + dy);
          dx;
      let dx :=
        IdxType.fold IndexType.Range.full (dx, 0) fun i dx =>
          let x₁ := MatrixType.row x₁₁ i;
          let dxi := dx₂₁[i];
          let dx_2 :=
            IdxType.fold IndexType.Range.full 0 fun i dx =>
              if h : i.1 < i.2 then dx
              else
                if h : i.1 = i.2 then
                  let x₁ := x₁[i.1];
                  let a := Scalar.exp x₁;
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
                  let xi := dx₁[{ val := d.toUSize * ↑i.2 + ↑i.1 - ↑i.2 - 1 - ↑i.2 * (↑i.2 + 1) / 2, isLt := ⋯ }];
                  let x :=
                    setElem dx₁ { val := d.toUSize * ↑i.2 + ↑i.1 - ↑i.2 - 1 - ↑i.2 * (↑i.2 + 1) / 2, isLt := ⋯ }
                      (xi + dxi) True.intro;
                  (dx₂, x);
          let dy := dx_2.1;
          let dz := dx_2.2;
          let dx₁ := dx.1;
          let dx₂ := dx.2;
          let ri := MatrixType.row dx₁ i;
          let dx₁ := MatrixType.updateRow dx₁ i (ri + dy);
          let ri := MatrixType.row dx₂ i;
          let dx₁_1 := MatrixType.updateRow dx₂ i (ri + dz);
          (dx₁, dx₁_1);
      let dx₂₂₁_1 := dx.1;
      let dx₂₂₂ := dx.2;
      (dx₂₂₁, dx₂₂₂₁, dx₂₂₁_1, dx₂₂₂))
-/
#guard_msgs in
#check gmmObjective.arg_alphasmeanslogdiaglt.HasRevFDeriv_simple_rule
