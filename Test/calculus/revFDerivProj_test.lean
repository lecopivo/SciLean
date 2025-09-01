import SciLean

open SciLean

variable {R : Type} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R] [LawfulBLAS (DataArray R) R R] {n : Nat}


set_default_scalar R


/--
info: fun w =>
  let s := ∑ᴵ i, w[i];
  (s, fun dx =>
    let dw :=
      IndexType.fold IndexType.Range.full 0 fun i dw =>
        let xi := dw[i];
        let x := setElem dw i (xi + dx) True.intro;
        x;
    dw) : R^[n] → R × (R → R^[n])
-/
#guard_msgs in
#check (<∂ (x : R^[n]), ∑ᴵ i, x[i]) rewrite_by
  lsimp [↓revFDeriv_simproc]


/--
info: fun w =>
  let s := ∑ᴵ i, w[i] ^ 2;
  (s, fun dx =>
    let dw :=
      IndexType.fold IndexType.Range.full 0 fun i dw =>
        let x₁ := w[i];
        let xi := dw[i];
        let x := setElem dw i (xi + 2 * (x₁ * dx)) True.intro;
        x;
    dw) : R^[n] → R × (R → R^[n])
-/
#guard_msgs in
#check (<∂ (x : R^[n]), ∑ᴵ i, x[i]^2) rewrite_by
  lsimp [↓revFDeriv_simproc]



variable (A : R^[n,n])


/--
info: fun w =>
  let s := ∑ᴵ i, ∑ᴵ j, A[(i, j)] * w[i] * w[j];
  (s, fun dx =>
    let dw :=
      IndexType.fold IndexType.Range.full 0 fun i dw =>
        let dw :=
          IndexType.fold IndexType.Range.full dw fun i_1 dw =>
            let x₁ := A[(i, i_1)];
            let x₁_1 := w[i];
            let x₁_2 := x₁ * x₁_1;
            let x₁_3 := w[i_1];
            let dy₁ := x₁_2 * dx;
            let dy₂ := x₁_3 * dx;
            let xi := dw[i_1];
            let x := setElem dw i_1 (xi + dy₁) True.intro;
            let dy₁ := x₁ * dy₂;
            let xi := x[i];
            let x := setElem x i (xi + dy₁) True.intro;
            x;
        dw;
    dw) : R^[n] → R × (R → R^[n])
-/
#guard_msgs in
#check (<∂ (x : R^[n]), ∑ᴵ i j, A[i,j]*x[i]*x[j]) rewrite_by
  lsimp [↓revFDeriv_simproc]
