import SciLean

open SciLean

variable {R : Type} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R] [LawfulBLAS (DataArray R) R R] {n : Nat}


set_default_scalar R


/--
info: fun x =>
  let dw :=
    IdxType.fold IndexType.Range.full 0 fun i dw =>
      let xi := dw[i];
      let x := setElem dw i (xi + 1) True.intro;
      x;
  dw : R^[n] → R^[n]
-/
#guard_msgs in
#check (∇ (x : R^[n]), ∑ᴵ i, x[i]) rewrite_by
  lsimp +unfoldPartialApp [fgradient,↓revFDeriv_simproc]


/--
info: fun x =>
  let dw :=
    IdxType.fold IndexType.Range.full 0 fun i dw =>
      let x₁ := x[i];
      let xi := dw[i];
      let x := setElem dw i (xi + 2 * x₁) True.intro;
      x;
  dw : R^[n] → R^[n]
-/
#guard_msgs in
#check (∇ (x : R^[n]), ∑ᴵ i, x[i]^2) rewrite_by
  lsimp +unfoldPartialApp [fgradient,↓revFDeriv_simproc]



variable (A : R^[n,n])


/--
info: fun x =>
  let dw :=
    IdxType.fold IndexType.Range.full 0 fun i dw =>
      let dw :=
        IdxType.fold IndexType.Range.full dw fun i_1 dw =>
          let x₁ := A[(i, i_1)];
          let x₁_1 := x[i];
          let x₁_2 := x₁ * x₁_1;
          let x₁_3 := x[i_1];
          let xi := dw[i_1];
          let x := setElem dw i_1 (xi + x₁_2) True.intro;
          let dy₁ := x₁ * x₁_3;
          let xi := x[i];
          let x := setElem x i (xi + dy₁) True.intro;
          x;
      dw;
  dw : R^[n] → R^[n]
-/
#guard_msgs in
#check (∇ (x : R^[n]), ∑ᴵ i j, A[i,j]*x[i]*x[j]) rewrite_by
  lsimp +unfoldPartialApp [fgradient,↓revFDeriv_simproc]
