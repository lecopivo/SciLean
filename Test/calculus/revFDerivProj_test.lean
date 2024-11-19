import SciLean

open SciLean

variable {R : Type} [RealScalar R] [PlainDataType R]
  {n : Nat}


set_default_scalar R


/--
info: fun x =>
  IndexType.foldl
    (fun dx i =>
      let dx := ArrayType.modify dx i fun xi => xi + 1;
      dx)
    0 : R^[n] → R^[n]
-/
#guard_msgs in
#check (∇ (x : R^[n]), ∑ i, x[i]) rewrite_by autodiff


/--
info: fun x =>
  IndexType.foldl
    (fun dx i =>
      let ydf := x[i];
      let y' := 2 * ydf;
      let dx := ArrayType.modify dx i fun xi => xi + y';
      dx)
    0 : R^[n] → R^[n]
-/
#guard_msgs in
#check (∇ (x : R^[n]), ∑ i, x[i]^2) rewrite_by autodiff


variable (A : R^[n,n])


/--
info: fun x =>
  IndexType.foldl
    (fun dx i =>
      let zdg := x[i];
      let dx :=
        IndexType.foldl
          (fun dx i_1 =>
            let ydf := A[i, i_1];
            let ydf_1 := ydf * zdg;
            let zdg := x[i_1];
            let dy₂ := ydf * zdg;
            let dx := ArrayType.modify dx i_1 fun xi => xi + ydf_1;
            let dx := ArrayType.modify dx i fun xi => xi + dy₂;
            dx)
          dx;
      dx)
    0 : R^[n] → R^[n]
-/
#guard_msgs in
#check (∇ (x : R^[n]), ∑ i j, A[i,j]*x[i]*x[j]) rewrite_by autodiff
