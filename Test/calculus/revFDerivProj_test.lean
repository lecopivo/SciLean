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
      let zdf := x[i];
      let dx :=
        IndexType.foldl
          (fun dx i_1 =>
            let ydg := A[i, i_1];
            let zdf' := ydg * zdf;
            let zdf := x[i_1];
            let dy₂ := ydg * zdf;
            let dx := ArrayType.modify dx i fun xi => xi + dy₂;
            let dx := ArrayType.modify dx i_1 fun xi => xi + zdf';
            dx)
          dx;
      dx)
    0 : R^[n] → R^[n]
-/
#guard_msgs in
#check (∇ (x : R^[n]), ∑ i j, A[i,j]*x[i]*x[j]) rewrite_by autodiff
