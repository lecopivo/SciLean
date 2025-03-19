import SciLean

open SciLean

variable {R : Type} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R] [LawfulBLAS (DataArray R) R R] {n : Nat}


set_default_scalar R


/--
info: fun x =>
   ∑ i,
    let dx := setElem 0 i 1 True.intro;
    dx : R^[n] → R^[n]
-/
#guard_msgs in
#check (∇ (x : R^[n]), ∑ᴵ i, x[i]) rewrite_by autodiff


/--
info: fun x =>
   ∑ i,
    let ydf := x[i];
    let dx := (2 * ydf) • setElem 0 i 1 True.intro;
    dx : R^[n] → R^[n]
-/
#guard_msgs in
#check (∇ (x : R^[n]), ∑ i, x[i]^2) rewrite_by autodiff


variable (A : R^[n,n])


/--
info: fun x =>
   ∑ i,
    let
      dx := ∑ i_1,
        let ydf := A[(i, i_1)];
        let zdg := x[i];
        let ydf_1 := ydf * zdg;
        let zdg := x[i_1];
        let dx := zdg • ydf • setElem 0 i 1 True.intro + ydf_1 • setElem 0 i_1 1 True.intro;
        dx;
    dx : R^[n] → R^[n]
-/
#guard_msgs in
#check (∇ (x : R^[n]), ∑ i j, A[i,j]*x[i]*x[j]) rewrite_by autodiff
