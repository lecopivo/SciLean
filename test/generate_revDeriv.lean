import SciLean

open SciLean

variable 
  {K : Type} [RealScalar K]
  {X : Type} [SemiInnerProductSpace K X]
  {X₁ : Type} [SemiInnerProductSpace K X₁]
  {X₂ : Type} [SemiInnerProductSpace K X₂]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {W : Type} [SemiInnerProductSpace K W]
  {ι : Type} [EnumType ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]

set_default_scalar K

def mul (x y : K) : K := x * y

#generate_revDeriv mul x y
  prop_by unfold mul; fprop
  trans_by unfold mul; ftrans; ftrans

def add (x y : X) : X := x + y

#generate_revDeriv add x y
  prop_by unfold add; fprop
  trans_by unfold add; ftrans; ftrans

def smul {X : Type} [SemiHilbert K X]
 (x : K) (y : X) : X := x • y

#generate_revDeriv smul x y
  prop_by unfold smul; fprop
  trans_by unfold smul; ftrans; ftrans


example :
  (revDeriv K fun (xy : K×K) => mul xy.1 xy.2)
  =
  fun x =>
    let zdf := mul.arg_xy.revDeriv x.1 x.2;
    (zdf.1, fun dz =>
      let dy := zdf.2 dz;
      dy) :=
by 
  conv => lhs; ftrans


example :
  (revDeriv K fun (x : K) => mul x x)
  =
  fun x =>
    let zdf := mul.arg_xy.revDeriv x x;
    (zdf.1, fun dz =>
      let dy := zdf.2 dz;
      dy.1 + dy.2) :=
by
  conv => lhs; ftrans

example :
  (revDeriv K fun (x : K) =>
    let x1 := mul x x
    let x2 := mul x1 (mul x x)
    let x3 := mul x2 (mul x1 x)
    let x4 := mul x3 (mul x2 x)
    let x5 := mul x4 (mul x3 x)
    x5)
  =
  fun x : K =>
    let zdf := mul.arg_xy.revDeriv x x;
    let zdf_1 := mul.arg_xy.revDeriv x x;
    let zdf_2 := mul.arg_xy.revDeriv zdf.1 zdf_1.1;
    let zdf_3 := mul.arg_xy.revDeriv zdf.1 x;
    let zdf_4 := mul.arg_xy.revDeriv zdf_2.1 zdf_3.1;
    let zdf_5 := mul.arg_xy.revDeriv zdf_2.1 x;
    let zdf_6 := mul.arg_xy.revDeriv zdf_4.1 zdf_5.1;
    let zdf_7 := mul.arg_xy.revDeriv zdf_4.1 x;
    let zdf_8 := mul.arg_xy.revDeriv zdf_6.1 zdf_7.1;
    (zdf_8.1, fun dz =>
      let dy := zdf_8.2 dz;
      let dy_1 := zdf_7.2 dy.2;
      let dy := zdf_6.2 dy.1;
      let dy_2 := zdf_5.2 dy.2;
      let dx1 := dy_1.1 + dy.1;
      let dx0 := dy_1.2 + dy_2.2;
      let dy := zdf_4.2 dx1;
      let dy_3 := zdf_3.2 dy.2;
      let dx1 := dy_2.1 + dy.1;
      let dx0 := dx0 + dy_3.2;
      let dy := zdf_2.2 dx1;
      let dy_4 := zdf_1.2 dy.2;
      let dx1 := dy_3.1 + dy.1;
      let dx0 := dx0 + dy_4.1;
      let dx0 := dx0 + dy_4.2;
      let dy := zdf.2 dx1;
      let dx := dx0 + dy.1;
      let dx := dx + dy.2;
      dx) :=
by
  conv => lhs; ftrans

example : 
  (revDeriv K fun (x : K) =>
    let x1 := mul x x
    let x2 := mul x1 x1
    let x3 := mul x2 x2
    let x4 := mul x3 x3
    let x5 := mul x4 x4
    x5)
  =
  fun x =>
    let zdf := mul.arg_xy.revDeriv x x;
    let zdf_1 := mul.arg_xy.revDeriv zdf.1 zdf.1;
    let zdf_2 := mul.arg_xy.revDeriv zdf_1.1 zdf_1.1;
    let zdf_3 := mul.arg_xy.revDeriv zdf_2.1 zdf_2.1;
    let zdf_4 := mul.arg_xy.revDeriv zdf_3.1 zdf_3.1;
    (zdf_4.1, fun dz =>
      let dy := zdf_4.2 dz;
      let dy := dy.1 + dy.2;
      let dy := zdf_3.2 dy;
      let dy := dy.1 + dy.2;
      let dy := zdf_2.2 dy;
      let dy := dy.1 + dy.2;
      let dy := zdf_1.2 dy;
      let dy := dy.1 + dy.2;
      let dy := zdf.2 dy;
     dy.1 + dy.2) := 
by
  ftrans


example :
  (revDeriv K fun (x : K) =>
    let x1 := mul x x
    let x2 := mul x1 x
    let x3 := mul x2 x
    let x4 := mul x3 x
    let x5 := mul x4 x
    x5)
  =
  fun x =>
    let zdf := mul.arg_xy.revDeriv x x;
    let zdf_1 := mul.arg_xy.revDeriv zdf.1 x;
    let zdf_2 := mul.arg_xy.revDeriv zdf_1.1 x;
    let zdf_3 := mul.arg_xy.revDeriv zdf_2.1 x;
    let zdf_4 := mul.arg_xy.revDeriv zdf_3.1 x;
    (zdf_4.1, fun dz =>
      let dy := zdf_4.2 dz;
      let dy_1 := zdf_3.2 dy.1;
      let dx0 := dy.2 + dy_1.2;
      let dy := zdf_2.2 dy_1.1;
      let dx0 := dx0 + dy.2;
      let dy := zdf_1.2 dy.1;
      let dx0 := dx0 + dy.2;
      let dy := zdf.2 dy.1;
      let dx := dx0 + dy.1;
      let dx := dx + dy.2;
      dx) :=
by
  conv => lhs; ftrans

