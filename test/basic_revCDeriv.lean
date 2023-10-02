import SciLean
import SciLean.Tactic.LetNormalize
import SciLean.Util.RewriteBy

open SciLean

variable 
  {K : Type} [RealScalar K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {ι : Type} [EnumType ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]

set_default_scalar K 

example 
  : <∂ xy : X×Y, (xy.1,xy.2)
    =
    fun x => (x, fun dyz => dyz) :=
by
  conv => lhs; autodiff

example 
  : <∂ xy : X×Y, (xy.2,xy.1)
    =
    fun x => ((x.snd, x.fst), fun dyz => (dyz.snd, dyz.fst)) :=
by
  conv => lhs; autodiff

variable (f : Y → X → X) 
  (hf : HasAdjDiff K (fun yx : Y×X => f yx.1 yx.2))
  (hf₁ : ∀ x, HasAdjDiff K (fun y => f y x))
  (hf₂ : ∀ y, HasAdjDiff K (fun x => f y x))
  (x : X)

example
  : <∂ yy : Y×Y×Y, f yy.1 (f yy.2.1 (f yy.2.2 x))
    =
    fun x_1 =>
      let zdf := <∂ (x0:=x_1.snd.snd), f x0 x;
      let zdf_1 := <∂ (x0x1:=(x_1.snd.fst, zdf.fst)), f x0x1.fst x0x1.snd;
      let zdf_2 := <∂ (x0x1:=(x_1.fst, zdf_1.fst)), f x0x1.fst x0x1.snd;
      (zdf_2.fst, fun dz =>
        let dy := Prod.snd zdf_2 dz;
        let dy_1 := Prod.snd zdf_1 dy.snd;
        let dy_2 := Prod.snd zdf dy_1.snd;
        (dy.fst, dy_1.fst, dy_2)) :=
by
  conv => lhs; autodiff

example 
  : <∂ yy : Y×Y×Y×Y, f yy.1 (f yy.2.1 (f yy.2.2.1 (f yy.2.2.2 x)))
    =
    fun x_1 =>
      let zdf := <∂ (x0:=x_1.snd.snd.snd), f x0 x;
      let zdf_1 := <∂ (x0x1:=(x_1.snd.snd.fst, zdf.fst)), f x0x1.fst x0x1.snd;
      let zdf_2 := <∂ (x0x1:=(x_1.snd.fst, zdf_1.fst)), f x0x1.fst x0x1.snd;
      let zdf_3 := <∂ (x0x1:=(x_1.fst, zdf_2.fst)), f x0x1.fst x0x1.snd;
      (zdf_3.fst, fun dz =>
        let dy := Prod.snd zdf_3 dz;
        let dy_1 := Prod.snd zdf_2 dy.snd;
        let dy_2 := Prod.snd zdf_1 dy_1.snd;
        let dy_3 := Prod.snd zdf dy_2.snd;
        (dy.fst, dy_1.fst, dy_2.fst, dy_3)) :=
by
  conv => lhs; autodiff
