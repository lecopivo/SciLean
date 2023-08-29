import SciLean
import SciLean.Util.Profile
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

theorem cderiv.uncurry_rule (f : X → Y → Z)
  (hf : IsDifferentiable K (fun xy : X×Y => f xy.1 xy.2))
  : cderiv K (fun xy : X×Y => f xy.1 xy.2)
    =
    fun xy dxy =>
      cderiv K (fun x => f x xy.2) xy.1 dxy.1
      +
      cderiv K (fun y => f xy.1 y) xy.2 dxy.2 := sorry_proof

theorem revCDeriv.prod_rule
  (f : X → Y → Z) (hf : HasAdjDiff K (fun x : X×Y => f x.1 x.2))
  : revCDeriv K (fun xy : X × Y => f xy.1 xy.2)
    =
    fun x =>
      let ydf := revCDeriv K (fun x : X×Y => f x.1 x.2) (x.1,x.2)
      (ydf.1,
       fun dz => 
         let dxy := ydf.2 dz
         (dxy.1, dxy.2)) := 
by
  -- simp [cderiv.uncurry_rule _ hf]
  sorry_proof


theorem revCDeriv.prod_rule'
  (f : X → Y → X×Y → Z) (hf : HasAdjDiff K (fun x : X×Y×(X×Y) => f x.1 x.2.1 x.2.2))
  : revCDeriv K (fun xy : X × Y => f xy.1 xy.2 xy)
    =
    fun x =>
      let ydf := revCDeriv K (fun x : X×Y×(X×Y) => f x.1 x.2.1 x.2.2) (x.1,x.2,x)
      (ydf.1,
       fun dz => 
         let dxy := ydf.2 dz
         (dxy.1, dxy.2.1) + dxy.2.2) := 
by
  -- simp [cderiv.uncurry_rule _ hf]
  sorry_proof


theorem revCDeriv.pi_rule_v1
  (f : (i : ι) → X → (ι → X) → Y) (hf : ∀ i, HasAdjDiff K (fun x : X×(ι→X) => f i x.1 x.2))
  : (revCDeriv K fun (x : ι → X) (i : ι) => f i (x i) x)
    =
    fun x =>
      let xdf₁ := fun i => ∇ x':=x i, f i x' x
      let xdf₂ := ∇ x':=x, fun i => f i (x i) x'
      (fun i => f i (x i) x, 
       fun dy i => xdf₁ i (dy i) + xdf₂ dy i) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  have : ∀ i x, IsDifferentiable K (fun x' => f i x' x) := sorry_proof
  have : ∀ i x x'', HasSemiAdjoint K (cderiv K (fun x' => f i x' x) x'') := sorry_proof
  have : ∀ i x, IsDifferentiable K (fun x' => f i x x') := sorry_proof
  have : ∀ i x x'', HasSemiAdjoint K (cderiv K (fun x' => f i x x') x'') := sorry_proof
  unfold gradient; unfold revCDeriv
  funext x; ftrans; ftrans; simp
  funext dy i; 
  ftrans; 
  conv in (cderiv _ _) => 
    rw[cderiv.uncurry_rule (K:=K) (f i) (by fprop)]
  simp;
  set_option trace.Meta.Tactic.simp.discharge true in
  ftrans only
  ftrans



theorem revCDeriv.pi_rule_v1'
  (f : (i : ι) → X → (ι → X) → Y) (hf : ∀ i, HasAdjDiff K (fun x : X×(ι→X) => f i x.1 x.2))
  : (revCDeriv K fun (x : ι → X) (i : ι) => f i (x i) x)
    =
    fun x =>
      let xdf := fun i => (<∂ x' : X×(ι→X), fun i' => f i' x'.1 x'.2) (x i, x)
      (fun i => (xdf i).1 i, 
       fun dy i => ((xdf i).2 dy).1 + ((xdf i).2 dy).2 i) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  have : ∀ i x, IsDifferentiable K (fun x' => f i x' x) := sorry_proof
  have : ∀ i x x'', HasSemiAdjoint K (cderiv K (fun x' => f i x' x) x'') := sorry_proof
  have : ∀ i x, IsDifferentiable K (fun x' => f i x x') := sorry_proof
  have : ∀ i x x'', HasSemiAdjoint K (cderiv K (fun x' => f i x x') x'') := sorry_proof
  unfold revCDeriv
  funext x; simp; funext dy i; ftrans; ftrans; simp
  conv in (cderiv _ _) => 
    rw[cderiv.uncurry_rule (K:=K) (f i) (by fprop)]
  conv =>
    rhs
    enter[1,1,2,i]
    simp[cderiv.uncurry_rule (K:=K) (f i) (by fprop)]
    ftrans
  sorry_proof



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

/--
info: fun x_1 =>
  let zdf := <∂ (x0:=x_1.snd.snd), f x0 x;
  let zdf_1 := <∂ (x0x1:=(x_1.snd.fst, zdf.fst)), f x0x1.fst x0x1.snd;
  let zdf_2 := <∂ (x0x1:=(x_1.fst, zdf_1.fst)), f x0x1.fst x0x1.snd;
  (zdf_2.fst, fun dz =>
    let dy := Prod.snd zdf_2 dz;
    let dy_1 := Prod.snd zdf_1 dy.snd;
    let dy_2 := Prod.snd zdf dy_1.snd;
    (dy.fst, dy_1.fst, dy_2)) : Y × Y × Y → X × (X → Y × Y × Y)
-/
#guard_msgs in
#check 
  <∂ yy : Y×Y×Y, f yy.1 (f yy.2.1 (f yy.2.2 x))
  rewrite_by autodiff

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


example 
  : (∇ (x : Fin 10 → K), fun i => x i)
    =
    fun x dx => dx :=
by 
  autodiff; admit

example
  : (∇ (x : Fin 10 → K), ∑ i, x i)
    =
    fun x i => 1 :=
by 
  autodiff; admit

example
  : (∇ (x : Fin 10 → K), ∑ i, ‖x i‖₂²)
    =
    fun x => 2 • x :=
by
  autodiff; admit

example (A : Fin 5 → Fin 10 → K)
  : (∇ (x : Fin 10 → K), fun i => ∑ j, A i j * x j)
    =
    fun _ dy j => ∑ i, A i j * dy i := 
by 
  autodiff; admit


