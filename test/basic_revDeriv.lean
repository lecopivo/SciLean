import SciLean
import SciLean.Util.RewriteBy
import SciLean.Tactic.LSimp2.Elab

open SciLean

variable 
  {K : Type} [RealScalar K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {ι : Type} [EnumType ι]
  {E : ι → Type} [∀ i, SemiInnerProductSpace K (E i)]

set_default_scalar K 

macro "clean_up" : conv => `(conv| (simp (config:={zeta:=false}) only[oneHot,structModify,structMake,dite_eq_ite,eq_self,ite_true,ite_false,dite_true,dite_false,SciLean.conj_for_real_scalar,Sum.inr.injEq,Sum.inl.injEq,Prod.snd_zero, Prod.fst_zero]; ftrans only))


example 
  : revDeriv K (fun xy : X×Y => (xy.1,xy.2))
    =
    fun x => (x, fun dyz => dyz) :=
by
  conv => lhs; ftrans

example 
  : revDeriv K (fun xy : X×Y => (xy.2,xy.1))
    =
    fun x => ((x.snd, x.fst), fun dyz => (dyz.snd, dyz.fst)) :=
by
  conv => lhs; ftrans

variable (f : Y → X → X) 
  (hf : HasAdjDiff K (fun yx : Y×X => f yx.1 yx.2))
  (hf₁ : ∀ x, HasAdjDiff K (fun y => f y x))
  (hf₂ : ∀ y, HasAdjDiff K (fun x => f y x))
  (x : X)

example
  : revDeriv K (fun yy : Y×Y×Y => f yy.1 (f yy.2.1 (f yy.2.2 x)))
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
  conv => lhs; ftrans

example 
  : revDeriv K (fun yy : Y×Y×Y×Y => f yy.1 (f yy.2.1 (f yy.2.2.1 (f yy.2.2.2 x))))
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
  conv => lhs; ftrans


--------------------------------------------------------------------------------
-- Basic derivative w.r.t. to function with finite domain ----------------------
--------------------------------------------------------------------------------

attribute [ftrans_simp] Function.repeatIdx_update' 
attribute [ftrans_simp] Pi.zero_apply
attribute [ftrans_simp] ArrayType.introElem_getElem ArrayType.getElem_introElem

@[simp, ftrans_simp]
theorem Function.repeatIdx_add {α : Type _} [Add α] [Zero α] (f : ι → α) (x : α)
  : repeatIdx (fun i x => x + f i) x
    =
    x + ∑ i, f i :=
by
  simp[EnumType.sum, repeatIdx]; sorry_proof

@[simp, ftrans_simp]
theorem Function.repeatIdx_add' {α κ : Type _} [Add α] [Zero α] (f : ι → κ → α) (x : κ → α)
  : repeatIdx (fun i x j => x j + f i j) x
    =
    fun j => x j + ∑ i, f i j :=
by
  sorry_proof

@[simp, ftrans_simp]
theorem Function.repeatIdx_add'' 
  {Cont Idx Elem} [ArrayType Cont Idx Elem] [EnumType Idx] [EnumType ι]
  [Add Elem] [Zero Elem]
  (f : ι → Idx → Elem) (x : Cont)
  : repeatIdx (fun i x => introElem (Cont:=Cont) fun j => x[j] + f i j) x
    =
    introElem (Cont:=Cont) fun j => x[j] + ∑ i, f i j := 
by
  sorry_proof

@[simp, ftrans_simp]
theorem Function.repeatIdx_modifyElem
  {Cont Idx Elem} [ArrayType Cont Idx Elem] [EnumType Idx]
  (x : Cont) (f : Idx → Elem → Elem)
  : repeatIdx (fun i x => modifyElem x i (f i)) x
    =
    introElem fun i => f i (x[i]) := sorry_proof

@[simp, ftrans_simp]
theorem Function.repeatIdx_setElem
  {Cont Idx Elem} [ArrayType Cont Idx Elem] [EnumType Idx]
  (x : Cont) (f : Idx → Elem → Elem)
  : repeatIdx (fun i x => setElem x i (f i (x[i]))) x
    =
    introElem fun i => f i (x[i]) := sorry_proof


@[simp,ftrans_simp]
theorem Function.repeatIdx_modify {α : Type _} (f : ι → α → α) (g : ι → α)
  : repeatIdx (fun i g' => Function.modify g' i (f i)) g
    =
    fun i => f i (g i) := sorry_proof

@[simp]
theorem Function.repeatIdx_update'' {α : Type _} [EnumType ι] [EnumType κ] 
  (f : ι×κ → α) (g : ι → α) (op : α → α → α)
  : repeatIdx (fun (ij : ι×κ) g' => Function.update g' ij.1 (op (g' ij.1) (f ij))) g
    =
    fun i => 
      repeatIdx (fun (j : κ) g' => op g' (f (i,j))) (g i) := 
by
  sorry_proof

@[simp,ftrans_simp]
theorem Function.repeatIdx_update''' {α : Type _} [EnumType ι] [EnumType κ] 
  (f : ι×κ → α) (g : κ → α) (op : α → α → α)
  : repeatIdx (fun (ij : ι×κ) g' => Function.update g' ij.2 (op (g' ij.2) (f ij))) g
    =
    fun j => 
      repeatIdx (fun (i : ι) g' => op g' (f (i,j))) (g j) := 
by
  sorry_proof

@[simp,ftrans_simp]
theorem Function.repeatIdx_repeatIdx {ι κ α} [EnumType ι] [EnumType κ] (f : ι → κ → α → α)
  : repeatIdx (fun i x => (repeatIdx fun j x => f i j x) x)
    =
    repeatIdx (fun (ij : ι×κ) x => f ij.1 ij.2 x) := sorry_proof

----------------
----------------

example 
  : revDeriv K (fun (x : Fin 10 → K) => fun i => x i)
    =
    fun x => (x, fun dx => dx) :=
by 
  conv => lhs; ftrans; simp only [ftrans_simp]

example
  : revDeriv K (fun (x : Fin 10 → K) => ∑ i, x i)
    =
    fun x => (∑ i, x i, fun dx _ => dx) :=
by 
  conv => lhs; ftrans; simp only [ftrans_simp]

example
  : revDeriv K (fun (x : Fin 10 → K) => ∑ i, ‖x i‖₂²)
    =
    fun x => (∑ i, ‖x i‖₂², fun dx i => 2 * dx * (x i)) :=
by
  conv => lhs; ftrans; simp only [ftrans_simp]

example (A : Fin 5 → Fin 10 → K)
  : revDeriv K (fun (x : Fin 10 → K) => fun i => ∑ j, A i j * x j)
    =
    fun x => (fun i => ∑ j, A i j * x j, fun dy j => ∑ i, A i j * dy i) := 
by 
  conv => lhs; ftrans; simp only [ftrans_simp]

variable [PlainDataType K]

example 
  : revDeriv K (fun (x : K ^ Idx 10) => fun i => x[i])
    =
    fun x => (fun i => x[i], fun dx => ⊞ i => dx i) :=
by 
  conv => lhs; ftrans; simp only [ftrans_simp]

example
  : revDeriv K (fun (x : K ^ Idx 10) => ⊞ i => x[i])
    =
    fun x => (x, fun dx => dx) :=
by 
  conv => lhs; ftrans; simp only [ftrans_simp]

example
  : revDeriv K (fun (x : K ^ Idx 10) => ∑ i, x[i])
    =
    fun x => (∑ i, x[i], fun dy => ⊞ _ => dy) :=
by 
  conv => lhs; ftrans; simp only [ftrans_simp]

example
  : revDeriv K (fun (x : K ^ Idx 10) => ∑ i, ‖x[i]‖₂²)
    =
    fun x => (∑ i, ‖x[i]‖₂², fun dy : K => ⊞ i => 2 * dy * (x[i])) :=
by
  conv => lhs; ftrans; simp only [ftrans_simp]

example (A : Idx 5 → Idx 10 → K)
  : revDeriv K (fun (x : K ^ Idx 10) => fun i => ∑ j, A i j * x[j])
    =
    fun x => (fun i => ∑ j, A i j * x[j], fun dy => ⊞ j => ∑ i, A i j * dy i) := 
by 
  conv => lhs; ftrans; simp only [ftrans_simp]

example 
  : revDeriv K (fun (x : Fin 5 → Fin 10 → K) => fun i j => x i j)
    =
    fun x => (x, fun dx => dx) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  sorry_proof

example
  : revDeriv K (fun (x : Fin 5 → Fin 10 → Fin 15→ K) => fun i j k => x i j k)
    =
    fun x => (x, fun dx => dx) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  sorry_proof

example
  : revDeriv K (fun (x : Fin 5 → Fin 10 → Fin 15→ K) => fun k i j => x i j k)
    =
    fun x => (fun k i j => x i j k, fun dx i j k => dx k i j) :=
by
  (conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp])
  sorry_proof

example 
  : revDeriv K (fun (x : Fin 10 → K) => fun ij : Fin 5 × Fin 10 => x ij.2)
    =
    fun x => (fun ij : Fin 5 × Fin 10 => x ij.2, fun dx i => ∑ j, dx (j,i)) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  sorry_proof

example 
  : revDeriv K (fun (x : Fin 5 → K) => fun ij : Fin 5 × Fin 10 => x ij.1)
    =
    fun x => (fun ij : Fin 5 × Fin 10 => x ij.1, fun dx i => ∑ j, dx (i,j)) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  sorry_proof

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, HasAdjDiff K (f · i j k))
  : revDeriv K (fun (x : X) => fun k i j => f x i j k)
    =
    fun x =>
      let ydf := revDeriv K f x
      (fun k i j => ydf.1 i j k,
       fun dy => ydf.2 fun i j k => dy k i j) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  sorry_proof

example 
  : revDeriv K (fun (x : K ^ Idx 10) => fun (ij : Idx 5 × Idx 10) => x[ij.snd])
    =
    fun x => 
      (fun (ij : Idx 5 × Idx 10) => x[ij.snd], 
       fun dx => ⊞ j => ∑ i, dx (i,j)) := 
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  sorry_proof

example 
  : revDeriv K (fun (x : K ^ (Idx 10 × Idx 5)) => fun i j => x[(i,j)])
    =
    fun x => (fun i j => x[(i,j)],
              fun dx => ⊞ ij => dx ij.1 ij.2) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]

example
  : revDeriv K (fun (x : K ^ (Idx 5 × Idx 10 × Idx 15)) => fun i j k => x[(k,i,j)])
    =
    fun x =>
      (fun i j k => x[(k,i,j)],
       fun dx => ⊞ kij => dx kij.2.1 kij.2.2 kij.1) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  sorry_proof

example
  : revDeriv K (fun (x : K ^ (Idx 5 × Idx 10 × Idx 15)) => fun k i j => x[(i, j, k)])
    =
    fun x =>
      (fun k i j => x[(i,j,k)],
       fun dx => ⊞ ijk => dx ijk.2.2 ijk.1 ijk.2.1) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  sorry_proof

example 
  : revDeriv K (fun (x : Fin 10 → K) => fun i j => x i * x j)
    = 
    fun x => 
      (fun i j => x i * x j,
       fun dx i => ∑ j, x j * dx i j + ∑ j, x j * dx j i) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  sorry_proof

example 
  : revDeriv K (fun (x : Fin 10 → K) => fun (i : Fin 10) (j : Fin 5) => x (i+j))
    = 
    fun x => 
      (fun (i : Fin 10) (j : Fin 5) => x (i+j),
       fun dy i => ∑ (j : Fin 5), dy (i - j) j) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  sorry_proof

example (w : Idx' (-5) 5 → K)
  : revDeriv K (fun (x : Idx 10 → K) => fun (i : Idx 10) (j : Idx' (-5) 5) => w j * x (j.1 +ᵥ i))
    = 
    fun x =>
      (fun (i : Idx 10) (j : Idx' (-5) 5) => w j * x (j.1 +ᵥ i),
       fun dy i => ∑ (j : Idx' (-5) 5), w j * dy (-j.1 +ᵥ i) j) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  sorry_proof


example  (w : Idx' (-5) 5 → K)
  : revDeriv K (fun (x : Idx 10 → K) => fun (i : Idx 10) => ∑ j, w j * x (j.1 +ᵥ i))
    = 
    fun x =>
      (fun (i : Idx 10) => ∑ j, w j * x (j.1 +ᵥ i),
       fun dy i => ∑ (j : Idx' (-5) 5), w j * dy (-j.1 +ᵥ i)) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [ftrans_simp]
  simp
  sorry_proof



