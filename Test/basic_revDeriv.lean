import SciLean

open SciLean

variable
  {K : Type} [RealScalar K]
  {X} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]
  {ι : Type} [IndexType ι nι]

set_default_scalar K

example
  : revFDeriv K (fun xy : X×Y => (xy.1,xy.2))
    =
    fun x => (x, fun dyz => dyz) :=
by
  conv => lhs; fun_trans

example
  : revFDeriv K (fun xy : X×Y => (xy.2,xy.1))
    =
    fun x => ((x.snd, x.fst), fun dyz => (dyz.snd, dyz.fst)) :=
by
  conv => lhs; fun_trans

variable (f : Y → X → X)
  (hf : Differentiable K (fun yx : Y×X => f yx.1 yx.2))
  (hf₁ : ∀ x, Differentiable K (fun y => f y x))
  (hf₂ : ∀ y, Differentiable K (fun x => f y x))
  (x : X)

set_option synthInstance.maxHeartbeats 100000 in
example
  : revFDeriv K (fun yy : Y×Y×Y => f yy.1 (f yy.2.1 (f yy.2.2 x)))
    =
    fun x_1 =>
      let ydg := x_1.1;
      let yzdf := x_1.2;
      let ydg_1 := yzdf.1;
      let yzdf := x_1.2;
      let ydg_2 := yzdf.2;
      let zdf := revFDeriv K (fun x0 => f x0 x) ydg_2;
      let zdf_1 := zdf.1;
      let zdf_2 := revFDeriv K (fun x0x1 => f x0x1.1 x0x1.2) (ydg_1, zdf_1);
      let zdf_3 := zdf_2.1;
      let zdf_4 := revFDeriv K (fun x0x1 => f x0x1.1 x0x1.2) (ydg, zdf_3);
      (zdf_4.1, fun dz =>
        let dy := zdf_4.2 dz;
        let dx := dy.1;
        let dy := zdf_2.2 dy.2;
        let dy_1 := zdf.2 dy.2;
        let dx_1 := dy.1;
        (dx, dx_1, dy_1)) :=
by
  conv => lhs; lfun_trans

set_option synthInstance.maxHeartbeats 100000 in
example
  : revFDeriv K (fun yy : Y×Y×Y×Y => f yy.1 (f yy.2.1 (f yy.2.2.1 (f yy.2.2.2 x))))
    =
    fun x_1 =>
      let ydg := x_1.1;
      let yzdf := x_1.2;
      let ydg_1 := yzdf.1;
      let xydf := x_1.2;
      let yzdf := xydf.2;
      let ydg_2 := yzdf.1;
      let xydf := x_1.2;
      let yzdf := xydf.2;
      let ydg_3 := yzdf.2;
      let zdf := revFDeriv K (fun x0 => f x0 x) ydg_3;
      let zdf_1 := zdf.1;
      let zdf_2 := revFDeriv K (fun x0x1 => f x0x1.1 x0x1.2) (ydg_2, zdf_1);
      let zdf_3 := zdf_2.1;
      let zdf_4 := revFDeriv K (fun x0x1 => f x0x1.1 x0x1.2) (ydg_1, zdf_3);
      let zdf_5 := zdf_4.1;
      let zdf_6 := revFDeriv K (fun x0x1 => f x0x1.1 x0x1.2) (ydg, zdf_5);
      (zdf_6.1, fun dz =>
        let dy := zdf_6.2 dz;
        let dx := dy.1;
        let dy := zdf_4.2 dy.2;
        let dy_1 := zdf_2.2 dy.2;
        let dy_2 := zdf.2 dy_1.2;
        let dx_1 := dy.1;
        let dx_2 := dy_1.1;
        (dx, dx_1, dx_2, dy_2)) :=
by
  conv => lhs; lfun_trans


-- @[simp, simp_core]
-- theorem fold_function_modify_simplify {ι} [IndexType ι nι] [DecidableEq ι] {X} [AddGroup X]
--     (g h : ι → X) :
--     IndexType.foldl (fun f i => Function.modify f i fun fi => fi + g i) (h : ι → X)
--     =
--     fun i => h i + g i := sorry_proof

-- todo: add LawfulIndexType ( n(right now I'm on old LeanColls)
-- @[simp, simp_core]
-- theorem fold_indexed_update_simplify
--   {Idx Cont} [IndexType I NIdx] [DecidableEq Idx] {Elem} [AddCommGroup Elem] [ArrayType Cont Idx Elem]
--   (h : Cont) (g : Idx → Elem) :
--   IndexType.foldl (fun f i => ArrayType.modify f i fun fi => fi + g i) h
--   =
--   ArrayType.ofFn fun i => h[i] + g i := sorry_proof

-- @[simp, simp_core]
-- theorem fold_struct_modify_simplify
--   {Idx Cont} [IndexType I NIdx] [DecidableEq Idx] {Elem} [AddCommGroup Elem]
--   [StructType Cont Idx (fun _ => Elem)] (h : Cont) (g : Idx → Elem) :
--   IndexType.foldl (fun f i => structModify i (fun fi => fi + g i) f) h
--   =
--   structMake fun i => structProj h i + g i := sorry_proof


-- -- simplifier seems to have hard time applying this
-- @[simp, simp_core]
-- theorem fold_ofFn_simplify
--   {J} [IndexType J NJ]
--   {Idx} [DecidableEq Idx] {Elem} [AddGroup Elem] {Cont} [ArrayType Cont Idx Elem]
--   (h : Cont) (g : Idx → J → Elem):
--   IndexType.foldl (no_index (fun (x : Cont) j => ArrayType.ofFn fun i => x[i] + g i j)) (no_index h)
--   =
--   ArrayType.ofFn fun i => IndexType.foldl (fun xi j => xi + g i j) h[i] := sorry_proof

----------------
----------------

example
  : revFDeriv K (fun (x : Fin 10 → K) => fun i => x i)
    =
    fun x => (x, fun dx => dx) :=
by
  conv => lhs; fun_trans

example
  : revFDeriv K (fun (x : Fin 10 → K) => ∑ᴵ i, x i)
    =
    fun x => (∑ᴵ i, x i, fun dx _ => dx) :=
by
  conv => lhs; autodiff

example
  : revFDeriv K (fun (x : Fin 10 → K) => ∑ᴵ i, ‖x i‖₂²)
    =
    fun x => (∑ᴵ i, (x i)^2, fun dx i => 2 * dx * (x i)) :=
by
  conv => lhs; autodiff
  sorry_proof

#exit

example (A : Fin 5 → Fin 10 → K)
  : revFDeriv K (fun (x : Fin 10 → K) => fun i => ∑ j, A i j * x j)
    =
    fun x => (fun i => ∑ j, A i j * x j, fun dy j => ∑ i, A i j * dy i) :=
by
  conv => lhs; autodiff

variable [PlainDataType K]


example
  : revFDeriv K (fun (x : K^[Fin 10]) => fun i => x[i])
    =
    fun (x : K^[Fin 10]) => (fun i => x[i], fun dx => ⊞ i => dx i) :=
by
  conv => lhs; autodiff; simp

example
  : revFDeriv K (fun (x : K^[Fin 10]) => ⊞ i => x[i])
    =
    fun x => (x, fun dx => dx) :=
by
  conv => lhs; autodiff; simp

example
  : revFDeriv K (fun (x : K^[Fin 10]) => ∑ i, x[i])
    =
    fun (x : K^[Fin 10]) => (∑ i, x[i], fun dy => ⊞ _ => dy) :=
by
  conv => lhs; autodiff; simp

example
  : revFDeriv K (fun (x : K^[Fin 10]) => ∑ i, ‖x[i]‖₂²)
    =
    fun (x : DataArrayN K (Fin 10)) => (∑ i, ‖x[i]‖₂², fun dy : K => ⊞ i => 2 * dy * (x[i])) :=
by
  conv => lhs; autodiff; simp

example (A : Fin 5 → Fin 10 → K)
  : revFDeriv K (fun (x : K^[Fin 10]) => fun i => ∑ j, A i j * x[j])
    =
    fun (x : K^[Fin 10]) => (fun i => ∑ j, A i j * x[j], fun dy => ⊞ j => ∑ i, A i j * dy i) :=
by
  conv => lhs; autodiff; simp

example
  : revFDeriv K (fun (x : Fin 5 → Fin 10 → K) => fun i j => x i j)
    =
    fun x => (x, fun dx => dx) :=
by
  conv => lhs; autodiff

example
  : revFDeriv K (fun (x : Fin 5 → Fin 10 → Fin 15→ K) => fun i j k => x i j k)
    =
    fun x => (x, fun dx => dx) :=
by
  conv => lhs; autodiff

#exit

example
  : revFDeriv K (fun (x : Fin 5 → Fin 10 → Fin 15→ K) => fun k i j => x i j k)
    =
    fun x => (fun k i j => x i j k, fun dx i j k => dx k i j) :=
by
  (conv => lhs; fun_trans (config:={zeta:=false,singlePass:=true}); simp [simp_core])

example
  : revFDeriv K (fun (x : Fin 10 → K) => fun ij : Fin 5 × Fin 10 => x ij.2)
    =
    fun x => (fun ij : Fin 5 × Fin 10 => x ij.2, fun dx i => ∑ j, dx (j,i)) :=
by
  conv => lhs; fun_trans

example
  : revFDeriv K (fun (x : Fin 5 → K) => fun ij : Fin 5 × Fin 10 => x ij.1)
    =
    fun x => (fun ij : Fin 5 × Fin 10 => x ij.1, fun dx i => ∑ j, dx (i,j)) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [simp_core]
  sorry_proof

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, HasAdjDiff K (f · i j k))
  : revFDeriv K (fun (x : X) => fun k i j => f x i j k)
    =
    fun x =>
      let ydf := revFDeriv K f x
      (fun k i j => ydf.1 i j k,
       fun dy => ydf.2 fun i j k => dy k i j) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [simp_core]
  sorry_proof

example
  : revFDeriv K (fun (x : K ^ Idx 10) => fun (ij : Idx 5 × Idx 10) => x[ij.snd])
    =
    fun x =>
      (fun (ij : Idx 5 × Idx 10) => x[ij.snd],
       fun dx => ⊞ j => ∑ i, dx (i,j)) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [simp_core]
  sorry_proof

example
  : revFDeriv K (fun (x : K ^ (Idx 10 × Idx 5)) => fun i j => x[(i,j)])
    =
    fun x => (fun i j => x[(i,j)],
              fun dx => ⊞ ij => dx ij.1 ij.2) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [simp_core]

example
  : revFDeriv K (fun (x : K ^ (Idx 5 × Idx 10 × Idx 15)) => fun i j k => x[(k,i,j)])
    =
    fun x =>
      (fun i j k => x[(k,i,j)],
       fun dx => ⊞ kij => dx kij.2.1 kij.2.2 kij.1) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [simp_core]
  sorry_proof

example
  : revFDeriv K (fun (x : K ^ (Idx 5 × Idx 10 × Idx 15)) => fun k i j => x[(i, j, k)])
    =
    fun x =>
      (fun k i j => x[(i,j,k)],
       fun dx => ⊞ ijk => dx ijk.2.2 ijk.1 ijk.2.1) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [simp_core]
  sorry_proof

example
  : revFDeriv K (fun (x : Fin 10 → K) => fun i j => x i * x j)
    =
    fun x =>
      (fun i j => x i * x j,
       fun dx i => ∑ j, x j * dx i j + ∑ j, x j * dx j i) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [simp_core]
  sorry_proof

example
  : revFDeriv K (fun (x : Fin 10 → K) => fun (i : Fin 10) (j : Fin 5) => x (i+j))
    =
    fun x =>
      (fun (i : Fin 10) (j : Fin 5) => x (i+j),
       fun dy i => ∑ (j : Fin 5), dy (i - j) j) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [simp_core]
  sorry_proof

example (w : Idx' (-5) 5 → K)
  : revFDeriv K (fun (x : Idx 10 → K) => fun (i : Idx 10) (j : Idx' (-5) 5) => w j * x (j.1 +ᵥ i))
    =
    fun x =>
      (fun (i : Idx 10) (j : Idx' (-5) 5) => w j * x (j.1 +ᵥ i),
       fun dy i => ∑ (j : Idx' (-5) 5), w j * dy (-j.1 +ᵥ i) j) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [simp_core]
  sorry_proof


example  (w : Idx' (-5) 5 → K)
  : revFDeriv K (fun (x : Idx 10 → K) => fun (i : Idx 10) => ∑ j, w j * x (j.1 +ᵥ i))
    =
    fun x =>
      (fun (i : Idx 10) => ∑ j, w j * x (j.1 +ᵥ i),
       fun dy i => ∑ (j : Idx' (-5) 5), w j * dy (-j.1 +ᵥ i)) :=
by
  conv => lhs; ftrans; simp (config:={zeta:=false}) only [simp_core]
  simp
  sorry_proof
