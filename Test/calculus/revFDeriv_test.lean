import SciLean

open SciLean

set_option deprecated.oldSectionVars true

-- todo: move thi
section StructTypeSimps

variable
  {X I : Type _} {XI : I → Type _} [StructType X I XI] [Zero X] [∀ i, Zero (XI i)] [DecidableEq I]
  {Y J : Type _} {YJ : J → Type _} [StructType Y J YJ] [Zero Y] [∀ j, Zero (YJ j)] [DecidableEq J]

-- @[simp, simp_core]
-- theorem sum_oneHot [Add X] [IndexType I NI] (xi : (i : I) → XI i) :
--     (∑ i : I, oneHot (X:=X) i (xi i)) = structMake xi := sorry_proof

@[simp, simp_core]
theorem oneHot_prod_inl (i : I) (x : XI i) :
    oneHot (X:=X×Y) (I:=I⊕J) (.inl i) x = (oneHot i x, 0) := sorry_proof

@[simp, simp_core]
theorem oneHot_prod_inr (j : J) (y : YJ j) :
    oneHot (X:=X×Y) (I:=I⊕J) (.inr j) y = (0, oneHot j y) := sorry_proof

end StructTypeSimps


section ArrayTypeSimps



-- ∑ i, oneHot i (dy i)


variable
  {K : Type} [RealScalar K]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]
  {ι : Type} [IndexType ι nι] [DecidableEq ι]
  -- {E : ι → Type} [∀ i, SemiInnerProductSpace K (E i)]

set_default_scalar K

-- slow `fun_prop`
example : Differentiable K fun (x : Fin 5 → Fin 10 → Fin 15→ K) i_1 j => x i_1 j i := by fun_prop

-- @[fun_trans]
-- theorem revFDeriv_linear_map_rule (f : X → Y) (hf : IsContinuousLinearMap K f) :
--     revFDeriv K f
--     =
--     fun x => (f x, fun dy => adjoint K f dy) := by unfold revFDeriv; fun_trans


-- @[fun_trans]
-- theorem ArrayType.get.arg_cont.adjoint_rule
--     {XI : Type} [NormedAddCommGroup XI] [AdjointSpace K XI] [CompleteSpace XI]
--     [ArrayType X I XI] [DecidableEq I] (i : I) :
--     adjoint K (fun x : X => ArrayType.get x i)
--     =
--     fun xi => oneHot (X:=X) i xi := by sorry_proof


-- @[fun_trans]
-- theorem ArrayType.ofFn.arg_f.adjoint_rule
--     {XI : Type} [NormedAddCommGroup XI] [AdjointSpace K XI] [CompleteSpace XI]
--     [ArrayType X I XI] [IndexType I NI] [DecidableEq I] :
--     adjoint K (fun f : I → XI => ArrayType.ofFn (Cont:=X) f)
--     =
--     fun x i => ArrayType.get x i := by sorry_proof


example
  : revFDeriv K (fun xy : X×Y => (xy.1,xy.2))
    =
    fun x => (x, fun dyz => dyz) :=
by
  conv => lhs; autodiff

open Lean Elab Term Meta in
elab "lhs_of" h:term : term => do
  let prf ← elabTermAndSynthesize h.raw none
  let type ← instantiateMVars (← inferType prf)

  let .some (_,lhs,_) := type.eq? | throwError s!"{← ppExpr type} is not equality!"

  return lhs

open Lean Elab Term Meta in
elab "rhs_of" h:term : term => do
  let prf ← elabTermAndSynthesize h.raw none
  let type ← instantiateMVars (← inferType prf)

  let .some (_,_,rhs) := type.eq? | throwError s!"{← ppExpr type} is not equality!"

  return rhs


-- example
--   : revFDerivProj K Unit (fun xy : X×Y => (xy.2,xy.1))
--     =
--     fun x => ((x.snd, x.fst), fun _ dyz => (dyz.snd, dyz.fst)) :=
-- by
--   conv =>
--     lhs
--     autodiff

variable (f : Y → X → X)
  (hf : Differentiable K (fun yx : Y×X => f yx.1 yx.2))
  (hf₁ : ∀ x, Differentiable K (fun y => f y x))
  (hf₂ : ∀ y, Differentiable K (fun x => f y x))
  (x : X)

example
  : revFDeriv K (fun yy : Y×Y×Y => f yy.1 (f yy.2.1 (f yy.2.2 x)))
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
  conv => lhs; lfun_trans


example
  : revFDeriv K (fun yy : Y×Y×Y×Y => f yy.1 (f yy.2.1 (f yy.2.2.1 (f yy.2.2.2 x))))
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
  conv => lhs; lfun_trans



----------------
----------------

example
  : revFDeriv K (fun (x : Idx 10 → K) => fun i => x i)
    =
    fun x => (x, fun dx => dx) :=
by
  conv => lhs; fun_trans

#exit

example
  : revFDerivProj K Unit (fun (x : Fin 10 → K) => ∑ i, x i)
    =
    fun x => (∑ i, x i, fun _ dx _ => dx) :=
by
  conv => lhs; autodiff
  sorry

example
  : revFDeriv K (fun (x : Fin 10 → K) => ∑ i, ‖x i‖₂²)
    =
    fun x => (∑ i, (x i)^2, fun dx i => 2 * dx * (x i)) :=
by
  conv => lhs; autodiff
  sorry

example (A : Fin 5 → Fin 10 → K)
  : revCDeriv K (fun (x : Fin 10 → K) => fun i => ∑ j, A i j * x j)
    =
    fun x => (fun i => ∑ j, A i j * x j, fun dy j => ∑ i, A i j * dy i) :=
by
  conv => lhs; autodiff
  sorry

variable [PlainDataType K]


example
  : revFDeriv K (fun (x : K^[Fin 10]) => fun i => x[i])
    =
    fun (x : K^[Fin 10]) => (fun i => x[i], fun dx => ⊞ i => dx i) :=
by
  conv =>
    lhs; autodiff

example
  : revFDeriv K (fun (x : K^[Fin 10]) => ⊞ i => x[i])
    =
    fun x => (x, fun dx => dx) :=
by
  conv => lhs; autodiff

example
  : revFDeriv K (fun (x : K^[Fin 10]) => ⊞ i => 2*x[i]^3+x[i])
    =
    fun x => (x, fun dx => dx) :=
by
  conv => lhs; autodiff


example
  : revFDeriv K (fun (x : K^[Fin 10]) => ∑ i, x[i])
    =
    fun (x : K^[Fin 10]) => (∑ i, x[i], fun dy => ⊞ _ => dy) :=
by
  conv => lhs; autodiff

example
  : revFDeriv K (fun (x : K^[Fin 10]) => ∑ i, ‖x[i]‖₂²)
    =
    fun (x : DataArrayN K (Fin 10)) => (∑ i, x[i]^2, fun dy : K => ⊞ i => 2 * dy * (x[i])) :=
by
  conv => lhs; autodiff

example
  : revFDerivProj K Unit (fun (x : K^[Fin 10]) => ∑ i, let y := x[i]; ‖y‖₂²*y^3)
    =
    sorry :=
    -- fun (x : DataArrayN K (Fin 10)) => (∑ i, x[i]^2, fun dy : K => ⊞ i => 2 * dy * (x[i])) :=
by
  set_option trace.Meta.Tactic.fun_trans true in
  conv => lhs; autodiff

example (A : Fin 5 → Fin 10 → K)
  : revFDeriv K (fun (x : K^[Fin 10]) => fun i => ∑ j, A i j * x[j])
    =
    fun (x : K^[Fin 10]) => (fun i => ∑ j, A i j * x[j], fun dy => ⊞ j => ∑ i, A i j * dy i) :=
by
  conv => lhs; autodiff

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



example
  : revFDeriv K (fun (x : Fin 5 → Fin 10 → Fin 15→ K) => fun k i j => x i j k)
    =
    fun x => (fun k i j => x i j k, fun dx i j k => dx k i j) :=
by
  set_option trace.Meta.Tactic.fun_trans true in
  set_option trace.Meta.Tactic.fun_prop true in
  (conv => lhs; lfun_trans only)

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
