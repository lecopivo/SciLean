module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv

public import SciLean.Tactic.FunTrans.Attr
public import SciLean.Tactic.FunTrans.Elab
public import SciLean.Meta.Notation.Let'

public import SciLean.Analysis.Normed.IsContinuousLinearMap

@[expose] public section


open SciLean

variable
  {K : Type*} [RCLike K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]

namespace SciLean

attribute [fun_trans] fderiv

/-- Turn `deriv` to `fderiv`, this goes against mathlib that turns `fderiv` to `deriv`.
-/
@[simp, simp_core]
theorem deriv_fderiv'
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (f : 𝕜 → X) : deriv f = fun x => fderiv 𝕜 f x 1 := by funext x; rw[← toSpanSingleton_deriv]; simp

-- SciLean prefers `fderiv` over `deriv`
attribute [-simp] fderiv_eq_smul_deriv

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem fderiv.id_rule :
    (fderiv K fun x : X => x) = fun _ => fun dx =>L[K] dx := by ext x dx; simp

@[fun_trans]
theorem fderiv.const_rule (x : X) :
    (fderiv K fun _ : Y => x)
    =
    fun x => fun dy =>L[K] 0 := by
  ext x dx; simp

@[fun_trans]
theorem fderiv.apply_rule (i : ι) :
    (fderiv K fun (x : (i : ι) → E i) => x i)
    =
    fun _ => fun dx =>L[K] dx i := by
  funext x; ext dx
  let φ := fun (i : ι) (x : (j : ι) → E j) => x i
  have h := (fderiv_pi (𝕜:=K) (φ := φ) (h:=by fun_prop) (x:=x))
       |> (congrArg DFunLike.coe ·)
       |> (congrFun · dx)
       |> (congrFun · i)
  simp [φ] at h
  simp[h.symm]

@[fun_trans]
theorem fderiv.comp_rule_at
    (f : Y → Z) (g : X → Y) (x : X)
    (hf : DifferentiableAt K f (g x)) (hg : DifferentiableAt K g x) :
    (fderiv K fun x : X => f (g x)) x
    =
    let y := g x
    fun dx =>L[K]
      let dy := fderiv K g x dx
      let dz := fderiv K f y dy
      dz :=
by
  rw[show (fun x => f (g x)) = f ∘ g by rfl]
  rw[fderiv_comp x hf hg]
  ext dx; simp

@[fun_trans]
theorem fderiv.comp_rule
    (f : Y → Z) (g : X → Y)
    (hf : Differentiable K f) (hg : Differentiable K g) :
    (fderiv K fun x : X => f (g x))
    =
    fun x =>
    let y := g x
    fun dx =>L[K]
      let dy := fderiv K g x dx
      let dz := fderiv K f y dy
      dz :=
by
  funext x; fun_trans

@[fun_trans]
theorem fderiv.let_rule_at
    (f : X → Y → Z) (g : X → Y) (x : X)
    (hf : DifferentiableAt K (fun xy : X×Y => f xy.1 xy.2) (x, g x))
    (hg : DifferentiableAt K g x) :
    (fderiv K fun x : X => let y := g x; f x y) x
    =
    let y := g x
    fun dx =>L[K]
      let dy := fderiv K g x dx
      let dz := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
      dz :=
by
  have h : (fun x => f x (g x)) = (fun xy : X×Y => f xy.1 xy.2) ∘ (fun x => (x, g x)) := by rfl
  conv =>
    lhs
    rw[h]
    rw[fderiv_comp x hf (DifferentiableAt.prodMk (by simp) hg)]
    rw[DifferentiableAt.fderiv_prodMk (by simp) hg]
  ext dx; simp[ContinuousLinearMap.comp]


@[fun_trans]
theorem fderiv.let_rule
    (f : X → Y → Z) (g : X → Y)
    (hf : Differentiable K (fun xy : X×Y => f xy.1 xy.2))
    (hg : Differentiable K g) :
    (fderiv K fun x : X => let y := g x; f x y)
    =
    fun x =>
    let y := g x
    fun dx =>L[K]
      let dy := fderiv K g x dx
      let dz := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
      dz :=
by
  funext x; fun_trans

omit [Fintype ι] in
@[fun_trans]
theorem fderiv.pi_rule_at
    (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f · i) x) :
    (fderiv K fun (x : X) (i : ι) => f x i) x
    =
    fun dx =>L[K] fun i =>
      fderiv K (f · i) x dx := fderiv_pi hf

omit [Fintype ι] in
@[fun_trans]
theorem fderiv.pi_rule
    (f : X → (i : ι) → E i) (hf : ∀ i, Differentiable K (f · i)) :
    (fderiv K fun (x : X) (i : ι) => f x i)
    =
    fun x => fun dx =>L[K] fun i =>
      fderiv K (f · i) x dx := by funext x; rw[fderiv.pi_rule_at]; intro i; apply hf i


end SciLean

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

@[fun_trans]
theorem isContinuousLinearMap_fderiv (f : X → Y) (hf : IsContinuousLinearMap K f) :
    fderiv K f = fun _ => fun dx =>L[K] f dx := by
  ext x dx
  let hf : IsBoundedLinearMap K f := by
    have h : f = (fun x =>L[K] f x) := by rfl
    rw[h]
    apply ContinuousLinearMap.isBoundedLinearMap
  rw[IsBoundedLinearMap.fderiv (f:=f) hf]
  rfl


-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.mk.arg_fstsnd.fderiv_rule_at  (x : X)
    (g : X → Y) (hg : DifferentiableAt K g x)
    (f : X → Z) (hf : DifferentiableAt K f x) :
    fderiv K (fun x => (g x, f x)) x
    =
    fun dx =>L[K]
      let dy := fderiv K g x dx
      let dz := fderiv K f x dx
      (dy, dz) := by
  apply DifferentiableAt.fderiv_prodMk hg hf



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.fst.arg_self.fderiv_rule_at (x : X)
    (f : X → Y×Z) (hf : DifferentiableAt K f x) :
    fderiv K (fun x => (f x).1) x
    =
    fun dx =>L[K]
      let dyz := fderiv K f x dx
      dyz.1 := by
  apply fderiv.fst hf


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.snd.arg_self.fderiv_rule_at (x : X)
    (f : X → Y×Z) (hf : DifferentiableAt K f x) :
    fderiv K (fun x => (f x).2) x
    =
    fun dx =>L[K]
      let dyz := fderiv K f x dx
      dyz.2 := by
  apply fderiv.snd hf


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.fderiv_rule_at (x : X)
    (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fderiv K fun x => f x + g x) x
    =
    fun dx =>L[K]
      let dy := fderiv K f x dx
      let dz := fderiv K g x dx
      dy + dz := fderiv_add hf hg


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSub.hSub.arg_a0a1.fderiv_rule_at (x : X)
    (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fderiv K fun x => f x - g x) x
    =
    fun dx =>L[K]
      let dy := fderiv K f x dx
      let dz := fderiv K g x dx
      dy - dz := fderiv_sub hf hg


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.fderiv_rule (f : X → Y) :
    (fderiv K fun x => - f x)
    =
    fun x => fun dx =>L[K]
      let dy := fderiv K f x dx
      (-dy) := by funext x; apply fderiv_neg


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HMul.hMul.arg_a0a1.fderiv_rule_at
    {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] (x : X)
    (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fderiv K fun x => f x * g x) x
    =
    let y := f x
    let z := g x
    fun dx =>L[K]
      let dy := fderiv K f x dx
      let dz := fderiv K g x dx
      y * dz + z * dy := by
  ext dx
  simpa [mul_comm, Pi.mul_def] using congrArg (fun F => F dx) (fderiv_mul hf hg)



-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.fderiv_rule_at (x : X)
    (f : X → K) (g : X → Y)
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fderiv K fun x => f x • g x) x
    =
    let k := f x
    let y := g x
    fun dx =>L[K]
      let dk := fderiv K f x dx
      let dy := fderiv K g x dx
      k • dy + dk • y := fderiv_smul hf hg


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

set_option linter.unusedVariables false in
@[fun_prop]
theorem _root_.HDiv.hDiv.arg_a0a1.DifferentiableAt_rule
    {R} [RCLike R]
    {W} [NormedAddCommGroup W] [NormedSpace R W]
    (w : W) (a0 a1 : W → R)
    (ha0 : DifferentiableAt R a0 w) (ha1 : DifferentiableAt R a1 w) (ha1' : a1 w ≠ 0) :
    DifferentiableAt R (fun w => a0 w / a1 w) w := by fun_prop

set_option linter.unusedVariables false in
@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.fderiv_rule_at
    (x : X) (f : X → K) (g : X → K)
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) (hx : g x ≠ 0) :
    (fderiv K fun x => f x / g x) x
    =
    let y := f x
    let z := g x
    fun dx =>L[K]
      let dy := fderiv K f x dx
      let dz := fderiv K g x dx
      (dy * z - y * dz) / z^2 := by
  have hinv : HasFDerivAt (fun x => (g x)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton K (-(g x^2)⁻¹)).comp (fderiv K g x)) x :=
    HasFDerivAt.comp (𝕜:=K) x ((hasDerivAt_inv hx).hasFDerivAt) hg.hasFDerivAt
  have hmul := HasFDerivAt.fun_mul hf.hasFDerivAt hinv
  rw [show (fun x => f x / g x) = (fun x => f x * (g x)⁻¹) by funext x; rw [div_eq_mul_inv]]
  rw [hmul.fderiv]
  refine ContinuousLinearMap.ext fun dx => ?_
  simp [ContinuousLinearMap.toSpanSingleton_apply]
  field_simp
  ring


-- Inv.inv -------------------------------------------------------------------
--------------------------------------------------------------------------------
set_option linter.unusedVariables false in
@[fun_prop]
theorem _root_.Inv.inv.arg_a0.DifferentiableAt_rule
    {R} [RCLike R]
    {W} [NormedAddCommGroup W] [NormedSpace R W]
    (w : W) (a0 : W → R)
    (ha0 : DifferentiableAt R a0 w) (ha0' : a0 w ≠ 0) :
    DifferentiableAt R (fun w => (a0 w)⁻¹) w := by fun_prop

@[fun_trans]
theorem HInv.hInv.arg_a0a1.fderiv_rule_at
    (x : X) (f : X → K)
    (hf : DifferentiableAt K f x) (hx : f x ≠ 0) :
    (fderiv K fun x => (f x)⁻¹) x
    =
    let y := f x
    fun dx =>L[K]
      let dy := fderiv K f x dx
      (-dy) / y^2 := by
  ext dx
  rw[fderiv_fun_comp]
  rw[fderiv_inv]
  simp; ring
  apply differentiableAt_inv hx
  apply hf


-- HPow.hPow ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HPow.hPow.arg_a0.fderiv_rule_at (n : Nat) (x : X)
    (f : X → K) (hf : DifferentiableAt K f x) :
    fderiv K (fun x => f x ^ n) x
    =
    let y := f x
    fun dx =>L[K]
      let dy := fderiv K f x dx
      n * dy * (y ^ (n-1)) :=
by
  induction n
  case zero =>
    simp; rfl
  case succ n hn =>
    ext dx
    simp_rw [pow_succ]
    rw [HMul.hMul.arg_a0a1.fderiv_rule_at x _ f (by fun_prop) (by fun_prop)]
    simp only [ContinuousLinearMap.mk'_eval]
    rw [hn]
    simp only [ContinuousLinearMap.mk'_eval]
    induction n
    case zero => simp
    case succ =>
      rw [show ∀ (n : Nat), n.succ - 1 = n by simp]
      rw [pow_succ]
      simp; ring


-- sum -------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- @[fun_trans]
-- theorem sum.arg_f.fderiv_rule_at {ι} [IndexType ι]
--   (x : X) (f : X → ι → Y) (hf : ∀ i, DifferentiableAt K (f · i) x)
--   : fderiv K (fun x => sum fun i => f x i) x
--     =
--     fun dx =>L[K]
--       sum fun i =>
--         let dy := fderiv K (f · i) x dx
--         dy :=
-- by
--   ext dx
--   fun_trans [ContinuousLinearMap.mk']
--   rw[fderiv.pi_rule_at]; simp
--   apply hf

-- @[fun_trans]
-- theorem sum.arg_f.fderiv_rule {ι} [IndexType ι]
--   (f : X → ι → Y) (hf : ∀ i, Differentiable K (f · i))
--   : fderiv K (fun x => sum fun i => f x i)
--     =
--     fun x => fun dx =>L[K]
--       sum fun i =>
--         let dy := fderiv K (f · i) x dx
--         dy :=
-- by
--   funext x; fun_trans



--------------------------------------------------------------------------------

theorem SciLean.fderiv_wrt_prod
  {f : X → Y → Z} (hf : Differentiable K ↿f := by fun_prop) :
  fderiv K (fun xy : X×Y => f xy.1 xy.2)
  =
  fun xy => fun dxy =>L[K]
    let x := xy.1; let y := xy.2
    let dx := dxy.1; let dy := dxy.2
    let dzdx := fderiv K (f · y) x dx
    let dzdy := fderiv K (f x ·) y dy
    dzdx + dzdy := by
  funext xy
  obtain ⟨x,y⟩ := xy
  have hF := (hf (x,y)).hasFDerivAt
  have h1 : HasFDerivAt (fun x' => f x' y)
      ((fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y)).comp
        ((ContinuousLinearMap.id K X).prod 0)) x :=
    HasFDerivAt.comp (f := fun x' : X => (x',y)) x hF
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
  have h2 : HasFDerivAt (fun y' => f x y')
      ((fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y)).comp
        ((0 : Y →L[K] X).prod (ContinuousLinearMap.id K Y))) y :=
    HasFDerivAt.comp (f := fun y' : Y => (x,y')) y hF
      ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y))
  refine ContinuousLinearMap.ext fun dxy => ?_
  obtain ⟨dx,dy⟩ := dxy
  simp only [ContinuousLinearMap.mk'_eval, h1.fderiv, h2.fderiv, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply]
  rw [← map_add]
  norm_num


variable
  {X₁ : Type*} [NormedAddCommGroup X₁] [NormedSpace K X₁]
  {X₂ : Type*} [NormedAddCommGroup X₂] [NormedSpace K X₂]
  {X₃ : Type*} [NormedAddCommGroup X₃] [NormedSpace K X₃]


theorem SciLean.fderiv_wrt_prod3
  {f : X₁ → X₂ → X₃ → Z} (hf : Differentiable K ↿f := by fun_prop) :
  fderiv K (fun x : X₁×X₂×X₃ => f x.1 x.2.1 x.2.2)
  =
  fun x => fun dx =>L[K]
    let' (x₁,x₂,x₃) := x
    let' (dx₁,dx₂,dx₃) := dx
    let dzdx₁ := fderiv K (f · x₂ x₃) x₁ dx₁
    let dzdx₂ := fderiv K (f x₁ · x₃) x₂ dx₂
    let dzdx₃ := fderiv K (f x₁ x₂ ·) x₃ dx₃
    dzdx₁ + dzdx₂ + dzdx₃ := by
  funext x
  obtain ⟨x₁,x₂,x₃⟩ := x
  have hF := (hf (x₁,x₂,x₃)).hasFDerivAt
  set F := fderiv K (fun x : X₁×X₂×X₃ => f x.1 x.2.1 x.2.2) (x₁,x₂,x₃) with hFdef
  have h1 : HasFDerivAt (fun x' => f x' x₂ x₃)
      (F.comp ((ContinuousLinearMap.id K X₁).prod 0)) x₁ :=
    HasFDerivAt.comp (f := fun x' : X₁ => (x',x₂,x₃)) x₁ hF
      ((hasFDerivAt_id x₁).prodMk (hasFDerivAt_const (x₂,x₃) x₁))
  have h2 : HasFDerivAt (fun x' => f x₁ x' x₃)
      (F.comp ((0 : X₂ →L[K] X₁).prod (((ContinuousLinearMap.id K X₂).prod 0)))) x₂ :=
    HasFDerivAt.comp (f := fun x' : X₂ => (x₁,x',x₃)) x₂ hF
      ((hasFDerivAt_const x₁ x₂).prodMk ((hasFDerivAt_id x₂).prodMk (hasFDerivAt_const x₃ x₂)))
  have h3 : HasFDerivAt (fun x' => f x₁ x₂ x')
      (F.comp ((0 : X₃ →L[K] X₁).prod ((0 : X₃ →L[K] X₂).prod (ContinuousLinearMap.id K X₃)))) x₃ :=
    HasFDerivAt.comp (f := fun x' : X₃ => (x₁,x₂,x')) x₃ hF
      ((hasFDerivAt_const x₁ x₃).prodMk ((hasFDerivAt_const x₂ x₃).prodMk (hasFDerivAt_id x₃)))
  refine ContinuousLinearMap.ext fun dx => ?_
  obtain ⟨dx₁,dx₂,dx₃⟩ := dx
  simp only [ContinuousLinearMap.mk'_eval, h1.fderiv, h2.fderiv, h3.fderiv,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply]
  rw [← map_add, ← map_add]
  norm_num
