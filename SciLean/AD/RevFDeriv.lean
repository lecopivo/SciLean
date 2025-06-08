import SciLean.Analysis.Calculus.FDeriv
import SciLean.Analysis.AdjointSpace.Adjoint

set_option linter.unusedVariables false
set_option deprecated.oldSectionVars true

namespace SciLean

open ContinuousLinearMap

@[fun_trans]
noncomputable
def revFDeriv
  (K : Type _) [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace K Y]
  (f : X → Y) (x : X) : Y×(Y→X) :=
  (f x, adjoint K (fun dx => fderiv K f x dx))

noncomputable
def fgradient
  {K : Type _} [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace K X]
  (f : X → K) (x : X) : X := (revFDeriv K f x).2 1

noncomputable
def adjointFDeriv
  (K : Type _) [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace K Y]
  (f : X → Y) (x : X) (dy : Y) : X := (revFDeriv K f x).2 dy

namespace revFDeriv

variable
  (K : Type u') [RCLike K]
  {X : Type u} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type v} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z : Type w} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]
  {ι : Type _} {nι} [IndexType ι nι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace K (E i)] [∀ i, CompleteSpace (E i)]


-- Basic simp lemmas -----------------------------------------------------------
--------------------------------------------------------------------------------

@[simp, simp_core]
theorem revFDeriv_fst (f : X → Y) (x : X) : (revFDeriv K f x).1 = f x := by rfl


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem id_rule :
    revFDeriv K (fun x : X => x) = fun x => (x, fun dx => dx) := by
  unfold revFDeriv
  fun_trans


@[fun_trans]
theorem const_rule (y : Y) :
    revFDeriv K (fun _ : X => y) = fun x => (y, fun _ => 0) := by
  unfold revFDeriv
  fun_trans


@[fun_trans]
theorem proj_rule
    {n} [IndexType I n] [Fold I] [DecidableEq I]
    {E : I → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace K (E i)] [∀ i, CompleteSpace (E i)] :
    revFDeriv K (fun (x : (i' : I) → E i') => x i)
    =
    fun x =>
      (x i, fun dxi j => if h : i=j then h ▸ dxi else 0) := by
  unfold revFDeriv
  fun_trans


@[fun_trans]
theorem comp_rule
    (f : Y → Z) (g : X → Y)
    (hf : Differentiable K f) (hg : Differentiable K g) :
    revFDeriv K (fun x : X => f (g x))
    =
    fun x =>
      let ydg := revFDeriv K g x
      let zdf := revFDeriv K f ydg.1
      (zdf.1,
       fun dz =>
         let dy := zdf.2 dz
         ydg.2 dy)  := by

  unfold revFDeriv
  fun_trans


@[fun_trans]
theorem let_rule
    (f : X → Y → Z) (g : X → Y)
    (hf : Differentiable K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : Differentiable K g) :
    revFDeriv K (fun x : X => let y := g x; f x y)
    =
    fun x =>
      let ydg := revFDeriv K g x
      let zdf := revFDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz =>
         let dxdy := zdf.2 dz
         let dx := ydg.2 dxdy.2
         dxdy.1 + dx)  := by

  unfold revFDeriv
  fun_trans

@[fun_trans]
theorem pi_rule [Fold ι] [Fold ι] -- these instances have different universes
  (f : X → (i : ι) → E i) (hf : ∀ i, Differentiable K (f · i))
  : (revFDeriv K fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      (fun i => f x i,
       fun dy => IndexType.sum fun i =>
         let dx := (revFDeriv K (f · i) x).2 (dy i)
         dx)
       := by

  unfold revFDeriv
  simp (disch:=fun_prop) only [fderiv.pi_rule_at,adjoint.pi_rule]
  fun_trans
  sorry_proof


@[fun_trans]
theorem comp_rule_at
    (f : Y → Z) (g : X → Y) (x : X)
    (hf : DifferentiableAt K f (g x)) (hg : DifferentiableAt K g x) :
    revFDeriv K (fun x : X => f (g x)) x
    =
    let ydg := revFDeriv K g x
    let zdf := revFDeriv K f ydg.1
    (zdf.1,
     fun dz =>
       let dy := zdf.2 dz
       ydg.2 dy)  := by

  unfold revFDeriv
  fun_trans


@[fun_trans]
theorem let_rule_at
    (f : X → Y → Z) (g : X → Y) (x : X)
    (hf : DifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x,g x)) (hg : DifferentiableAt K g x) :
    revFDeriv K (fun x : X => let y := g x; f x y) x
    =
    let ydg := revFDeriv K g x
    let zdf := revFDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
    (zdf.1,
     fun dz =>
       let dxdy := zdf.2 dz
       let dx := ydg.2 dxdy.2
       dxdy.1 + dx)  := by

  unfold revFDeriv
  fun_trans


@[fun_trans]
theorem pi_rule_at [Fold ι] [Fold ι]
    (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f · i) x) :
    (revFDeriv K fun (x : X) (i : ι) => f x i) x
    =
    (fun i => f x i,
     fun dy => IndexType.sum fun i =>
       let dx := (revFDeriv K (f · i) x).2 (dy i)
       dx) := by
  unfold revFDeriv
  simp (disch:=fun_prop) only [fderiv.pi_rule_at]
  fun_trans
  sorry_proof


end SciLean.revFDeriv

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable
  {K : Type _} [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace K (E i)] [∀ i, CompleteSpace (E i)]


-- of linear function ----------------------------------------------------------
--------------------------------------------------------------------------------

-- @[fun_trans]
theorem revFDeriv_linear
  (f : X → Y) (hf : IsContinuousLinearMap K f) :
  revFDeriv K f
  =
  fun x => (f x, adjoint K f) := by unfold revFDeriv; fun_trans

theorem SciLean.revFDeriv_wrt_prod
    {f : X → Y → Z} (hf : Differentiable K ↿f := by fun_prop) :
    revFDeriv K (fun xy : X×Y => f xy.1 xy.2)
    =
    fun (xy : X×Y) =>
      let x := xy.1; let y := xy.2
      let zdz₁ := revFDeriv K (f · y) x
      let zdz₂ := revFDeriv K (f x ·) y
      let z := zdz₁.1; let dz₁ := zdz₁.2; let dz₂ := zdz₂.2
      (z, fun dz => (dz₁ dz, dz₂ dz)) := by

  unfold revFDeriv
  funext (x,y)
  rw[fderiv_wrt_prod hf]
  fun_trans


-- Prod.mk ----------------------------------- ---------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.Prod.mk.arg_fstsnd.revFDeriv_rule_at
    (g : X → Y) (f : X → Z) (x : X)
    (hg : DifferentiableAt K g x) (hf : DifferentiableAt K f x) :
    revFDeriv K (fun x => Prod.mk (g x) (f x)) x
    =
    let ydg := revFDeriv K g x
    let zdf := revFDeriv K f x
    ((ydg.1,zdf.1), fun dyz => ydg.2 dyz.1 + zdf.2 dyz.2) := by

  unfold revFDeriv
  fun_trans


@[fun_trans]
theorem SciLean.Prod.mk.arg_fstsnd.revFDeriv_rule
  (g : X → Y) (f : X → Z)
  (hg : Differentiable K g) (hf : Differentiable K f)
  : revFDeriv K (fun x => Prod.mk (g x) (f x))
    =
    fun x =>
      let ydg := revFDeriv K g x
      let zdf := revFDeriv K f x
      ((ydg.1,zdf.1), fun dyz => ydg.2 dyz.1 + zdf.2 dyz.2) := by

  funext x; fun_trans


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.Prod.fst.arg_self.revFDeriv_rule_at
    (f : X → Y×Z) (x : X) (hf : DifferentiableAt K f x) :
    revFDeriv K (fun x => (f x).1) x
    =
    let yzdf := revFDeriv K f x
    (Prod.fst yzdf.1, fun dy => yzdf.2 (dy,0)) := by

  unfold revFDeriv
  fun_trans

@[fun_trans]
theorem SciLean.Prod.fst.arg_self.revFDeriv_rule
    (f : X → Y×Z) (hf : Differentiable K f) :
    revFDeriv K (fun x => (f x).1)
    =
    fun x =>
      let yzdf := revFDeriv K f x
      (Prod.fst yzdf.1, fun dy => yzdf.2 (dy,0)) := by

  funext x; fun_trans


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.Prod.snd.arg_self.revFDeriv_rule_at
    (f : X → Y×Z) (x : X) (hf : DifferentiableAt K f x) :
    revFDeriv K (fun x => Prod.snd (f x)) x
    =
    let yzdf := revFDeriv K f x
    (Prod.snd yzdf.1, fun dz => yzdf.2 (0,dz)) := by

  unfold revFDeriv
  fun_trans

@[fun_trans]
theorem SciLean.Prod.snd.arg_self.revFDeriv_rule
    (f : X → Y×Z) (hf : Differentiable K f) :
    revFDeriv K (fun x => Prod.snd (f x))
    =
    fun x =>
      let yzdf := revFDeriv K f x
      (Prod.snd yzdf.1, fun dz => yzdf.2 (0,dz)) := by

  funext x
  fun_trans


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revFDeriv_rule_at
    (f g : X → Y) (x : X) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (revFDeriv K fun x => f x + g x) x
    =
    let ydf := revFDeriv K f x
    let ydg := revFDeriv K g x
    (ydf.1 + ydg.1, fun dy => ydf.2 dy + ydg.2 dy) := by

  unfold revFDeriv
  fun_trans


@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revFDeriv_rule
    (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDeriv K fun x => f x + g x)
    =
    fun x =>
      let ydf := revFDeriv K f x
      let ydg := revFDeriv K g x
      (ydf.1 + ydg.1, fun dy => ydf.2 dy + ydg.2 dy) := by

  funext; fun_trans


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSub.hSub.arg_a0a1.revFDeriv_rule_at
    (f g : X → Y) (x : X) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (revFDeriv K fun x => f x - g x) x
    =
    let ydf := revFDeriv K f x
    let ydg := revFDeriv K g x
    (ydf.1 - ydg.1, fun dy => ydf.2 dy - ydg.2 dy) := by

  unfold revFDeriv
  fun_trans

@[fun_trans]
theorem HSub.hSub.arg_a0a1.revFDeriv_rule
    (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDeriv K fun x => f x - g x)
    =
    fun x =>
      let ydf := revFDeriv K f x
      let ydg := revFDeriv K g x
      (ydf.1 - ydg.1, fun dy => ydf.2 dy - ydg.2 dy) := by

  funext; fun_trans


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.revFDeriv_rule
    (f : X → Y) (x : X) :
    (revFDeriv K fun x => - f x) x
    =
    let ydf := revFDeriv K f x
    (-ydf.1, fun dy => - ydf.2 dy) := by

  unfold revFDeriv; fun_trans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate

@[fun_trans]
theorem HMul.hMul.arg_a0a1.revFDeriv_rule_at
    (f g : X → K) (x : X)
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (revFDeriv K fun x => f x * g x) x
    =
    let ydf := revFDeriv K f x
    let zdg := revFDeriv K g x
    (ydf.1 * zdg.1, fun dx' => (conj zdg.1) • ydf.2 dx' + (conj ydf.1) • zdg.2 dx') := by

  unfold revFDeriv; fun_trans; ac_rfl


@[fun_trans]
theorem HMul.hMul.arg_a0a1.revFDeriv_rule
    (f g : X → K)
    (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDeriv K fun x => f x * g x)
    =
    fun x =>
      let ydf := revFDeriv K f x
      let zdg := revFDeriv K g x
      (ydf.1 * zdg.1, fun dx' => (conj zdg.1) • ydf.2 dx' + (conj ydf.1) • zdg.2 dx') := by

  funext; fun_trans


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revFDeriv_rule_at
    (f : X → K) (g : X → Y) (x : X)
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (revFDeriv K fun x => f x • g x) x
    =
    let ydf := revFDeriv K f x
    let zdg := revFDeriv K g x
    (ydf.1 • zdg.1, fun dx' => ydf.2 (inner K zdg.1 dx') + (conj ydf.1) • zdg.2 dx') := by
  unfold revFDeriv
  fun_trans
  funext y; rw[add_comm]; congr
  simp[smul_push]


@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revFDeriv_rule
    (f : X → K) (g : X → Y)
    (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDeriv K fun x => f x • g x)
    =
    fun x =>
      let ydf := revFDeriv K f x
      let zdg := revFDeriv K g x
      (ydf.1 • zdg.1, fun dx' => ydf.2 (inner K zdg.1 dx') + (conj ydf.1) • zdg.2 dx') := by

  funext; fun_trans


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HDiv.hDiv.arg_a0.revFDeriv_rule_at
    (f : X → K) (c : K) (x : X)
    (hf : DifferentiableAt K f x) :
    (revFDeriv K fun x => f x / c) x
    =
    let ydf := revFDeriv K f x
    (ydf.1 / c,
     fun dx' => (conj c)⁻¹ • ydf.2 dx') := by

  unfold revFDeriv
  fun_trans


@[fun_trans]
theorem HDiv.hDiv.arg_a0.revFDeriv_rule
    (f : X → K) (c : K)
    (hf : Differentiable K f) :
    (revFDeriv K fun x => f x / c)
    =
    fun x =>
      let ydf := revFDeriv K f x
      (ydf.1 / c,
       fun dx' => (conj c)⁻¹ • ydf.2 dx') := by
  funext
  fun_trans


@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revFDeriv_rule_at
    (f g : X → K) (x : X)
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) (hx : g x ≠ 0) :
    (revFDeriv K fun x => f x / g x) x
    =
    let ydf := revFDeriv K f x
    let zdg := revFDeriv K g x
    (ydf.1 / zdg.1,
     fun dx' => ((conj zdg.1)^2)⁻¹ • (conj zdg.1 • ydf.2 dx' - conj ydf.1 • zdg.2 dx')) := by

  unfold revFDeriv
  fun_trans (disch:=assumption)


@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revFDeriv_rule
    (f g : X → K)
    (hf : Differentiable K f) (hg : Differentiable K g) (hx : ∀ x, g x ≠ 0) :
    (revFDeriv K fun x => f x / g x)
    =
    fun x =>
      let ydf := revFDeriv K f x
      let zdg := revFDeriv K g x
      (ydf.1 / zdg.1,
       fun dx' => ((conj zdg.1)^2)⁻¹ • (conj zdg.1 • ydf.2 dx' - conj ydf.1 • zdg.2 dx')) := by

  funext
  fun_trans (disch:=apply hx)


-- Inv.inv -------------------------------------------------------------------
--------------------------------------------------------------------------------
@[fun_trans]
theorem HInv.hInv.arg_a0a1.revFDeriv_rule_at
    (x : X) (f : X → K)
    (hf : DifferentiableAt K f x) (hx : f x ≠ 0) :
    (revFDeriv K fun x => (f x)⁻¹) x
    =
    let ydf := revFDeriv K f x
    let y := ydf.1
    let df := ydf.2
    (y⁻¹, fun dy => - (conj y^2)⁻¹ • (df dy)) := by
  unfold revFDeriv; fun_trans (disch:=assumption)


-- HPow.hPow ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
def HPow.hPow.arg_a0.revFDeriv_rule_at
  (f : X → K) (x : X) (n : Nat) (hf : DifferentiableAt K f x)
  : revFDeriv K (fun x => f x ^ n) x
    =
    let ydf := revFDeriv K f x
    (ydf.1 ^ n, fun dx' => (n * (conj ydf.1 ^ (n-1))) • ydf.2 dx') :=
by unfold revFDeriv; fun_trans
   simp only [mul_comm, ← mul_smul]


@[fun_trans]
def HPow.hPow.arg_a0.revFDeriv_rule
    (f : X → K) (n : Nat) (hf : Differentiable K f) :
    revFDeriv K (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revFDeriv K f x
      (ydf.1 ^ n, fun dx' => (n * (conj ydf.1 ^ (n-1))) • ydf.2 dx') := by

  funext; fun_trans



-- sum -------------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_trans]
theorem IndexType.sum.arg_f.revFDeriv_rule_at {I n} [IndexType I n] [Fold I]
  (x : X) (f : X → I → Y) (hf : ∀ i, DifferentiableAt K (f · i) x)
  : revFDeriv K (fun x => ∑ᴵ i, f x i) x
    =
    (∑ᴵ i, f x i,
     fun dy =>
       ∑ᴵ (i : I),
         let dx := adjointFDeriv K (f · i) x dy
         dx) :=

by
  unfold revFDeriv;
  fun_trans [adjointFDeriv,revFDeriv]
  simp (disch:=fun_prop) [fderiv.pi_rule_at]


@[fun_trans]
theorem IndexType.sum.arg_f.revFDeriv_rule {I n} [IndexType I n] [Fold I]
  (f : X → I → Y) (hf : ∀ i, Differentiable K (f · i))
  : revFDeriv K (fun x => ∑ᴵ i, f x i)
    =
    fun x =>
    (∑ᴵ i, f x i,
     fun dy =>
       ∑ᴵ i,
         let dx := adjointFDeriv K (f · i) x dy
         dx) := by funext x; fun_trans
