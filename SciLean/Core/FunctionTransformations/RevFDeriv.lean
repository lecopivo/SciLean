import SciLean.Core.FunctionTransformations.FDeriv
import SciLean.Core.FunctionTransformations.Adjoint
import SciLean.Mathlib.Analysis.AdjointSpace.Adjoint

set_option linter.unusedVariables false

namespace SciLean


open ContinuousLinearMap

@[fun_trans]
noncomputable
def revFDeriv
  (K : Type _) [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  (f : X → Y) (x : X) : Y×(Y→X) :=
  (f x, adjoint K (fun dx => fderiv K f x dx))

noncomputable
def fgradient
  {K : Type _} [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  (f : X → K) (x : X) : X := (revFDeriv K f x).2 1

namespace revFDeriv

variable
  (K : Type _) [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace K (E i)] [∀ i, CompleteSpace (E i)]


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
theorem proj_rule [DecidableEq ι] (i : ι) :
    revFDeriv K (fun (x : (i' : ι) → E i') => x i)
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
theorem pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, Differentiable K (f · i))
  : (revFDeriv K fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let xdf := fun i =>
        (revFDeriv K fun (x : X) => f x i) x
      (fun i => (xdf i).1,
       fun dy => Finset.univ.sum fun i => (xdf i).2 (dy i))
       := by

  unfold revFDeriv
  simp (disch:=fun_prop) only [fderiv.pi_rule_at]
  fun_trans


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
theorem pi_rule_at
    (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f · i) x) :
    (revFDeriv K fun (x : X) (i : ι) => f x i) x
    =
    let xdf := fun i =>
      (revFDeriv K fun (x : X) => f x i) x
    (fun i => (xdf i).1,
     fun dy => Finset.univ.sum fun i => (xdf i).2 (dy i)) := by

  unfold revFDeriv
  simp (disch:=fun_prop) only [fderiv.pi_rule_at]
  fun_trans


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
    (ydf.1 • zdg.1, fun dx' => ydf.2 (inner zdg.1 dx') + (conj ydf.1) • zdg.2 dx') := by
  unfold revFDeriv
  fun_trans
  funext y; rw[add_comm]; congr
  rw[smul_adjoint (hA:=by fun_prop)]; simp


@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revFDeriv_rule
    (f : X → K) (g : X → Y)
    (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDeriv K fun x => f x • g x)
    =
    fun x =>
      let ydf := revFDeriv K f x
      let zdg := revFDeriv K g x
      (ydf.1 • zdg.1, fun dx' => ydf.2 (inner zdg.1 dx') + (conj ydf.1) • zdg.2 dx') := by

  funext; fun_trans


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

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
