import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

import SciLean.Tactic.FunTrans.Attr
import SciLean.Tactic.FunTrans.Elab

import SciLean.Analysis.Normed.IsContinuousLinearMap

open SciLean

variable
  {K : Type _} [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]

namespace SciLean

attribute [fun_trans] fderiv

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
    rw[fderiv_comp x hf (DifferentiableAt.prod (by simp) hg)]
    rw[DifferentiableAt.fderiv_prod (by simp) hg]
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

@[fun_trans]
theorem fderiv.pi_rule_at
    (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f · i) x) :
    (fderiv K fun (x : X) (i : ι) => f x i) x
    =
    fun dx =>L[K] fun i =>
      fderiv K (f · i) x dx := fderiv_pi hf

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
  apply DifferentiableAt.fderiv_prod hg hf



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
      y * dz + dy * z := by
  ext dx
  simp[fderiv_mul hf hg, mul_comm]



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
    DifferentiableAt R (fun w => a0 w / a1 w) w := sorry_proof

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
  ext dx
  have h : ∀ (f : X → K) x, fderiv K f x dx = deriv (fun h : K => f (x + h•dx)) 0 := by sorry_proof
  simp[h]
  rw[deriv_div (c:=(fun h => f (x + h • dx))) (d:=(fun h => g (x + h • dx)))
               (hc:=by sorry_proof) (hd:= by sorry_proof)
               (hx:=by simp; assumption)]
  simp


-- Inv.inv -------------------------------------------------------------------
--------------------------------------------------------------------------------
set_option linter.unusedVariables false in
@[fun_prop]
theorem _root_.Inv.inv.arg_a0.DifferentiableAt_rule
    {R} [RCLike R]
    {W} [NormedAddCommGroup W] [NormedSpace R W]
    (w : W) (a0 : W → R)
    (ha0 : DifferentiableAt R a0 w) (ha0' : a0 w ≠ 0) :
    DifferentiableAt R (fun w => (a0 w)⁻¹) w := sorry_proof

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
  rw[fderiv_comp']
  rw[fderiv_inv]
  simp; ring
  apply differentiableAt_inv hx
  apply hf


-- HPow.hPow ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
def HPow.hPow.arg_a0.fderiv_rule_at (n : Nat) (x : X)
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
    simp_rw[pow_succ]
    rw[HMul.hMul.arg_a0a1.fderiv_rule_at x _ f (by fun_prop) (by fun_prop)]
    rw[hn]
    induction n
    case zero => simp
    case succ =>
      rw[show ∀ (n : Nat), n.succ - 1 = n by simp]
      rw[pow_succ]
      simp; ring


-- sum -------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem IndexType.sum.arg_f.fderiv_rule_at {ι} [IndexType ι]
  (x : X) (f : X → ι → Y) (hf : ∀ i, DifferentiableAt K (f · i) x)
  : fderiv K (fun x => IndexType.sum fun i => f x i) x
    =
    fun dx =>L[K]
      IndexType.sum fun i =>
        let dy := fderiv K (f · i) x dx
        dy :=
by
  ext dx
  fun_trans [ContinuousLinearMap.mk']
  rw[fderiv.pi_rule_at]; simp
  apply hf

@[fun_trans]
theorem IndexType.sum.arg_f.fderiv_rule {ι} [IndexType ι]
  (f : X → ι → Y) (hf : ∀ i, Differentiable K (f · i))
  : fderiv K (fun x => IndexType.sum fun i => f x i)
    =
    fun x => fun dx =>L[K]
      IndexType.sum fun i =>
        let dy := fderiv K (f · i) x dx
        dy :=
by
  funext x; fun_trans
