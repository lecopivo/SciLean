import SciLean.Analysis.Calculus.FDeriv

namespace SciLean

set_option linter.unusedVariables false

variable
  {K : Type _} [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} {nι} [IndexType ι nι]
  {E : ι → Type _} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace K (E j)]

variable (K)

@[fun_trans]
noncomputable
def fwdFDeriv (f : X → Y) (x dx : X) : Y×Y := (f x, fderiv K f x dx)

variable {K}

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

namespace fwdFDeriv

@[fun_trans]
theorem id_rule
  : fwdFDeriv K (fun x : X => x) = fun x dx => (x,dx) :=
by
  unfold fwdFDeriv; fun_trans

@[fun_trans]
theorem const_rule (y : Y) :
    fwdFDeriv K (fun _ : X => y) = fun x dx => (y, 0) := by unfold fwdFDeriv; fun_trans

@[fun_trans]
theorem comp_rule_at (x : X)
    (f : Y → Z) (g : X → Y)
    (hf : DifferentiableAt K f (g x)) (hg : DifferentiableAt K g x) :
    fwdFDeriv K (fun x : X => f (g x)) x
    =
    fun dx =>
      let ydy := fwdFDeriv K g x dx
      let y := ydy.1; let dy := ydy.2
      let zdz := fwdFDeriv K f y dy
      zdz := by
  unfold fwdFDeriv; fun_trans

@[fun_trans]
theorem comp_rule
    (f : Y → Z) (g : X → Y)
    (hf : Differentiable K f) (hg : Differentiable K g) :
    fwdFDeriv K (fun x : X => f (g x))
    =
    fun x dx =>
      let ydy := fwdFDeriv K g x dx
      let y := ydy.1; let dy := ydy.2
      let zdz := fwdFDeriv K f y dy
      zdz := by
  unfold fwdFDeriv; fun_trans


@[fun_trans]
theorem let_rule_at (x : X)
    (f : X → Y → Z) (g : X → Y)
    (hf : DifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x,g x)) (hg : DifferentiableAt K g x) :
    fwdFDeriv K (fun x : X => let y := g x; f x y) x
    =
    fun dx =>
      let ydy := fwdFDeriv K g x dx
      let y := ydy.1; let dy := ydy.2
      let zdz := fwdFDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,y) (dx,dy)
      zdz := by
  funext dx
  unfold fwdFDeriv
  fun_trans

@[fun_trans]
theorem let_rule
    (f : X → Y → Z) (g : X → Y)
    (hf : Differentiable K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : Differentiable K g) :
    fwdFDeriv K (fun x : X => let y := g x; f x y)
    =
    fun x dx =>
      let ydy := fwdFDeriv K g x dx
      let y := ydy.1; let dy := ydy.2
      let zdz := fwdFDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,y) (dx,dy)
      zdz := by funext x; fun_trans

@[fun_trans]
theorem apply_rule (i : ι) :
    fwdFDeriv K (fun (x : (i : ι) → E i) => x i) = fun x dx => (x i, dx i) := by
  unfold fwdFDeriv
  fun_trans


def _root_.Equiv.piProdTranpose {α : Type*} {β γ : α → Type*} :
    ((a : α) → β a × γ a) ≃ (((a : α) → β a) × ((a : α) → γ a)) := {
  toFun f := (fun a => (f a).1, fun a => (f a).2)
  invFun := fun (f,g) a => (f a, g a)
  left_inv := by intro; simp
  right_inv := by intro; simp
}


@[fun_trans]
theorem pi_rule_at (x : X)
    (f : X → (i : ι) → E i) (hf : ∀ i, DifferentiableAt K (f · i) x) :
    fwdFDeriv K (fun (x : X) (i : ι) => f x i) x
    =
    fun dx =>
      let f' := (fun i => fwdFDeriv K (fun x => f x i) x dx)
      Equiv.piProdTranpose f' := by
  unfold fwdFDeriv; fun_trans
  funext x; simp[Equiv.piProdTranpose]
  rw[fderiv_pi (h:=by fun_prop)]
  simp

@[fun_trans]
theorem pi_rule
    (f : X → (i : ι) → E i) (hf : ∀ i, Differentiable K (f · i)) :
    fwdFDeriv K (fun (x : X) (i : ι) => f x i)
    =
    fun x dx =>
      let f' := (fun i => fwdFDeriv K (fun x => f x i) x dx)
      Equiv.piProdTranpose f' := by

  unfold fwdFDeriv; fun_trans
  funext x
  rw[fderiv_pi (h:=by fun_prop)]
  simp[Equiv.piProdTranpose]

-- of linear function ----------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem linear_rule
  (f : X → Y) (hf : IsContinuousLinearMap K f) :
  fwdFDeriv K f
  =
  fun x dx => (f x, f dx) := by unfold fwdFDeriv; fun_trans

end fwdFDeriv


--------------------------------------------------------------------------------

end SciLean
open SciLean


variable
  {K : Type _} [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} {nι} [IndexType ι nι]
  {E : ι → Type _} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace K (E j)]



-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.mk.arg_fstsnd.fwdFDeriv_rule
    (g : X → Y) (hg : Differentiable K g)
    (f : X → Z) (hf : Differentiable K f) :
    fwdFDeriv K (fun x => (g x, f x))
    =
    fun x dx =>
      let ydy := fwdFDeriv K g x dx
      let y := ydy.1; let dy := ydy.2
      let zdz := fwdFDeriv K f x dx
      let z := zdz.1; let dz := zdz.2
      ((y,z), (dy, dz)) := by
  unfold fwdFDeriv; fun_trans


@[fun_trans]
theorem Prod.mk.arg_fstsnd.fwdFDeriv_rule_at (x : X)
    (g : X → Y) (hg : DifferentiableAt K g x)
    (f : X → Z) (hf : DifferentiableAt K f x) :
    fwdFDeriv K (fun x => (g x, f x)) x
    =
    fun dx =>
      let ydy := fwdFDeriv K g x dx
      let y := ydy.1; let dy := ydy.2
      let zdz := fwdFDeriv K f x dx
      let z := zdz.1; let dz := zdz.2
      ((y,z), (dy, dz)) := by
  unfold fwdFDeriv; fun_trans


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.fst.arg_self.fwdFDeriv_rule :
    fwdFDeriv K (fun xy : X×Y => xy.1)
    =
    fun xy dxy => (xy.1, dxy.1) := by
  unfold fwdFDeriv; fun_trans

@[fun_trans]
theorem Prod.fst.arg_self.fwdFDeriv_rule_at (x : X)
    (f : X → Y×Z) (hf : DifferentiableAt K f x) :
    fwdFDeriv K (fun x => (f x).1) x
    =
    fun dx =>
      let yzdyz := fwdFDeriv K f x dx
      let y := yzdyz.1.1; let dy := yzdyz.2.1
      (y,dy) := by
  unfold fwdFDeriv; fun_trans


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.snd.arg_self.fwdFDeriv_rule :
    fwdFDeriv K (fun xy : X×Y => xy.2)
    =
    fun xy dxy => (xy.2, dxy.2) := by
  unfold fwdFDeriv; fun_trans


@[fun_trans]
theorem Prod.snd.arg_self.fwdFDeriv_rule_at (x : X)
    (f : X → Y×Z) (hf : DifferentiableAt K f x) :
    fwdFDeriv K (fun x => (f x).2) x
    =
    fun dx =>
      let yzdyz := fwdFDeriv K f x dx
      let z := yzdyz.1.2; let dz := yzdyz.2.2
      (z,dz) := by
  unfold fwdFDeriv; fun_trans


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.fwdFDeriv_rule_at (x : X)
    (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fwdFDeriv K fun x => f x + g x) x
    =
    fun dx =>
      let ydy := fwdFDeriv K f x dx
      let y := ydy.1; let dy := ydy.2
      let zdz := fwdFDeriv K g x dx
      let z := zdz.1; let dz := zdz.2
      (y + z, dy + dz) := by
  unfold fwdFDeriv; fun_trans


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSub.hSub.arg_a0a1.fwdFDeriv_rule_at (x : X)
    (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fwdFDeriv K fun x => f x - g x) x
    =
    fun dx =>
      let ydy := fwdFDeriv K f x dx
      let y := ydy.1; let dy := ydy.2
      let zdz := fwdFDeriv K g x dx
      let z := zdz.1; let dz := zdz.2
      (y - z, dy - dz) := by
  unfold fwdFDeriv; fun_trans


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.fwdFDeriv_rule (x : X) (f : X → Y) :
    (fwdFDeriv K fun x => - f x) x
    =
    fun dx =>
      let ydy := fwdFDeriv K f x dx
      let y := ydy.1; let dy := ydy.2
      (-y, -dy) := by
  unfold fwdFDeriv; fun_trans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_trans]
theorem HMul.hMul.arg_a0a1.fwdFDeriv_rule
    {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] :
    (fwdFDeriv K fun y : Y×Y => y.1 * y.2)
    =
    fun y dy =>
      let y₁ := y.1; let y₂ := y.2
      let dy₁ := dy.1; let dy₂ := dy.2
      (y₁ * y₂, y₁ * dy₂ + dy₁ * y₂) := by unfold fwdFDeriv; fun_trans


@[fun_trans]
theorem HMul.hMul.arg_a0a1.fwdFDeriv_rule_at (x : X) (f g : X → K)
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fwdFDeriv K fun x => f x * g x) x
    =
    fun dx =>
      let ydy := (fwdFDeriv K f x dx)
      let y := ydy.1; let dy := ydy.2
      let zdz := (fwdFDeriv K g x dx)
      let z := zdz.1; let dz := zdz.2
      (y * z, y * dz + dy * z) := by
  funext dx; unfold fwdFDeriv; fun_trans


-- HSMul.hSMul -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.fwdFDeriv_rule_at (x : X)
    (f : X → K) (g : X → Y)
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fwdFDeriv K fun x => f x • g x) x
    =
    fun dx =>
      let ydy := (fwdFDeriv K f x dx)
      let y := ydy.1; let dy := ydy.2
      let zdz := (fwdFDeriv K g x dx)
      let z := zdz.1; let dz := zdz.2
      (y • z, y • dz + dy • z) := by
  unfold fwdFDeriv; fun_trans


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HDiv.hDiv.arg_a0.fwdFDeriv_rule (y : K) :
    (fwdFDeriv K fun x => x / y)
    =
    fun x dx => (x / y, dx / y) := by
  unfold fwdFDeriv; fun_trans

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.fwdFDeriv_rule_at (x : X)
    (f : X → K) (g : X → K)
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) (hx : g x ≠ 0) :
    (fwdFDeriv K fun x => f x / g x) x
    =
    fun dx =>
      let ydy := (fwdFDeriv K f x dx)
      let y := ydy.1; let dy := ydy.2
      let zdz := (fwdFDeriv K g x dx)
      let z := zdz.1; let dz := zdz.2
      (y / z, (dy * z - y * dz) / z^2) := by
  unfold fwdFDeriv
  funext dx; simp
  conv =>
    lhs
    simp[div_eq_inv_mul]
    fun_trans (disch:=assumption)
  field_simp ; sorry_proof --ring


-- Inv.inv -------------------------------------------------------------------
--------------------------------------------------------------------------------
@[fun_trans]
theorem HInv.hInv.arg_a0a1.fwdFDeriv_rule_at
    (x : X) (f : X → K)
    (hf : DifferentiableAt K f x) (hx : f x ≠ 0) :
    (fwdFDeriv K fun x => (f x)⁻¹) x
    =
    fun dx =>
      let ydy := fwdFDeriv K f x dx
      let y := ydy.1; let dy := ydy.2
      (y⁻¹, -dy / y^2) := by
  unfold fwdFDeriv; fun_trans (disch:=assumption)


-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
def HPow.hPow.arg_a0.fwdFDeriv_rule (n : Nat) :
    fwdFDeriv K (fun x : K => x ^ n)
    =
    fun x dx : K =>
      (x ^ n, n * dx * (x ^ (n-1))) := by
  unfold fwdFDeriv; fun_trans


-- sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

set_option linter.unusedVariables false in
open BigOperators in
@[fun_trans]
theorem FinType.sum.arg_f.fwdFDeriv_rule_at (x : X) (A : Finset ι)
    (f : X → ι → Y) (hf : ∀ i, DifferentiableAt K (f · i) x) :
    fwdFDeriv K (fun x => Finset.sum A (f x)) x
    =
    fun dx =>
      let ydy := fun i => fwdFDeriv K (f · i) x dx
      Finset.sum A ydy := by
  unfold fwdFDeriv; fun_trans
  sorry_proof



@[fun_trans]
theorem sum.arg_f.fwdFDeriv_rule_at {ι nι} [IndexType ι nι] [Fold ι]
  (x : X) (f : X → ι → Y) (hf : ∀ i, DifferentiableAt K (f · i) x)
  : fwdFDeriv K (fun x => IndexType.sum fun i => f x i) x
    =
    fun dx =>
      IndexType.sum fun i =>
        let ydy := fwdFDeriv K (f · i) x dx
        ydy :=
by
  unfold fwdFDeriv;
  fun_trans [sum_push]
  sorry_proof


@[fun_trans]
theorem sum.arg_f.fwdFDeriv_rule {ι nι} [IndexType ι nι] [Fold ι]
  (f : X → ι → Y) (hf : ∀ i, Differentiable K (f · i))
  : fwdFDeriv K (fun x => IndexType.sum fun i => f x i)
    =
    fun x dx =>
      IndexType.sum fun i =>
        let ydy := fwdFDeriv K (f · i) x dx
        ydy :=
by
  funext x; fun_trans



-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem ite.arg_te.fwdFDeriv_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y) :
    fwdFDeriv K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (fwdFDeriv K t y) (fwdFDeriv K e y) := by
  induction dec
  case isTrue h  => ext y; simp[h]; simp[h]
  case isFalse h => ext y; simp[h]; simp[h]

@[fun_trans]
theorem dite.arg_te.fwdFDeriv_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y) (e : ¬c → X → Y) :
    fwdFDeriv K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => fwdFDeriv K (t p) y)
             (fun p => fwdFDeriv K (e p) y) := by
  induction dec
  case isTrue h  => ext y; simp[h]; simp[h]
  case isFalse h => ext y; simp[h]; simp[h]


--------------------------------------------------------------------------------


theorem SciLean.fwdFDeriv_wrt_prod
    {f : X → Y → Z} (hf : Differentiable K ↿f := by fun_prop) :
    fwdFDeriv K (fun xy : X×Y => f xy.1 xy.2)
    =
    fun (xy dxy : X×Y) =>
      let x := xy.1; let y := xy.2
      let dx := dxy.1; let dy := dxy.2
      let zdz₁ := fwdFDeriv K (f · y) x dx
      let zdz₂ := fwdFDeriv K (f x ·) y dy
      let z := zdz₁.1; let dz₁ := zdz₁.2; let dz₂ := zdz₂.2
      (z, dz₁ + dz₂) := by

  unfold fwdFDeriv
  rw[fderiv_wrt_prod hf]
  fun_trans
