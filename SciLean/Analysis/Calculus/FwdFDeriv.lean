import SciLean.Analysis.Calculus.FDeriv

namespace SciLean


variable
  {K : Type _} [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} [IndexType ι]
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
      let zdz := fwdFDeriv K f ydy.1 ydy.2
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
      let zdz := fwdFDeriv K f ydy.1 ydy.2
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
      let zdz := fwdFDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
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
      let zdz := fwdFDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz := by funext x; fun_trans

@[fun_trans]
theorem apply_rule (i : ι) :
    fwdFDeriv K (fun (x : (i : ι) → E i) => x i) = fun x dx => (x i, dx i) := by
  unfold fwdFDeriv
  fun_trans

@[fun_trans]
theorem pi_rule_at (x : X)
    (f : X → (i : ι) → E i) (hf : ∀ i, DifferentiableAt K (f · i) x) :
    fwdFDeriv K (fun (x : X) (i : ι) => f x i) x
    =
    fun dx =>
      (fun i => f x i, fun i => (fwdFDeriv K (f · i) x dx).2) := by
  unfold fwdFDeriv; fun_trans
  funext x; simp
  rw[fderiv_pi (h:=by fun_prop)]
  simp

@[fun_trans]
theorem pi_rule
    (f : X → (i : ι) → E i) (hf : ∀ i, Differentiable K (f · i)) :
    fwdFDeriv K (fun (x : X) (i : ι) => f x i)
    =
    fun x dx =>
      (fun i => f x i, fun i => (fwdFDeriv K (f · i) x dx).2) := by

  unfold fwdFDeriv; fun_trans
  funext x
  rw[fderiv_pi (h:=by fun_prop)]
  simp

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
  {ι : Type _} [IndexType ι]
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
      let zdz := fwdFDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := by
  unfold fwdFDeriv; fun_trans


@[fun_trans]
theorem Prod.mk.arg_fstsnd.fwdFDeriv_rule_at (x : X)
    (g : X → Y) (hg : DifferentiableAt K g x)
    (f : X → Z) (hf : DifferentiableAt K f x) :
    fwdFDeriv K (fun x => (g x, f x)) x
    =
    fun dx =>
      let ydy := fwdFDeriv K g x dx
      let zdz := fwdFDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := by
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
      (yzdyz.1.1, yzdyz.2.1) := by
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
      (yzdyz.1.2, yzdyz.2.2) := by
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
      let zdz := fwdFDeriv K g x dx
      ydy + zdz := by
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
      let zdz := fwdFDeriv K g x dx
      ydy - zdz  := by
  unfold fwdFDeriv; fun_trans


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.fwdFDeriv_rule (x : X) (f : X → Y) :
    (fwdFDeriv K fun x => - f x) x
    =
    fun dx =>
      let ydy := fwdFDeriv K f x dx
      (-ydy) := by
  unfold fwdFDeriv; fun_trans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_trans]
theorem HMul.hMul.arg_a0a1.fwdFDeriv_rule
    {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] :
    (fwdFDeriv K fun y : Y×Y => y.1 * y.2)
    =
    fun y dy =>
      (y.1 * y.2, y.1 * dy.2 + dy.1 * y.2) := by unfold fwdFDeriv; fun_trans


@[fun_trans]
theorem HMul.hMul.arg_a0a1.fwdFDeriv_rule_at (x : X) (f g : X → K)
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fwdFDeriv K fun x => f x * g x) x
    =
    fun dx =>
      let ydy := (fwdFDeriv K f x dx)
      let zdz := (fwdFDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) := by
  funext dx; unfold fwdFDeriv; fun_trans; simp[mul_comm]


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
      let zdz := (fwdFDeriv K g x dx)
      (ydy.1 • zdz.1, ydy.1 • zdz.2 + ydy.2 • zdz.1) := by
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
      let zdz := (fwdFDeriv K g x dx)
      (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / zdz.1^2) := by
  unfold fwdFDeriv
  funext dx; simp
  conv =>
    lhs
    simp[div_eq_inv_mul]
    fun_trans (disch:=assumption)
  field_simp ; sorry_proof --ring


-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
def HPow.hPow.arg_a0.fwdFDeriv_rule (n : Nat) :
    fwdFDeriv K (fun x : K => x ^ n)
    =
    fun x dx : K =>
      (x ^ n, n * dx * (x ^ (n-1))) := by
  unfold fwdFDeriv; fun_trans


-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

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
theorem IndexType.sum.arg_f.fwdFDeriv_rule_at {ι} [IndexType ι]
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


@[fun_trans]
theorem IndexType.sum.arg_f.fwdFDeriv_rule {ι} [IndexType ι]
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
