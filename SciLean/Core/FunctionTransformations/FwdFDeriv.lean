import SciLean.Core.FunctionTransformations.FDeriv

namespace SciLean


variable
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace K (E j)]

variable (K)

@[fun_trans]
noncomputable
def fwdFDeriv (f : X → Y) (x dx : X) : Y×Y := (f x, fderiv K f x dx)

variable {K}

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

namespace FwdFDeriv

@[fun_trans]
theorem id_rule
  : fwdFDeriv K (fun x : X => x) = fun x dx => (x,dx) :=
by
  unfold fwdFDeriv; fun_trans

@[fun_trans]
theorem const_rule (y : Y) :
    fwdFDeriv K (fun _ : X => y) = fun x dx => (y, 0) := by unfold fwdFDeriv; fun_trans

@[fun_trans, to_any_point]
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

@[fun_trans, to_any_point]
theorem let_rule_at (x : X)
    (f : X → Y → Z) (g : X → Y)
    (hf : DifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x,g x)) (hg : DifferentiableAt K g x) :
    fwdFDeriv K (fun x : X => let y := g x; f x y) x
    =
    fun dx =>
      let ydy := fwdFDeriv K g x dx
      let zdz := fwdFDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz := by
  unfold fwdFDeriv; fun_trans

@[fun_trans]
theorem apply_rule (i : ι) :
    fwdFDeriv K (fun (x : (i : ι) → E i) => x i) = fun x dx => (x i, dx i) := by
  unfold fwdFDeriv
  fun_trans

@[fun_trans, to_any_point]
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


open SciLean

-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
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

@[fun_trans, to_any_point]
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

@[fun_trans, to_any_point]
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

@[fun_trans, to_any_point]
theorem HAdd.hAdd.arg_a0a1.fwdFDeriv_rule_at (x : X)
    (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fwdFDeriv K fun x => f x + g x) x
    =
    fun dx =>
      fwdFDeriv K f x dx + fwdFDeriv K g x dx := by
  unfold fwdFDeriv; fun_trans


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HSub.hSub.arg_a0a1.fwdFDeriv_rule_at (x : X)
    (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fwdFDeriv K fun x => f x - g x) x
    =
    fun dx =>
      fwdFDeriv K f x dx - fwdFDeriv K g x dx := by
  unfold fwdFDeriv; fun_trans


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.fwdFDeriv_rule (x : X) (f : X → Y) :
    (fwdFDeriv K fun x => - f x) x
    =
    fun dx => - fwdFDeriv K f x dx := by
  unfold fwdFDeriv; fun_trans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
theorem HMul.hMul.arg_a0a1.fwdFDeriv_rule_at (x : X) (f g : X → K)
    (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) :
    (fwdFDeriv K fun x => f x * g x) x
    =
    fun dx =>
      let ydy := (fwdFDeriv K f x dx)
      let zdz := (fwdFDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) := by
  unfold fwdFDeriv; fun_trans


-- HSMul.hSMul -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans, to_any_point]
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

@[fun_trans, to_any_point]
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

@[fun_trans, to_any_point]
def HPow.hPow.arg_a0.fwdFDeriv_rule_at (n : Nat) (x : X)
    (f : X → K) (hf : DifferentiableAt K f x) :
    fwdFDeriv K (fun x => f x ^ n) x
    =
    fun dx =>
      let ydy := fwdFDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) := by
  unfold fwdFDeriv;
  funext dx; simp
  induction n
  case zero => simp
  case h nh => simp[pow_succ]; fun_trans; sorry_proof


-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

open BigOperators in
@[fun_trans, to_any_point]
theorem FinType.sum.arg_f.fwdFDeriv_rule_at (x : X)
    (f : X → ι → Y) (hf : ∀ i, DifferentiableAt K (f · i) x) :
    fwdFDeriv K (fun x => ∑ i, f x i) x
    =
    fun dx =>
      let ydy := fun i => fwdFDeriv K (f · i) x dx
      ∑ i, ydy i := by
  unfold fwdFDeriv; fun_trans
  sorry_proof


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
