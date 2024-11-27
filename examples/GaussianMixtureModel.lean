import SciLean
import SciLean.Data.DataArray.Operations.Simps
import SciLean.Lean.Meta.Basic

open SciLean Scalar

section Missing

variable
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y]

@[fun_prop]
theorem ite.arg_te.Differentiable_rule {c : Prop} [h : Decidable c]
  (t e : X → Y) (ht : Differentiable R t) (he : Differentiable R e) :
  Differentiable R (fun x => ite c (t x) (e x)) := by split_ifs <;> assumption

@[fun_prop]
theorem dite.arg_te.Differentiable_rule {c : Prop} [h : Decidable c]
  (t : c → X → Y) (e : ¬c → X → Y) (ht : ∀ h, Differentiable R (t h)) (he : ∀ h, Differentiable R (e h)) :
  Differentiable R (fun x => dite c (t · x) (e · x)) := by split_ifs <;> aesop

end Missing

variable {R} [RealScalar R] [PlainDataType R]

set_default_scalar R

variable {D N K : ℕ}


namespace SciLean.MatrixOperations

@[scoped simp, scoped simp_core]
theorem matrix_inverse_inverse {I} [IndexType I] [DecidableEq I] (A : R^[I,I]) (hA : A.Invertible) :
    (A⁻¹)⁻¹ = A := by simp[hA]

@[scoped simp, scoped simp_core]
theorem det_inv_eq_inv_det {I} [IndexType I] [DecidableEq I] (A : R^[I,I]) :
    (A⁻¹).det = (A.det)⁻¹ := by simp

variable {I J K : Type*} [IndexType I] [IndexType J] [IndexType K]

@[scoped simp, scoped simp_core]
theorem inner_QQT (x y : R^[I]) (Q : R^[I,J]) :
   ⟪x, Q*Qᵀ*y⟫ = ⟪Qᵀ*x,Qᵀ*y⟫ := by sorry

@[scoped simp, scoped simp_core]
theorem inner_QQT' (x y : R^[I]) (Q : R^[I,J]) :
   ⟪x, Q*(Qᵀ*y)⟫ = ⟪Qᵀ*x,Qᵀ*y⟫ := sorry

@[scoped simp, scoped simp_core]
theorem inner_QTQ (x y : R^[J]) (Q : R^[I,J]) :
   ⟪x, Qᵀ*Q*y⟫ = ⟪Q*x,Q*y⟫ := sorry

@[scoped simp, scoped simp_core]
theorem inner_QTQ' (x y : R^[J]) (Q : R^[I,J]) :
   ⟪x, Qᵀ*(Q*y)⟫ = ⟪Q*x,Q*y⟫ := sorry

@[scoped simp, scoped simp_core]
theorem gaussian_normalization_invQQT {d : ℕ} (Q : R^[d,d]) :
   (((2 * π) • (Q*Qᵀ)⁻¹).det) ^ (-(1:R) / 2)
   =
   (2 * π)^(-(d:R)/2) * Q.det := sorry

@[scoped simp, scoped simp_core]
theorem gaussian_normalization_invQTQ {d : ℕ} (Q : R^[d,d]) :
   (((2 * π) • (Qᵀ*Q)⁻¹).det) ^ (-(1:R) / 2)
   =
   (2 * π)^(-(d:R)/2) * Q.det := sorry

-- -- not sure if is shoud be defined for `R^[I]` or `I → R`
-- def logsumexp (x : R^[I]) : R:=
--   let xmax := IndexType.maxD (x[·]) 0
--   log (∑ i, exp (x[i] - xmax)) - xmax

-- -- derivative of `logsumexp` is `softmax`
-- -- related to `softmax` is `softmax' x y = ⟪softmax x, y⟫`
-- def softmax' (x dx : R^[I]) : R :=
--   let xmax := IndexType.maxD (x[·]) 0
--   (∑ i, dx[i] * exp (x[i] - xmax)) / ∑ j, exp (x[j] - xmax)

-- -- gradient of `logsumexp` is `softmax`
-- def softmax (x : R^[I]) : R^[I] :=
--   let xmax := IndexType.maxD (x[·]) 0
--   ⊞ i => exp (x[i] - xmax) / ∑ j, exp (x[j] - xmax)

theorem log_sum_exp (x : I → R) : log (∑ i, exp (x i)) = (⊞ i => x i).logsumexp := sorry

end SciLean.MatrixOperations

open MatrixOperations

noncomputable
def likelihood (x : R^[D]^[N]) (w : R^[K]) (μ : R^[D]^[K]) (σ : R^[D,D]^[K]) : R :=
  ∏ i, ∑ k, w[k] * (((2*π) • σ[k]).det)^(-(1:R)/2) *
    exp (-(1:R)/2 * ⟪x[i] - μ[k], (σ[k]⁻¹ * (x[i] - μ[k]) : R^[D])⟫)

namespace Param

def lowerTriangularIndex (i j : Fin n) (h : i < j) : Fin (((n-1)*n)/2) :=
  ⟨i.1, sorry⟩

def Q (q : R^[D]) (l : R^[((D-1)*D)/2]) : R^[D,D] :=
  ⊞ (i j : Fin D) =>
    if i = j then exp (q[i])
    else if i < j then l[lowerTriangularIndex i j sorry]
    else 0


#check ite
-- {α : Sort u} → (c : Prop) → [h : Decidable c] → α → α → α


example (l : R^[n]) : Differentiable R fun (q : R) (i : Fin m) =>
            if i.1 < 5 then q
            else if h : i.1 < n then l[⟨i.1,h⟩] else 0 := by
  set_option trace.Meta.Tactic.fun_prop true in
  fun_prop


set_option trace.Meta.Tactic.fun_prop true in
example (l : R^[((D-1)*D)/2]) : Differentiable R fun (q : R^[D]) (p : Fin D × Fin D) =>
            if p.1 = p.2 then SciLean.Scalar.exp q[p.1]
            else if h : p.1 < p.2 then l[Param.lowerTriangularIndex p.1 p.2 h] else 0 := by
  fun_prop

set_option trace.Meta.Tactic.fun_trans true in
def_fun_trans (l : R^[((D-1)*D)/2]) : fwdFDeriv R (fun q : R^[D] => Param.Q q l) by
  unfold Q
  simp[Function.HasUncurry.uncurry]
  -- autodiff -- casuses panic
  fun_trans

#exit

@[simp, simp_core]
theorem det_Q (q : R^[D]) (l : R^[((D-1)*D)/2]) : (Q q l).det = exp q.sum := sorry



@[simp, simp_core]
theorem det_QTQ (q : R^[D]) (l : R^[((D-1)*D)/2]) : ((Q q l)ᵀ * (Q q l)).det = exp (2 * q.sum) := sorry

@[simp, simp_core]
theorem QTQ_invertible (q : R^[D]) (l : R^[((D-1)*D)/2]) : ((Q q l)ᵀ * (Q q l)).Invertible := sorry

@[simp, simp_core]
theorem trace_QTQ (q : R^[D]) (l : R^[((D-1)*D)/2]) :
  ((Q q l)ᵀ * Q q l).trace
  = ‖q.exp‖₂² + ‖l‖₂² := sorry

@[simp, simp_core]
theorem trace_QQT (q : R^[D]) (l : R^[((D-1)*D)/2]) :
  (Q q l * (Q q l)ᵀ).trace
  = ‖q.exp‖₂² + ‖l‖₂² := sorry

end Param





open Param in
noncomputable
def likelihood' (x : R^[D]^[N]) (α : R^[K]) (μ : R^[D]^[K]) (q : R^[D]^[K]) (l : R^[((D-1)*D)/2]^[K]) : R :=
  likelihood x (α.softmax) μ (⊞ k => ((Q q[k] l[k])ᵀ * Q q[k] l[k])⁻¹)
  rewrite_by
    unfold likelihood
    simp

noncomputable
def prior (m : R) (σ : R^[D,D]^[K]) := ∏ k, /- C(D,m) -/ (σ[k].det)^m * exp ((-(1:R)/2) * ((σ[k])⁻¹).trace)

theorem log_prod {I} [IndexType I] (x : I → R) : log (∏ i, x i) = ∑ i, log (x i) := sorry

open Lean Meta
/-- Take expression full of multiplications and divitions and split it into lists of
  multiplication and division factors.

For example:
```
e = x₁ * x₂         ==> [x₁,x₂] []
e = x₁ * x₂ / y₁    ==> [x₁,x₂] [y₁]
e = x₁ / (y₁/x₂)    ==> [x₁,x₂] [y₁]
e = x₁ * x₂ / y₁ * (x₃ * x₄) / (y₂/x₅)`
                    ==> [x₁,x₂,x₃,x₄,x₄] [y₁,y₂]
```
-/
partial def parse (e : Expr) : Option (List Expr × List Expr × Bool) :=
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, e₁, e₂]) => do
    match parse e₁, parse e₂ with
    | .none, .none => return ([e₁,e₂], [], false)
    | .some (m₁,d₁,neg₁), .none => return (m₁ ++ [e₂], d₁, neg₁)
    | .none, .some (m₂,d₂,neg₂) => return ([e₁] ++ m₂, d₂, neg₂)
    | .some (m₁,d₁, neg₁), .some (m₂,d₂, neg₂) => return (m₁ ++ m₂, d₁ ++ d₂, neg₁ ^^ neg₂)
  | (``HDiv.hDiv, #[_, _, _, _, e₁, e₂]) =>
    match parse e₁, parse e₂ with
    | none, none => return ([e₁], [e₂], false)
    | .some (m₁,d₁, neg₁), .none => return (m₁, d₁ ++ [e₂], neg₁)
    | .none, .some (m₂,d₂,neg₂) => return (e₁ :: d₂, m₂, neg₂)
    | .some (m₁,d₁,neg₁), .some (m₂,d₂,neg₂) => return (m₁ ++ d₂, d₁ ++ m₂, neg₁ ^^ neg₂)
  | (``Neg.neg, #[_, _, e]) =>
    match parse e with
    | none => return ([e],[],true)
    | some (m,d,neg) => return (m,d,!neg)
  | (``Inv.inv, #[_, _, e]) =>
    match parse e with
    | none => return ([],[e],true)
    | some (m,d,neg) => return (d,m,!neg)
  | _ => return ([e],[],false)


open Qq Lean Meta Mathlib.Tactic in
simproc_decl mul_pull_from_sum (IndexType.sum _) := fun e => do
  let f := e.appArg!
  Lean.Meta.lambdaBoundedTelescope f 1 fun is b => do
    let i := is[0]!

    let .some (m,d,neg) := parse b | return .continue
    let (m₁,m₂) := m.toArray.split (fun e => ¬(e.containsFVar i.fvarId!))
    let (d₁,d₂) := d.toArray.split (fun e => ¬(e.containsFVar i.fvarId!))

    -- skip if all factors depend on the index
    unless m₁.size ≠ 0 ∨ d₁.size ≠ 0 do return .continue

    let X ← inferType b
    let one ← mkAppOptM ``OfNat.ofNat #[X, Expr.lit (.natVal 1), none]

    let merge := fun (m d : Array Expr) => do
      match m.size, d.size with
      | 0, 0 => pure one
      | _, 0 => mkAppFoldlM ``HMul.hMul m
      | 0, _ => mkAppM ``Inv.inv #[← mkAppFoldlM ``HMul.hMul d]
      | _, _ => mkAppM ``HDiv.hDiv #[← mkAppFoldlM ``HMul.hMul m, ← mkAppFoldlM ``HMul.hMul d]

    let mut e₁ ← merge m₁ d₁
    if neg then
       e₁ ← mkAppM ``Neg.neg #[e₁]
    let e₂ ← merge m₂ d₂

    let mut e' ← mkLambdaFVars #[i] e₂
    e' ← mkAppM ``IndexType.sum #[e']
    e' ← mkAppM ``HMul.hMul #[e₁,e']

    -- if nothing changes there is no need to pulute the proof with sorry
    if e.eqv e' then
       return .continue
    else
      let proof ← mkSorry (← mkEq e e') false
      -- IO.println s!"running simproc on {← ppExpr e}"
      -- IO.println s!"simplified to {← ppExpr e'}"
      -- TODO: here we should have `visit` but it gets into infinite loop :(
      return .done { expr := e', proof? := some proof }

theorem mul_exp (x y : R) : exp x * exp y = exp (x + y) := sorry
theorem log_pow (x y : R) : Scalar.log (x^y) = y * Scalar.log x := sorry

attribute [-simp_core] SciLean.ArrayType.sum_ofFn
attribute [rsimp] SciLean.ArrayType.sum_ofFn

#check SciLean.IndexType.sum_add_distrib

@[rsimp]
theorem IndexType.sum_const {I} [IndexType I] (x : R) :
  (∑ (i : I), x) = (Size.size I : R) • x := sorry

@[simp_core]
theorem neg_add_rev' {G : Type*} [SubtractionCommMonoid G] (a b : G) : -(a + b) = -a + -b := by
  simp[add_comm]


def sum (x : R^[I]) : R := ∑ i, x[i]

@[rsimp]
theorem sum_normalize (x : R^[I]) : ∑ i, x[i] = sum x := rfl

@[rsimp]
theorem norm_normalize (x : R^[I]) : ∑ i, ‖x[i]‖₂² = ‖x‖₂² := rfl

-- theorem sum_over_prod {R} [AddCommMonoid R] {I J : Type*} [IndexType I] [IndexType J]
--     {f : I → J → R} : ∑ i j, f i j = ∑ (i : I×J), f i.1 i.2  := sorry

@[rsimp]
theorem isum_sum (x : R^[I]^[J]) : ∑ i, x[i].sum = x.uncurry.sum := by
  simp[DataArrayN.uncurry_def,DataArrayN.sum,Function.HasUncurry.uncurry]
  rw[sum_over_prod]

@[rsimp]
theorem isum_norm_exp (x : R^[I]^[J]) :
    ∑ j, ‖x[j].exp‖₂² = ‖x.uncurry.exp‖₂² := by
  simp[DataArrayN.uncurry_def,DataArrayN.sum,Function.HasUncurry.uncurry,
       DataArrayN.norm2_def,DataArrayN.exp]
  rw[sum_over_prod]

@[rsimp]
theorem isum_norm (x : R^[I]^[J]) :
    ∑ j, ‖x[j]‖₂² = ‖x.uncurry‖₂² := by
  simp[DataArrayN.uncurry_def,DataArrayN.sum,Function.HasUncurry.uncurry,
       DataArrayN.norm2_def]
  rw[sum_over_prod]

open Param in
noncomputable
def loss (m : R) (x : R^[D]^[N]) (α : R^[K]) (μ : R^[D]^[K]) (q : R^[D]^[K]) (l : R^[((D-1)*D)/2]^[K]) : R :=
  let σ := ⊞ k => ((Q q[k] l[k])ᵀ * Q q[k] l[k])⁻¹
  (- log (likelihood x (α.softmax) μ σ /-* prior m σ -/))
  rewrite_by
    unfold likelihood
    simp only [DataArrayN.softmax_spec, DataArrayN.softmaxSpec]
    simp only [simp_core, likelihood, prior, σ]
    simp only [simp_core, mul_pull_from_sum, refinedRewritePost, sum_push,
               log_mul, log_prod, mul_exp, log_sum_exp, log_pow, log_div, log_inv]
    simp only [simp_core]
    ring_nf

#exit

def_fun_trans loss in α : fwdFDeriv R by
  unfold loss
  autodiff

def_fun_trans loss in α : revFDeriv R by
  unfold loss
  autodiff


def_fun_trans loss in μ : fwdFDeriv R by
  unfold loss
  autodiff


def_fun_trans loss in α μ : fwdFDeriv R by
  unfold loss
  autodiff


-- attribute [-simp_core] revFDeriv_on_DataArrayN

-- def_fun_trans loss in μ : revFDeriv R by
--   unfold loss
--   autodiff


-- def_fun_trans loss in q : fwdFDeriv R by
--   unfold loss
--   autodiff


-- def_fun_trans loss in l : fwdFDeriv R by
--   unfold loss
--   autodiff




set_option pp.raw true in
#check (1 : ℝ)
variable (x : Fin 10 → R)
#check (∑ i : Fin 10, ((-1:R)/2) * x i) rewrite_by simp [mul_pull_from_sum]
#check (∑ i : Fin 10, -(2* x i)) rewrite_by simp [mul_pull_from_sum]
