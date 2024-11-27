import SciLean
import SciLean.Lean.Meta.Basic

open SciLean Scalar

variable {R} [RealScalar R] [PlainDataType R]

set_default_scalar R

variable {D N K : ℕ}

notation "π" => @RealScalar.pi defaultScalar% inferInstance

#check |(1:ℝ)|

namespace SciLean.MatrixOperations

/-- Matrix determinant -/
def det {I : Type*} [IndexType I] (A : R^[I,I]) : R := sorry

@[inherit_doc det]
scoped macro:max atomic("|" noWs) a:term noWs "|ₘ" : term => `(det $a)

@[app_unexpander det]
def det.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|ₘ) | `(-$_) => `(|($a)|ₘ)
    | _ => `(|$a|ₘ)
  | _ => throw ()

def transpose {I J : Type*} [IndexType I] [IndexType J] (A : R^[I,J]) : R^[J,I] := ⊞ j i => A[i,j]

postfix:max "ᵀ" => transpose

def trace {I : Type*} [IndexType I] (A : R^[I,I]) : R := ∑ i, A[i,i]

scoped instance {I J : Type*} [IndexType I] [IndexType J] : HMul (R^[I,J]) (R^[J]) (R^[I]) where
  hMul A x := ⊞ i => ∑ j, A[i,j] * x[j]

scoped instance {I J K : Type*} [IndexType I] [IndexType J] [IndexType K] : HMul (R^[I,J]) (R^[J,K]) (R^[I,K]) where
  hMul A x := ⊞ i k => ∑ j, A[i,j] * x[j,k]

noncomputable
scoped instance {I : Type*} [IndexType I] [DecidableEq I] : Inv (R^[I,I]) where
  inv A := ⊞ (i j : I) => ⟪ⅇ i,  Function.invFun (fun x : R^[I] => A * x) (ⅇ j)⟫


@[scoped simp, scoped simp_core]
theorem matrix_inverse_inverse {I} [IndexType I] [DecidableEq I] (A : R^[I,I]) :
    (A⁻¹)⁻¹ = A := sorry

@[scoped simp, scoped simp_core]
theorem det_inv_eq_inv_det {I} [IndexType I] [DecidableEq I] (A : R^[I,I]) :
    det A⁻¹ = (det A)⁻¹ := sorry

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
theorem inner_self (x : R^[I]) :
   ⟪x, x⟫ = ‖x‖₂² := sorry

@[scoped simp, scoped simp_core]
theorem gaussian_normalization_invQQT {d : ℕ} (Q : R^[d,d]) :
   (det ((2 * π) • (Q*Qᵀ)⁻¹)) ^ (-(1:R) / 2)
   =
   (2 * π)^(-(d:R)/2) * det Q := sorry

@[scoped simp, scoped simp_core]
theorem gaussian_normalization_invQTQ {d : ℕ} (Q : R^[d,d]) :
   (det ((2 * π) • (Qᵀ*Q)⁻¹)) ^ (-(1:R) / 2)
   =
   (2 * π)^(-(d:R)/2) * det Q := sorry

-- not sure if is shoud be defined for `R^[I]` or `I → R`
def logsumexp (x : R^[I]) : R:=
  let xmax := IndexType.maxD (x[·]) 0
  log (∑ i, exp (x[i] - xmax)) - xmax

-- derivative of `logsumexp` is `softmax`
-- related to `softmax` is `softmax' x y = ⟪softmax x, y⟫`
def softmax' (x dx : R^[I]) : R :=
  let xmax := IndexType.maxD (x[·]) 0
  (∑ i, dx[i] * exp (x[i] - xmax)) / ∑ j, exp (x[j] - xmax)

-- gradient of `logsumexp` is `softmax`
def softmax (x : R^[I]) : R^[I] :=
  let xmax := IndexType.maxD (x[·]) 0
  ⊞ i => exp (x[i] - xmax) / ∑ j, exp (x[j] - xmax)

theorem log_sum_exp (x : I → R) : log (∑ i, exp (x i)) = logsumexp (⊞ i => x i) := sorry

end SciLean.MatrixOperations

open MatrixOperations

noncomputable
def likelihood (x : R^[D]^[N]) (w : R^[K]) (μ : R^[D]^[K]) (σ : R^[D,D]^[K]) : R :=
  ∏ i, ∑ k, w[k] * (det ((2*π) • σ[k]))^(-(1:R)/2) *
    exp (-(1:R)/2 * ⟪x[i] - μ[k], (σ[k]⁻¹ * (x[i] - μ[k]) : R^[D])⟫)

namespace Param

def lowerTriangularIndex (i j : Fin n) (h : i < j) : Fin (((n-1)*n)/2) := sorry

noncomputable
def Q (q : R^[D]) (l : R^[((D-1)*D)/2]) : R^[D,D] :=
  ⊞ i j =>
    if i = j  then exp (q[i])
    else if h : i < j then l[lowerTriangularIndex i j h]
    else 0

def w (α : R^[K]) : R^[K] := ⊞ i => exp α[i] / ∑ k, exp α[k]

@[simp, simp_core]
theorem det_Q (q : R^[D]) (l : R^[((D-1)*D)/2]) : det (Q q l) = exp (∑ i, q[i]) := sorry

@[simp, simp_core]
theorem det_QTQ (q : R^[D]) (l : R^[((D-1)*D)/2]) : det ((Q q l)ᵀ * (Q q l)) = exp (2 * ∑ i, q[i]) := sorry

@[simp, simp_core]
theorem trace_QTQ (q : R^[D]) (l : R^[((D-1)*D)/2]) :
  trace ((Q q l)ᵀ * Q q l)
  = (∑ i, (exp q[i])^2) + ‖l‖₂² := sorry

@[simp, simp_core]
theorem trace_QQT (q : R^[D]) (l : R^[((D-1)*D)/2]) :
  trace (Q q l * (Q q l)ᵀ)
  = (∑ i, (exp q[i])^2) + ‖l‖₂² := sorry

end Param

open Param in
noncomputable
def likelihood' (x : R^[D]^[N]) (α : R^[K]) (μ : R^[D]^[K]) (q : R^[D]^[K]) (l : R^[((D-1)*D)/2]^[K]) : R :=
  likelihood x (w α) μ (⊞ k => ((Q q[k] l[k])ᵀ * Q q[k] l[k])⁻¹)
  rewrite_by
    unfold likelihood
    simp

def prior (m : R) (σ : R^[D,D]^[K]) := ∏ k, /- C(D,m) -/ (det σ[k])^m * exp ((-(1:R)/2) * trace (σ[k])⁻¹)


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
    let one ← mkAppOptM ``One.one #[X, none]

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
      return .done { expr := e', proof? := some proof }

theorem mul_exp (x y : R) : exp x * exp y = exp (x + y) := sorry
theorem log_pow (x y : R) : Scalar.log (x^y) = y * Scalar.log x := sorry


@[simp, simp_core]
theorem IndexType.sum_const {I} [IndexType I] (x : R) :
  (∑ (i : I), x) = (Size.size I : R) • x := sorry

@[simp_core]
theorem neg_add_rev' {G : Type*} [SubtractionCommMonoid G] (a b : G) : -(a + b) = -a + -b := by
  simp[add_comm]


def sum (x : R^[I]) : R := ∑ i, x[i]

@[simp_core]
theorem sum_normalize (x : R^[I]) : ∑ i, x[i] = sum x := rfl

@[simp_core]
theorem norm_normalize (x : R^[I]) : ∑ i, ‖x[i]‖₂² = ‖x‖₂² := rfl

open Param in
noncomputable
def loss (m : R) (x : R^[D]^[N]) (α : R^[K]) (μ : R^[D]^[K]) (q : R^[D]^[K]) (l : R^[((D-1)*D)/2]^[K]) : R :=
  let σ := ⊞ k => ((Q q[k] l[k])ᵀ * Q q[k] l[k])⁻¹
  (- log (likelihood x (w α) μ σ * prior m σ))
  rewrite_by
    unfold likelihood
    simp only [simp_core, likelihood, prior, σ, w]
    simp only [simp_core, mul_pull_from_sum,
               log_mul, log_prod, mul_exp, log_sum_exp, log_pow, log_div, log_inv,sum_push]


variable (x : Fin 10 → R)
#check (∑ i : Fin 10, ((-1:R)/2) * x i) rewrite_by simp [mul_pull_from_sum]
#check (∑ i : Fin 10, -(2* x i)) rewrite_by simp [mul_pull_from_sum]
