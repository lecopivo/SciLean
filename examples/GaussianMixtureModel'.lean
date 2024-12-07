import SciLean
import SciLean.Tactic.DataSynth.DefRevDeriv
import SciLean.Data.DataArray.Operations.GaussianN


open SciLean Scalar SciLean.Meta


section Missing


variable
  {R : Type} [RealScalar R] [PlainDataType R]
  {X : Type} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace R Y]

variable {I : Type} [IndexType I]

theorem log_sum_exp (x : I → R) : log (∑ i, exp (x i)) = (⊞ i => x i).logsumexp := sorry_proof

end Missing


section Missing

variable {R} [RealScalar R]
variable {I : Type} [IndexType I]

theorem log_prod (x : I → R) : log (∏ i, x i) = ∑ i, log (x i) := sorry_proof
theorem mul_exp (x y : R) : exp x * exp y = exp (x + y) := sorry_proof
theorem log_pow (x y : R) : Scalar.log (x^y) = y * Scalar.log x := sorry_proof

@[rsimp]
theorem IndexType.sum_const {X} [AddCommGroup X] (x : X) :
  (∑ (i : I), x) = Size.size I • x := sorry_proof

end Missing

variable {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar R

namespace SciLean.MatrixOperations

variable {I J K : Type} [IndexType I] [IndexType J] [IndexType K]
variable (x y : R^[I]) (u v : R^[J]) (Q : R^[I,J])

theorem inner_QQT  : ⟪x, Q*Qᵀ*y⟫   = ⟪Qᵀ*x,Qᵀ*y⟫ := by sorry_proof
theorem inner_QQT' : ⟪x, Q*(Qᵀ*y)⟫ = ⟪Qᵀ*x,Qᵀ*y⟫ := by sorry_proof
theorem inner_QTQ  : ⟪u, Qᵀ*Q*v⟫   = ⟪Q*u,Q*v⟫ := by sorry_proof
theorem inner_QTQ' : ⟪u, Qᵀ*(Q*v)⟫ = ⟪Q*u,Q*v⟫ := by sorry_proof

attribute [scoped simp, scoped simp_core] inner_QQT inner_QQT' inner_QTQ inner_QTQ'


@[scoped simp, scoped simp_core]
theorem gaussian_normalization_invQQT {d : ℕ} (Q : R^[d,d]) :
   (((2 * π) • (Q*Qᵀ)⁻¹).det) ^ (-(1:R) / 2)
   =
   (2 * π)^(-(d:R)/2) * Q.det := sorry_proof

@[scoped simp, scoped simp_core]
theorem gaussian_normalization_invQTQ {d : ℕ} (Q : R^[d,d]) :
   (((2 * π) • (Qᵀ*Q)⁻¹).det) ^ (-(1:R) / 2)
   =
   (2 * π)^(-(d:R)/2) * Q.det := sorry_proof

end SciLean.MatrixOperations

open MatrixOperations

noncomputable
def likelihood (x : R^[D]^[N]) (w : R^[K]) (μ : R^[D]^[K]) (σ : R^[D,D]^[K]) : R :=
  ∏ i, ∑ k, w[k] * gaussianN (μ[k]) (σ[k]) (x[i])

namespace Param

def Q (q : R^[D]) (l : R^[((D-1)*D)/2]) : R^[D,D] := q.exp.diag + l.lowerTriangular D 1

def_rev_deriv Q in q l by
  unfold Q
  data_synth => lsimp

def_rev_deriv' Q in q l by
  unfold Q
  data_synth => lsimp


variable (q : R^[D]) (l : R^[((D-1)*D)/2])

-- properties of parametrization
theorem det_Q : (Q q l).det = exp q.sum := sorry_proof
theorem det_QTQ : ((Q q l)ᵀ * (Q q l)).det = exp (2 * q.sum) := sorry_proof
theorem QTQ_invertible : ((Q q l)ᵀ * (Q q l)).Invertible := sorry_proof
theorem trace_QTQ : ((Q q l)ᵀ * Q q l).trace = ‖q.exp‖₂² + ‖l‖₂² := sorry_proof

attribute [simp, simp_core] det_Q det_QTQ QTQ_invertible trace_QTQ
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


attribute [-simp_core] SciLean.ArrayType.sum_ofFn
attribute [rsimp] SciLean.ArrayType.sum_ofFn

#check SciLean.IndexType.sum_add_distrib



@[simp_core]
theorem neg_add_rev' {G : Type*} [SubtractionCommMonoid G] (a b : G) : -(a + b) = -a + -b := by
  simp[add_comm]


@[rsimp]
theorem sum_normalize (x : R^[I]) : ∑ i, x[i] = x.sum := rfl

-- TODO: this theorem replaces (∑ i, ‖x[i]‖₂²) with (∑ i, ‖x[i]‖₂²) instead of ‖x‖₂²
--       there must be some issue with transparency
omit [PlainDataType R] in
@[rsimp]
theorem norm_normalize {X} [PlainDataType X] [NormedAddCommGroup X] [AdjointSpace R X] (x : X^[I]) : (∑ i, ‖x[i]‖₂²) = ‖x‖₂² := rfl

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
    (∑ j, ‖x[j]‖₂²) = ‖x.uncurry‖₂² := by
  simp[DataArrayN.uncurry_def,DataArrayN.sum,Function.HasUncurry.uncurry,
       DataArrayN.norm2_def]
  rw[sum_over_prod]


open Param Scalar in
noncomputable
def loss (m : R) (x : R^[D]^[N]) (α : R^[K]) (μ : R^[D]^[K]) (q : R^[D]^[K]) (l : R^[((D-1)*D)/2]^[K]) : R :=
  let σ := ⊞ k => ((Q q[k] l[k])ᵀ * Q q[k] l[k])⁻¹
  (- log (likelihood x (α.softmax) μ σ * prior m σ))
  rewrite_by
    unfold likelihood
    simp only [simp_core, likelihood, prior, σ, DataArrayN.softmax_def]
    simp only [simp_core, mul_pull_from_sum, refinedRewritePost, sum_push,
               log_mul, log_prod, mul_exp, log_sum_exp, log_pow, log_div, log_inv]
    ring_nf

set_option pp.deepTerms.threshold 10000
set_option maxHeartbeats 10000000

macro "cleanup_pass" : conv => `(conv| lsimp (config:={singlePass:=true}) only [simp_core, ↓prodFunSimproc])


set_option profiler true
set_option trace.Meta.Tactic.data_synth.profile true
def_rev_deriv loss in α μ q l by
  unfold loss
  lsimp
  data_synth => skip


#exit
variable (x : R → R^[n]) (x' xi')
         (hx : HasRevFDerivUpdate R x x')
         (hxi : ∀ i, HasRevFDerivUpdate R (fun w => (x w)[i]) xi')
         (i : Fin n)

def_rev_deriv loss in x by
  unfold loss
  lsimp
  data_synth => skip


set_option trace.Meta.Tactic.data_synth true in
#check (HasRevFDerivUpdate R (fun w => (x w)[i] * (x w)[i]) _)
  rewrite_by
    data_synth

def foo (x y : R^[n]) := ‖⊞ i => x[i] + y[i]‖₂²

def_rev_deriv foo in x y by
  unfold foo
  data_synth => lsimp
