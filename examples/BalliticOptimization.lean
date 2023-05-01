import SciLean
import SciLean.Functions.OdeSolve
import SciLean.Solver.Solver 
import SciLean.Core.UnsafeAD


open SciLean
  

def g : ℝ^{2} := (-0.981 : ℝ) • 𝕖[ℝ^{2}] 1

instance [EnumType I] [GenericArrayType XI I X] [ToString X] : ToString XI :=
  ⟨λ x => Id.run do
    let mut s := "["
    for i in fullRange I do
      s := s ++ toString x[i] ++ ", "
    s ++ "]"⟩


variable (γ : ℝ)

noncomputable
opaque argminFun [Nonempty X] (f : X → ℝ) : X 

macro " argmin " x:Lean.Parser.Term.funBinder " , " b:term:66 : term => `(argminFun λ $x => $b)

@[app_unexpander argminFun] def unexpandArgmin : Lean.PrettyPrinter.Unexpander
  | `($(_) λ $x => $b) => 
    `(argmin $x, $b)
  | _  => throw ()

@[app_unexpander invFun] def unexpandInvFun : Lean.PrettyPrinter.Unexpander
  | `($(_) $f) => 
    `($f⁻¹)
  | `($(_) $f $x) => 
    `($f⁻¹ $x)
  | _  => throw ()

theorem invFun_as_argmin {X Y} [Nonempty X] [Hilbert Y] (f : X → Y) (y : Y) (hf : IsInv f)
  : f⁻¹ y = argmin x, ‖f x - y‖² := sorry_proof



structure GradientDescent.Config where
  stepScale : ℝ := 0.1
  maxSteps := 10
  -- absTol : Option ℝ := some (10^(-6))
  -- relTol : Option ℝ := some (10^(-6))

instance : Top (SciLean.Filter GradientDescent.Config) := sorry

-- TODO: define a filter on GradientDescent.Config

def gradientDescent [Vec X] (gradf : X → X) (x₀ : X) (s : ℝ) (steps : Nat) : X := Id.run do
  let mut x := x₀
  for i in [0:steps] do
    x := x - s • gradf x
  x

theorem argminFun.approx.gradientDescent {X} [Hilbert X] {f : X → ℝ} (x₀ : X) (s : ℝ)
  : argmin x, f x 
    =
    limit λ n => gradientDescent (∇ f) x₀ s n
  := sorry_proof






inductive Settings
  | backProp | adjForm


syntax (name := flatten_let_conv) " flatten_let ": conv
syntax (name := flatten_let_tactic) " flatten_let ": tactic

open Lean Meta Elab Tactic Conv


@[tactic flatten_let_conv] def convFlattenLet : Tactic
| `(conv| flatten_let) => do  
  (← getMainGoal).withContext do
    let lhs ← getLhs
    let lhs' ← flattenLet 20 (← instantiateMVars lhs)

    changeLhs lhs'
| _ => Lean.Elab.throwUnsupportedSyntax

@[tactic flatten_let_tactic] def tacticFlattenLet : Tactic
| `(tactic| flatten_let) => do  
  let goal ← getMainGoal
  goal.withContext do
    let t ← goal.getType
    let t' ← flattenLet 20 t

    let newGoal ← mkFreshExprMVar t'
    let eqGoal ← mkFreshExprMVar (← mkEq t t')
    eqGoal.mvarId!.refl

    goal.assign (← mkAppM ``Eq.mpr #[eqGoal, newGoal])
    replaceMainGoal [newGoal.mvarId!]

| _ => Lean.Elab.throwUnsupportedSyntax


def balisticMotion (x v : ℝ^{2}) := (v, g - ‖v‖•v)

function_properties balisticMotion  [UnsafeAD] (x v : ℝ^{2})
argument (x,v)
  IsSmooth,
  abbrev ∂ by unfold balisticMotion; fun_trans; fun_trans,
  def ∂† by unfold balisticMotion; fun_trans; flatten_let; fun_trans; simp,
  def ℛ by unfold balisticMotion; fun_trans; fun_trans; fun_trans; simp
argument x
  IsSmooth,
  HasAdjDiff,
  abbrev ∂† by unfold balisticMotion; fun_trans,
  abbrev ℛ by unfold balisticMotion; fun_trans
argument v 
  IsSmooth,
  HasAdjDiff,
  def ∂† by unfold balisticMotion; fun_trans; fun_trans,
  def ℛ by unfold balisticMotion; fun_trans; fun_trans


variable (v₀ : ℝ^{2}) (s : ℝ) (set : Settings)

#check Lean.Expr.eta

@[simp]
theorem reverseDifferential_fst {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) (x : X)
  : (ℛ f x).fst
    =
    f x
  := by rfl

noncomputable
approx aimToTarget (T : ℝ) (target : ℝ^{2}) :=
  let shoot := λ v : ℝ^{2} => 
               let xv' :=
                 odeSolve (t₀ := 0) (x₀ := (0,v)) (t := T)
                   (f := λ (t : ℝ) (x,v) => balisticMotion x v)
               xv'.1
  shoot⁻¹ target
by
  dsimp (config := {zeta := false})
  
  conv =>
    enter [1,shoot]
    rw [invFun_as_argmin _ _ sorry_proof]
    rw [argminFun.approx.gradientDescent v₀ s]
  
  approx_limit 1; intro gdSteps;
  dsimp (config := {zeta := false})

  have h : ∀ {X} [SemiHilbert X] (f : X → ℝ), ∇ f = λ x => (ℛ f x).2 1 := sorry
  simp (config := {zeta := false}) only [h]

  unsafe_ad
  ignore_fun_prop  
  set_option trace.Meta.Tactic.fun_trans.step true in
  set_option trace.Meta.Tactic.fun_trans.rewrite true in
  set_option trace.Meta.Tactic.simp.rewrite true in
  set_option trace.Meta.Tactic.fun_trans.lambda_special_cases true in
  set_option trace.Meta.Tactic.fun_trans.normalize_let true in
  conv => 
    enter [1]
    fun_trans
    flatten_let
    fun_trans
    flatten_let
    simp (config := {zeta := false, eta := false, iota := false, beta := true, etaStruct := .none, proj := false}) 
    flatten_let
    flatten_let
    dsimp (config := {zeta := false})
    fun_trans
    fun_trans

  

  -- set_option trace.Meta.Tactic.fun_trans.rewrite false in
  -- fun_trans
  -- conv in (reverseDifferential Prod.fst) => fun_trans; fun_trans
  -- conv in (reverseDifferential Prod.fst) => fun_trans; fun_trans
  -- dsimp (config := {zeta := false})
  -- conv in (reverseDifferential _) =>
  --   unfold balisticMotion
    
  

  -- unfold gradient
  -- unsafe_ad
  -- ignore_fun_prop
  -- fun_trans; fun_trans
  -- flatten_let
  -- flatten_let
  -- conv in (adjointDifferential _ _) => fun_trans
  -- dsimp (config := {zeta := false})
  -- flatten_let



#exit
  match set with
  | .adjForm =>
    unfold gradient
    unsafe_ad
    ignore_fun_prop
    fun_trans; fun_trans
    -- alternatives_fst
    unfold balisticMotion
    fun_trans; fun_trans
    flatten_let

#exit

    -- forward pass
    conv in (odeSolve _ _ _ _) =>
      rw [odeSolve_fixed_dt runge_kutta4_step]

    approx_limit 10; intro n';
    dsimp (config := {zeta := false})

    -- backward pass
    conv in (odeSolve _ _ _ _) =>
      rw [odeSolve_fixed_dt runge_kutta4_step]

    approx_limit 10; intro n'';
    dsimp (config := {zeta := false})
    
    apply Approx.exact

  | .backProp => 

    conv in (odeSolve _ _ _ _) =>
      rw [odeSolve_fixed_dt runge_kutta4_step]
    
    approx_limit 10; intro n'';
    dsimp (config := {zeta := false})

    unfold gradient
    simp
    unsafe_ad
    ignore_fun_prop
    -- fun_trans
    apply Approx.exact

