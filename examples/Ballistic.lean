import SciLean
import SciLean.Functions.OdeSolve
import SciLean.Solver.Solver 
import SciLean.Core.UnsafeAD
import SciLean.Tactic.LetUtils
import SciLean.Tactic.LetEnter
import SciLean.Tactic.Basic

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

function_properties balisticMotion (x v : ℝ^{2})
argument (x,v) [UnsafeAD]
  IsSmooth,
  abbrev ∂ by unfold balisticMotion; fun_trans only; fun_trans only,
  def ∂† by unfold balisticMotion; fun_trans; flatten_let; fun_trans; simp,
  def ℛ by unfold balisticMotion; fun_trans; fun_trans; fun_trans; simp
argument x
  IsSmooth,
  HasAdjDiff,
  abbrev ∂† by unfold balisticMotion; fun_trans,
  abbrev ℛ by unfold balisticMotion; fun_trans
argument v [UnsafeAD]
  IsSmooth,
  HasAdjDiff,
  def ∂† by unfold balisticMotion; fun_trans; fun_trans,
  def ℛ by unfold balisticMotion; fun_trans; fun_trans



#check Lean.Expr.eta

-- @[simp]
-- theorem reverseDifferential_fst {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) (x : X)
--   : (ℛ f x).fst
--     =
--     f x
--   := by rfl

#check Prod.neg_mk


theorem gradient_as_revDiff {X} [SemiHilbert X] (f : X → ℝ) 
  : (∇ λ x => f x) = λ x => (ℛ f x).2 1 := by rfl

syntax (name := project_conv) " project ": conv

open Lean Meta Elab Tactic Conv
@[tactic project_conv] def convProject : Tactic
| `(conv| project) => do  
  (← getMainGoal).withContext do
    let lhs ← getLhs
    dbg_trace "Is projection: {lhs.isProj} | {← ppExpr lhs}"
    dbg_trace "Is projection: {(← unfoldDefinition? lhs).get!.isProj} | {← ppExpr lhs}"
    if let some lhs' ← reduceProjFn?' lhs then
      changeLhs lhs'
    
| _ => Lean.Elab.throwUnsupportedSyntax

open Lean.Parser.Tactic in
macro "rw'" " [" s:simpLemma,* "]" : conv => 
  let s' : Syntax.TSepArray `Lean.Parser.Tactic.simpStar "," := ⟨s.1⟩ -- hack
  `(conv| simp (config := {zeta := false, proj := false, beta := false, iota := false, eta := false, singlePass := true, decide := false}) only [$s',*])

open Lean.Parser.Tactic in
macro "rw'" " [" s:simpLemma,* "]" : tactic => 
  let s' : Syntax.TSepArray `Lean.Parser.Tactic.simpStar "," := ⟨s.1⟩ -- hack
  `(tactic| simp (config := {zeta := false, proj := false, beta := false, iota := false, eta := false, singlePass := true, decide := false}) only [$s',*])

#check SciLean.GenericArrayType.instNeg

def a : Neg (ℝ^{2}) := SciLean.GenericArrayType.instNeg 
 
example 
   : a = SubNegMonoid.toNeg
   := 
by
  simp [a,GenericArrayType.instNeg, SubNegMonoid.toNeg, AddGroup.toSubNegMonoid, AddCommGroup.toAddGroup, Vec.toAddCommGroup, SemiHilbert.toVec, Hilbert.toSemiHilbert,FinVec.toHilbert]
  simp [GenericArrayType.instFinVecToEnumType, GenericArrayType.instFinVecProdInstEnumTypeProdToEnumType, GenericArrayType.instHilbert, GenericArrayType.instSemiHilbert, GenericArrayType.instVec, Vec.mkSorryProofs, AddCommGroup.mkSorryProofs, AddGroup.mkSorryProofs]
  simp [SubNegMonoid.mkSorryProofs]
  simp [GenericArrayType.instNeg]
  

-- set_option trace.Meta.Tactic.fun_trans.normalize_let true in
-- set_option trace.Meta.Tactic.fun_trans.rewrite true in
-- set_option trace.Meta.Tactic.simp.congr true in
-- set_option trace.Meta.Tactic.simp.unify true in
-- set_option trace.Meta.Tactic.simp.discharge true in
macro "clean_up" : tactic => `(tactic| conv => enter[1]; dsimp (config := {zeta := false, proj:=false}); flatten_let)

variable (v₀ : ℝ^{2}) (s : ℝ) (set : Settings)

approx aimToTarget := λ (T : ℝ) (target : ℝ^{2}) =>
  let shoot := λ (t : ℝ) (v : ℝ^{2}) =>
                 odeSolve (t₀ := 0) (x₀ := ((0:ℝ^{2}),v)) (t := t)
                   (f := λ (t : ℝ) (x,v) => balisticMotion x v)
  (λ v => (shoot T v).1)⁻¹ target
by
  clean_up
  
  -- reformulate inverse as minimization and apply gradient descent
  conv =>
    enter [1,shoot,T,target]
    rw [invFun_as_argmin _ _ sorry_proof]
    rw [argminFun.approx.gradientDescent v₀ s]
  
  approx_limit 1; intro gdSteps
  clean_up

  rw'[gradient_as_revDiff]

  unsafe_ad; ignore_fun_prop

  -- run automatic differentiation, it gets blocked on `ℛ shoot`
  conv =>
    enter [1]
    fun_trans only
    fun_trans only
    fun_trans only
    fun_trans only
  
  -- deal with `ℛ shoot` manually
  conv =>
    enter[1]; ext
    enter[T,target]
    let_add Rshoot (ℛ (shoot T))
    enter [RShoot]
    rw[(sorry_proof : ℛ (shoot T) = Rshoot)]
  
  let_unfold shoot

  -- run automatic differentiation on `shoot`, this formulates the adjoint problem
  conv =>
    enter [1]
    fun_trans only
    fun_trans only
    fun_trans only
    fun_trans only
    fun_trans only
    fun_trans only
  
  -- precomputed forward pass with RK4 and 50 steps on the interval [0,T] and used linear interpolation
  conv =>
    enter [1]
    enter_let x
    conv =>
      rw[odeSolve_fixed_dt_on_interval
          midpoint_step
          linearInterpolate1D
          T]
  
  approx_limit 50; intro forwardSteps; clean_up
  
  -- Use RK4 with 50 steps on the backward pass
  conv => 
    enter [1]
    enter_let Rfx₂
    enter [dx₀']
    rw[odeSolve_fixed_dt forward_euler_step]
      
  approx_limit 10; intro backwardSteps; clean_up

  apply Approx.exact


approx shoot := λ (t : ℝ) (v : ℝ^{2}) =>
                 odeSolve (t₀ := 0) (x₀ := ((0:ℝ^{2}),v)) (t := t)
                   (f := λ (t : ℝ) (x,v) => balisticMotion x v)
by
  rw[odeSolve_fixed_dt midpoint_step]
      
  approx_limit 50; intro steps; clean_up
  

def aimStep (v₀ : ℝ^{2}) := aimToTarget v₀ (1.0:ℝ) (1:ℝ) (⊞ i, if i=0 then 2 else 0)

def main : IO Unit := do

  let mut v : ℝ^{2} := 0

  for i in [0:200] do
    v := aimStep v
    IO.println v

  let x := (shoot 1 v).1

  IO.println s!"Final destination: {x}"
