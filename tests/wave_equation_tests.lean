import SciLean
import SciLean.Core.IsInv
import SciLean.Core.InvFun

open SciLean

-- Tests to necessary to get wave equation example to work


example 
  : ∂ (λ (x : Fin n → ℝ) => ∑ i, ‖ x i‖²)
    =
    λ x dx => ∑ i, 2 * ⟪dx i, x i⟫
  := by fun_trans


example {ι} [Enumtype ι]
  : ∂ (λ (x : ι → ℝ) => ∑ i, ‖ x i ‖²)
    =
    λ x dx => ∑ i, 2 * ⟪dx i, x i⟫
  := by fun_trans

example 
  : ∇ (λ (x : Fin n → ℝ) => ∑ i, ‖ x i ‖²)
    =
    λ x i => 2 * x i
  := by 
    conv => lhs; unfold gradient; fun_trans; fun_trans


example 
  : ∇ (λ (x : Fin n → ℝ) => ∑ i, ‖ x i ‖²)
    =
    λ x i => 2 * x i
  := by 
    conv => 
      lhs; unfold gradient; unfold adjointDifferential
      fun_trans; fun_trans; fun_trans
      simp (config := {zeta := false})
      simp

def _root_.Fin.shift (x : Fin n) (y : Int) : Fin n := ⟨((x.1 + y) % n).toNat, sorry⟩

set_option trace.Meta.Tactic.fun_trans.rewrite true in
example 
  : ∇ (λ (x : Fin n → ℝ) => ∑ i, ‖ x i + x (i.shift 1)‖²)
    =
    λ x i => 2 * x i
  := by 
    conv => lhs; unfold gradient; unfold adjointDifferential; fun_trans; fun_trans; fun_trans; simp (config := {zeta := false})


function_properties Fin.shift {n} [Nonempty (Fin n)] (x : Fin n) (y : Int)
argument x
  IsInv := sorry_proof,
  abbrev ⁻¹ := λ x' => x'.shift (-y) by sorry_proof

example [Nonempty (Fin n)]
  : ∂† (λ (x : Fin n → ℝ) i => ‖ x i - x (i.shift 1)‖²)
    =
    sorry
  :=
by
  let f := λ (i : Fin n) (xi : ℝ) (g : Fin n → ℝ) => ‖ xi - g (i.shift 1)‖²
  rw[adjointDifferential.rule_piComp' f (λ i => i)]
  funext g dg'
  simp only [adjointDifferential.rule_piComp (λ j x => ‖g j - x‖²) (λ i => i.shift 1)]

  dsimp; fun_trans; fun_trans; simp


-- open FunctionTransformation Lean Meta Qq

-- #eval show MetaM Unit from do

--   let e := q(
--     λ (x : Fin 10 → ℝ) =>
--       let df := fun (i : Fin 10) => 1;
--       fun i : Fin 10 =>
--         let x' := x i;
--         let dx := 2 * df i * x';
--       dx)
--   lambdaTelescope e λ xs e => do

--     let f := e.letValue!

--     let normalizeCondition : Bool := ¬(f.hasAnyFVar (λ _ => true)) && ¬f.hasLooseBVars
--     IO.println s!"{← ppExpr f} has free variables {(f.hasAnyFVar (λ _ => true))}"
--     IO.println s!"{← ppExpr f} has loose bound variables {(f.hasLooseBVars)}"
--     IO.println s!"{← ppExpr f} should normalize let binding {normalizeCondition}"

--     if let some e' := normalizeLet? e then
--       IO.println s!"{← ppExpr e'}"

-- set_option pp.funBinderTypes true in
-- set_option trace.Meta.Tactic.fun_trans.step true in
-- set_option trace.Meta.Tactic.fun_trans.normalize_let true in
-- set_option trace.Meta.Tactic.fun_trans.rewrite true in
#exit
def shift (x : Fin n) (y : Int) : Fin n := ⟨((x.1 + y) % n).toNat, sorry⟩


-- BUG in function transform!!!
set_option pp.funBinderTypes true
set_option trace.Meta.Tactic.fun_trans.step true in
set_option trace.Meta.Tactic.fun_trans.rewrite true in
example 
  : ∂ (λ (x : Fin n → ℝ) => ∑ (i : Fin n), ‖(x (id i))‖²)
    =
    sorry
  := by 
    conv => lhs; unfold gradient; fun_trans


set_option trace.Meta.Tactic.fun_trans.step true in
-- set_option trace.Meta.Tactic.fun_trans.rewrite true in
set_option trace.Meta.Tactic.fun_trans.lambda_special_cases true in
example 
  : ∂ (λ (x : Fin n → ℝ) (i : Fin n) => (x i) + (x (id i)))
    =
    sorry
  := by 
    conv => lhs; unfold gradient; fun_trans

example (x : Fin n → ℝ)
  :  x i + x (id i) = ((fun (i : Fin n) => x i) + fun (i : Fin n) => x (id i)) i
  := by rfl


example {n : Nat} : 
    differential (fun (t : Fin n → ℝ ) => sum fun (i : Fin n) =>  ‖ t i ‖²)
    =
    fun (t dt : Fin n → ℝ ) =>
      let df' := differential (fun (x : Fin n → ℝ ) (i : Fin n) =>  ‖ x (id i) ‖² ) t dt;
      sum df'
:= sorry

variable (t dt : Fin 10 → ℝ)

#check let_val_congr sum
    (congrFun (congrFun (Inner.normSqr.arg_x.differential_simp' fun (x : Fin 10 → ℝ) => x) t) dt)


example {T : Type} [inst : Vec T] {X : Type} [inst : Hilbert X] (x : T → X)
  [inst : IsSmooth x] :
  (differential fun t =>  ‖ x t ‖² ) = fun t dt =>
    let x' := x t;
    let dx' := differential x t dt;
    2 * ⟪dx', x'⟫
  := sorry
#check Inner.normSqr.arg_x.differential_simp'

-- #check let_val_congr (fun df' : Fin 10 → ℝ => sum df')
--     (congrFun (congrFun (Inner.normSqr.arg_x.differential_simp' fun (x : ℝ → Fin 10 → ℝ) (i : Fin 10) => x (shift i 1)) t) dt)

-- #check Inner.normSqr.arg_x.differential_simp'

-- #check  (congrFun (congrFun (Inner.normSqr.arg_x.differential_simp' fun (x : ℝ → Fin 10 → ℝ) (i : Fin 10) => x (shift i 1)) t) dt)


-- def foo := (congrFun (congrFun (Inner.normSqr.arg_x.differential_simp' fun (x : ℝ → Fin 10 → ℝ) (i : Fin 10) => x (shift i 1)) t) dt)

-- open Lean Meta Qq
-- #eval show MetaM Unit from do

--   let hihi := q(λ t dt => foo t dt)

--   lambdaTelescope hihi λ xs b => do
--     let B ← inferType b
--     IO.println s!"type : {← ppExpr B}"
--     IO.println s!"is eq : {(B.isAppOf ``Eq)}"

section Bug



opaque t : Nat → Fin 10 → Nat
opaque dt : Nat → Fin 10 → Nat

opaque diff {α β} (f : α → β) : α → α → β := λ a _ => f a
opaque norm2 {α} (a : α) : Nat 
opaque inner {α} (a b : α) : Nat

def compTheorem {T : Type} {X : Type} (x : T → X)
  :
  (diff fun t =>  norm2 (x t) ) = fun t dt => inner (diff x t dt) (x t)
  := sorry

#check let_val_congr (fun df' : Fin 10 → Nat => sum' df')
    (congrFun (congrFun (compTheorem fun (x : Nat → Fin 10 → Nat) (i : Fin 10) => x (shift i 1)) t) dt)
