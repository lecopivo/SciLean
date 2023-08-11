import SciLean.Core.Monads.FwdDerivMonad
import SciLean.Core.Monads.Id

namespace SciLean

variable 
  {K : Type _} [IsROrC K]
  

-- This is not true but lets assume it for now until I have 
instance [Vec K X] : Vec K (ForInStep X) := sorry

end SciLean
open SciLean

-- set_option linter.unusedVariables false

variable 
  {K : Type _} [IsROrC K]
  {m m'} [Monad m] [Monad m'] [FwdDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {ρ : Type _} {α : Type _} [ForIn m ρ α] [ForIn m' ρ α] {β : Type _}
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]


/-- Turns a pair of values each with yield/done annotation into a pair with
a single yield/done annotation based on the first element. -/
def ForInStep.return2 (x : ForInStep α × ForInStep β) : ForInStep (α × β) :=
  match x.1, x.2 with
  | .yield x₁, .yield x₂ => .yield (x₁, x₂)
  | .yield x₁,  .done x₂ => .yield (x₁, x₂)
  | .done  x₁, .yield x₂ => .done  (x₁, x₂)
  | .done  x₁,  .done x₂ => .done  (x₁, x₂)

def ForInStep.return2Inv (x : ForInStep (α × β)) : ForInStep α × ForInStep β :=
  match x with
  | .yield (x,y) => (.yield x, .yield y)
  | .done (x,y) => (.done x, .done y)


@[simp]
theorem ForInStep.return2_return2Inv_yield {α β} (x : α × β)
  : ForInStep.return2 (ForInStep.return2Inv (.yield x)) = .yield x := by rfl

@[simp]
theorem ForInStep.return2_return2Inv_done {α β} (x : α × β)
  : ForInStep.return2 (ForInStep.return2Inv (.done x)) = .done x := by rfl



-- we need some kind of lawful version of `ForIn` to be able to prove this
@[fprop]
theorem ForIn.forIn.arg_bf.IsDifferentiableM_rule
  (range : ρ) (init : X → Y) (f : X → α → Y → m (ForInStep Y))
  (hinit : IsDifferentiable K init) (hf : ∀ a, IsDifferentiableM K (fun (xy : X×Y) => f xy.1 a xy.2))
  : IsDifferentiableM K (fun x => forIn range (init x) (f x)) := sorry_proof


-- we need some kind of lawful version of `ForIn` to be able to prove this
@[ftrans]
theorem ForIn.forIn.arg_bf.fwdDerivM_rule
  (range : ρ) (init : X → Y) (f : X → α → Y → m (ForInStep Y))
  (hinit : IsDifferentiable K init) (hf : ∀ a, IsDifferentiableM K (fun (xy : X×Y) => f xy.1 a xy.2))
  : fwdDerivM K (fun x => forIn range (init x) (f x)) 
    =
    (fun x dx => do
      let ydy₀ := fwdCDeriv K init x dx
      forIn range ydy₀
        fun a ydy => do 
          let ydy ← fwdDerivM K (fun (xy : X×Y) => f xy.1 a xy.2) (x,ydy.1) (dx,ydy.2)
          return ForInStep.return2 ydy) :=
by
  sorry_proof


@[fprop]
theorem ForInStep.yield.arg_a0.IsDifferentiable_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : IsDifferentiable K fun x => ForInStep.yield (a0 x) := by sorry_proof

@[ftrans]
theorem ForInStep.yield.arg_a0.cderiv_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : cderiv K (fun x => ForInStep.yield (a0 x))
    =
    fun x dx => ForInStep.yield (cderiv K a0 x dx) := by sorry_proof

@[ftrans]
theorem ForInStep.yield.arg_a0.fwdCDeriv_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : fwdCDeriv K (fun x => ForInStep.yield (a0 x))
    =
    fun x dx => ForInStep.return2Inv (ForInStep.yield (fwdCDeriv K a0 x dx))
  := by sorry_proof


@[fprop]
theorem ForInStep.done.arg_a0.IsDifferentiable_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : IsDifferentiable K fun x => ForInStep.done (a0 x) := by sorry_proof

@[ftrans]
theorem ForInStep.done.arg_a0.cderiv_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : cderiv K (fun x => ForInStep.done (a0 x))
    =
    fun x dx => ForInStep.done (cderiv K a0 x dx) := by sorry_proof

@[ftrans]
theorem ForInStep.done.arg_a0.fwdCDeriv_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : fwdCDeriv K (fun x => ForInStep.done (a0 x))
    =
    fun x dx => ForInStep.return2Inv (ForInStep.done (fwdCDeriv K a0 x dx))
  := by sorry_proof




-- example : ForIn.{0, 0, 0, 0} Id.{0} Std.Range Nat := by infer_instance

-- example 
--    : IsDifferentiable ℝ (fun x : ℝ =>
--       let col : Std.Range := { start := 0, stop := 5, step := 1 };
--       forIn (m:=Id) col x (fun i r =>
--         let y := r;
--         let y := y * y;
--         do
--           pure PUnit.unit
--           pure (ForInStep.yield y))) := 
-- by
--   set_option trace.Meta.Tactic.fprop.step true in
--   set_option trace.Meta.Tactic.fprop.missing_rule true in
--   set_option trace.Meta.Tactic.fprop.discharge true in
--   set_option trace.Meta.Tactic.fprop.unify true in
--   set_option trace.Meta.Tactic.fprop.apply true in
--   set_option trace.Meta.Tactic.fprop.rewrite true in
--   set_option trace.Meta.synthInstance true in
--   -- set_option pp.all true in
--   fprop

#check Std.Range.instForInRangeNat


variable [FwdDerivMonad ℝ m m']

example 
  : IsDifferentiable ℝ (fun x : ℝ => Id.run do
  let mut y := x
  for i in [0:5] do
    y := i * y * y + x - x + i
  pure y) := 
by
  fprop

example 
  : IsDifferentiableM ℝ (fun x : ℝ => show m ℝ from do
  let mut y := x
  for i in [0:5] do
    y := i * y * y + x - x + i
  pure y) := 
by
  fprop

-- set_option trace.Meta.Tactic.ftrans.step true in
-- set_option trace.Meta.Tactic.ftrans.theorems true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
-- set_option trace.Meta.Tactic.fprop.discharge true in
-- set_option trace.Meta.Tactic.fprop.step true in
set_option pp.notation false in
set_option trace.Meta.Tactic.ftrans.step true in
-- set_option pp.funBinderTypes true in
-- set_option trace.Meta.isDefEq.onFailure true in

example : fwdCDeriv ℝ (fun x : ℝ => Id.run do
  let mut y := x
  for i in [0:5] do
    y := y * x
  pure y) 
  = 
  fun x dx : ℝ => 0
  := 
by
  -- dsimp
  ftrans only
  -- simp




open Lean Qq in
#eval show MetaM Unit from do
  let e := q(Id.run do
    let mut y := 0
    for i in [0:5] do
      y := y * 2
    pure y) 

  IO.println e
  
