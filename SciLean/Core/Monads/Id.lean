import SciLean.Core.Objects.FinVec
import SciLean.Core.FunctionTransformations.CDeriv

namespace SciLean

variable 
  {K : Type _} [IsROrC K]
  {ι : Type _} [Fintype ι] [DecidableEq ι]

instance [Vec K X] : Vec K (Id X) := by unfold Id; infer_instance
instance [SemiInnerProductSpace K X] : SemiInnerProductSpace K (Id X) := by unfold Id; infer_instance
instance [FinVec ι K X] : SemiInnerProductSpace K (Id X) := by unfold Id; infer_instance


instance [Vec K X] : Vec K (ForInStep X) := sorry


variable {ρ : Type _} {α : Type _} [ForIn Id ρ α] {β : Type _}

variable 
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]


@[fprop]
theorem _root_.ForIn.forIn.arg_bf.IsDifferentiable_rule [Vec K β]
  (range : ρ) (init : X → β) (f : X → α → β → Id (ForInStep β))
  (hinit : IsDifferentiable K init) (hf : ∀ a, IsDifferentiable K (fun (xb : X×β) => f xb.1 a xb.2))
  : IsDifferentiable K (fun x => forIn range (init x) (f x)) := sorry_proof

@[ftrans]
theorem _root_.ForIn.forIn.arg_bf.cderiv_rule [Vec K β]
  (range : ρ) (init : X → β) (f : X → α → β → Id (ForInStep β))
  (hinit : IsDifferentiable K init) (hf : ∀ a, IsDifferentiable K (fun (xb : X×β) => f xb.1 a xb.2))
  : cderiv K (fun x => forIn range (init x) (f x)) 
    =
    (fun x dx => Id.run do
      let dinit := cderiv K init x dx
      let (r,dr) ←
        forIn range (init x, dinit) 
          fun a (s,ds) => Id.run do 
            let s' ← f x a s
            let ds' ← cderiv K (fun (xb : X×β) => f xb.1 a xb.2) (x,s) (dx,ds)
            match s', ds' with
            | .yield s', .yield ds' => .yield (s', ds')
            | .yield s',  .done ds' => .yield (s', ds')
            | .done  s', .yield ds' => .done  (s', ds')
            | .done  s',  .done ds' => .done  (s', ds')
      dr) := 
by
  sorry_proof


@[fprop]
theorem _root_.Id.run.arg_x.IsDifferentiable_rule
  (a : X → Id Y)
  (ha : IsDifferentiable K a)
  : IsDifferentiable K (fun x => Id.run (a x)) := by unfold Id.run; fprop


@[ftrans]
theorem _root_.Id.run.arg_x.cderiv_rule (a : X → Id Y)
  : cderiv K (fun x => Id.run (a x))
    =
    fun x dx => (cderiv K a x dx) := by unfold Id.run; ftrans


@[fprop] 
theorem _root_.Bind.bind.arg_a0a1.IsDifferentiable_rule
  (a0 : X → Id Y) (a1 : X → Y → Id Z)
  (ha0 : IsDifferentiable K a0) (ha1 : IsDifferentiable K (fun (xy : X×Id Y) => a1 xy.1 xy.2))
  : IsDifferentiable K (fun x => Bind.bind (a0 x) (a1 x)) := 
by 
  simp[Bind.bind]; fprop

@[ftrans] 
theorem _root_.Bind.bind.arg_a0a1.cderiv_rule
  (a0 : X → Id Y) (a1 : X → Y → Id Z)
  (ha0 : IsDifferentiable K a0) (ha1 : IsDifferentiable K (fun (xy : X×Id Y) => a1 xy.1 xy.2))
  : cderiv K (fun x => Bind.bind (a0 x) (a1 x))
    =
    fun x dx => 
      let a0x := a0 x
      let da0 := cderiv K a0 x dx
      let da1 := cderiv K (fun (xy : X×Y) => a1 xy.1 xy.2) (x, a0x) (dx, da0)
      da1 := 
by 
  simp[Bind.bind]
  ftrans only; funext x dx; congr 

@[fprop]
theorem _root_.Pure.pure.arg_a0.IsDifferentiable_rule
  (a0 : X → Y)
  (ha0 : IsDifferentiable K a0) 
  : IsDifferentiable K (fun x => Pure.pure (f:=Id) (a0 x)) := by simp[Pure.pure]; fprop

@[ftrans]
theorem _root_.Pure.pure.arg_a0.cderiv_rule
  (a0 : X → Y)
  (ha0 : IsDifferentiable K a0) 
  : cderiv K (fun x => Pure.pure (f:=Id) (a0 x))
    =
    cderiv K a0 := by simp[Pure.pure]


@[fprop]
theorem _root_.ForInStep.yield.arg_a0.IsDifferentiable_rule
  (a0 : X → Y)
  (ha0 : IsDifferentiable K a0)
  : IsDifferentiable K fun x => ForInStep.yield (a0 x) := by sorry_proof


@[ftrans]
theorem _root_.ForInStep.yield.arg_a0.cderiv_rule
  (a0 : X → Y)
  (ha0 : IsDifferentiable K a0)
  : cderiv K (fun x => ForInStep.yield (a0 x))
    =
    fun x dx => ForInStep.yield (cderiv K a0 x dx) := by sorry_proof


@[fprop]
theorem _root_.ForInStep.done.arg_a0.IsDifferentiable_rule
  (a0 : X → Y)
  (ha0 : IsDifferentiable K a0)
  : IsDifferentiable K fun x => ForInStep.done (a0 x) := by sorry_proof

@[ftrans]
theorem _root_.ForInStep.done.arg_a0.cderiv_rule
  (a0 : X → Y)
  (ha0 : IsDifferentiable K a0)
  : cderiv K (fun x => ForInStep.done (a0 x))
    =
    fun x dx => ForInStep.done (cderiv K a0 x dx) := by sorry_proof



example : ForIn.{0, 0, 0, 0} Id.{0} Std.Range Nat := by infer_instance

end SciLean

open SciLean

example 
   : IsDifferentiable ℝ (fun x : ℝ =>
      let col : Std.Range := { start := 0, stop := 5, step := 1 };
      forIn (m:=Id) col x (fun i r =>
        let y := r;
        let y := y * y;
        do
          pure PUnit.unit
          pure (ForInStep.yield y))) := 
by
  set_option trace.Meta.Tactic.fprop.step true in
  set_option trace.Meta.Tactic.fprop.missing_rule true in
  set_option trace.Meta.Tactic.fprop.discharge true in
  set_option trace.Meta.Tactic.fprop.unify true in
  set_option trace.Meta.Tactic.fprop.apply true in
  set_option trace.Meta.Tactic.fprop.rewrite true in
  set_option trace.Meta.synthInstance true in
  -- set_option pp.all true in
  fprop

#check Std.Range.instForInRangeNat


example : IsDifferentiable ℝ (fun x : ℝ => Id.run do
  let mut y := x
  for i in [0:5] do
    y := i * y * y + x - x + i
  y) := 
by
  fprop




example : cderiv ℝ (fun x : ℝ => Id.run do
  let mut y := x
  for i in [0:5] do
    y := i*x
  y)
  = 0 := 
by
  set_option trace.Meta.Tactic.ftrans.step true in
  set_option trace.Meta.Tactic.ftrans.theorems true in
  set_option trace.Meta.Tactic.simp.rewrite true in
  set_option trace.Meta.Tactic.simp.discharge true in
  set_option trace.Meta.Tactic.simp.unify true in
  set_option trace.Meta.Tactic.fprop.discharge true in
  set_option trace.Meta.Tactic.fprop.step true in
  set_option pp.funBinderTypes true in
  ftrans only


example 
  : IsDifferentiable ℝ fun (xy : (ℝ × ℝ) × Id ℝ) =>
      let y := xy.snd;
      y
  := 
by
  set_option trace.Meta.Tactic.fprop.step true in
  fprop


  

#exit

@[fprop]
theorem _root_.ForIn.forIn.arg_bf.IsDifferentiable_rule [Vec K β] [Vec K X]
  (range : ρ) (init : X → β) (f : X → α → β → Id (ForInStep β))
  (hinit : IsDifferentiable K init) (hf : ∀ a, IsDifferentiable K (fun (xb : X×β) => f xb.1 a xb.2))
  : cderiv K (fun x => forIn range (init x) (f x)) := sorry_proof

