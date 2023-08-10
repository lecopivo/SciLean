import SciLean.Core.Monads.FwdDerivMonad

namespace SciLean

variable 
  {K : Type _} [IsROrC K]
  {ι : Type _} [Fintype ι] [DecidableEq ι]

instance [Vec K X] : Vec K (Id X) := by unfold Id; infer_instance
-- instance [SemiInnerProductSpace K X] : SemiInnerProductSpace K (Id X) := by unfold Id; infer_instance
-- instance [FinVec ι K X] : SemiInnerProductSpace K (Id X) := by unfold Id; infer_instance


  
noncomputable
instance : FwdDerivMonad K Id Id where
  fwdDerivM f := fwdCDeriv K f
  fwdDerivValM x := (x,0)
  IsDifferentiableM f := IsDifferentiable K f
  IsDifferentiableValM _ := True
  fwdDerivM_pure f := by simp[pure]
  fwdDerivM_bind := by intros; simp; ftrans
  fwdDerivM_const y := by simp; ftrans
  IsDifferentiableM_pure := by simp[pure]
  IsDifferentiableM_bind := by simp[bind]; fprop
  IsDifferentiableM_const y := by simp; fprop




variable 
  (K : Type _) [IsROrC K]
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]
  {E : ι → Type} [∀ i, Vec K (E i)]

theorem IsDifferentiableValM.Id (x : Id X) : IsDifferentiableValM K x := True.intro

noncomputable
instance (S : Type _) [Vec K S] : FwdDerivMonad K (StateM S) (StateM (S×S)) where
  fwdDerivM f := fun x dx sds => 
    -- ((y,s'),(dy,ds'))
    let r := fwdCDeriv K (fun (xs : _×S) => f xs.1 xs.2) (x,sds.1) (dx,sds.2)
    -- ((y,dy),(s',ds'))
    ((r.1.1,r.2.1),(r.1.2, r.2.2))

  fwdDerivValM x := fun sds => 
    -- ((y,s'),(dy,ds'))
    let r := fwdCDeriv K x sds.1 sds.2
    -- ((y,dy),(s',ds'))
    ((r.1.1,r.2.1),(r.1.2, r.2.2))

  IsDifferentiableM f := IsDifferentiable K (fun (xs : _×S) => f xs.1 xs.2)
  IsDifferentiableValM x := IsDifferentiable K x

  fwdDerivM_pure f h := 
    by 
      simp[pure, StateT.pure, fwdCDeriv]
      funext x dx sds
      rw[Prod.mk.arg_fstsnd.cderiv_rule (K:=K) (fun xs : _×S => f xs.1) (by fprop) (fun xs : _×S => xs.2) (by fprop)]
      ftrans; ftrans
      
  fwdDerivM_bind f g hf hg :=
    by 
      funext x dx sds
      simp[fwdCDeriv, bind, StateT.bind, StateT.bind.match_1]
      ftrans

  fwdDerivM_const x hx :=
    by 
      funext sds
      simp[fwdCDeriv, bind, StateT.bind, StateT.bind.match_1]
      ftrans

  IsDifferentiableM_pure f :=
    by 
      simp; constructor
      case mp => 
        intros
        simp[pure, StateT.pure]
        apply IsDifferentiable.comp_rule K (fun xs : _×S => (f xs.1, xs.2)) (fun xs => xs) (by fprop) (by fprop)
      case mpr => 
        intros
        simp[pure, StateT.pure]
        let g := Prod.fst ∘ (fun (xs : _×S) => pure (f:=StateM S) (f xs.fst) xs.snd) ∘ (fun x => (x,0))
        have : IsDifferentiable K (Prod.fst ∘ (fun (xs : _×S) => pure (f:=StateM S) (f xs.fst) xs.snd) ∘ (fun x => (x,0))) := by fprop
        have hg : IsDifferentiable K g := by fprop
        rw[show f = g by rfl]
        apply hg

  IsDifferentiableM_IsDifferentiableValM y :=
    by 
      simp; constructor
      intros; fprop
      intro hy
      apply IsDifferentiable.comp_rule K (fun xs : _×S => y xs.2) (fun s : S => (0,s)) hy (by fprop)



variable {ρ : Type _} {α : Type _} [ForIn Id ρ α] {β : Type _}

variable 
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]


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



instance [Vec K X] : Vec K (ForInStep X) := sorry



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
  -- set_option trace.Meta.Tactic.ftrans.step true in
  -- set_option trace.Meta.Tactic.ftrans.theorems true in
  set_option trace.Meta.Tactic.simp.rewrite true in
  -- set_option trace.Meta.Tactic.simp.discharge true in
  -- set_option trace.Meta.Tactic.simp.unify true in
  -- set_option trace.Meta.Tactic.fprop.discharge true in
  -- set_option trace.Meta.Tactic.fprop.step true in
  -- set_option pp.funBinderTypes true in
  -- set_option trace.Meta.isDefEq.onFailure true in
  ftrans only


example : IsDifferentiable ℝ (fun (xy : ℝ × Id ℝ) =>
      let y := xy.snd;
      y) :=
by
  fprop

set_option pp.notation false
--- !!!!INVESTIGATE THIS!!!!
example : cderiv ℝ 
  (fun x : ℝ => 
      bind (m:=Id) (pure x) fun r => 
        let y := r;
        y)
  = 0 := 
by
  -- set_option trace.Meta.Tactic.ftrans.step true in
  -- set_option trace.Meta.Tactic.ftrans.theorems true in
  set_option trace.Meta.Tactic.simp.rewrite true in
  set_option trace.Meta.Tactic.simp.discharge true in
  -- set_option trace.Meta.Tactic.simp.unify true in
  set_option trace.Meta.Tactic.fprop.unify true in
  set_option trace.Meta.Tactic.fprop.discharge true in
  set_option trace.Meta.Tactic.fprop.step true in
  set_option pp.funBinderTypes true in

  -- set_option trace.Meta.isDefEq.onFailure true in
  ftrans only
  dsimp (config := {zeta := false})



example (col : Std.Range)
  : IsDifferentiable ℝ (fun (xy : ℝ × ℝ) => do
      let col : Std.Range := { start := 0, stop := 5, step := 1 }
      let r ←
        forIn col xy.snd (fun (i : ℕ) (r : ℝ) =>
          let y := r;
          let y := i * xy.fst;
          do
          pure PUnit.unit
          pure (f:=Id) (ForInStep.yield y))
      let y : ℝ := r
      y)
  := by fprop


#exit
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

