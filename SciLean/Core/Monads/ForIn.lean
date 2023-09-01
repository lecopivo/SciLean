import SciLean.Core.Monads.FwdDerivMonad
import SciLean.Core.Monads.Id

set_option linter.unusedVariables false

namespace SciLean

variable 
  {K : Type _} [IsROrC K]
  
-- This is not true but lets assume it for now until I have 
instance [Vec K X] : Vec K (ForInStep X) := sorry

-- This is not true but lets assume it for now until I have 
instance [SemiInnerProductSpace K X] : SemiInnerProductSpace K (ForInStep X) := sorry


end SciLean
open SciLean

-- set_option linter.unusedVariables false

def ForInStep.val : ForInStep α → α
| .yield a => a
| .done  a => a


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


section OnVec

variable 
  {K : Type _} [IsROrC K]
  {m m'} [Monad m] [Monad m'] [FwdDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {ρ : Type _} {α : Type _} [ForIn m ρ α] [ForIn m' ρ α] {β : Type _}
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]


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

-- Proof that the above theorem is true for the range [0:3] and function that does not break the for loop
example
  (init : X → Y) (f : X → Nat → Y → m Y)
  (hinit : IsDifferentiable K init) (hf : ∀ a, IsDifferentiableM K (fun (xy : X×Y) => f xy.1 a xy.2))
  : fwdDerivM K (fun x => forIn [0:3] (init x) (fun i y => do pure (ForInStep.yield (← f x i y)))) 
    =
    (fun x dx => do
      let ydy₀ := fwdCDeriv K init x dx
      forIn [0:3] ydy₀
        fun a ydy => do 
          let ydy ← fwdDerivM K (fun (xy : X×Y) => f xy.1 a xy.2) (x,ydy.1) (dx,ydy.2)
          return .yield ydy) :=
by
  simp [forIn,Std.Range.forIn,Std.Range.forIn.loop,Std.Range.forIn.loop.match_1]
  ftrans


@[fprop]
theorem ForInStep.yield.arg_a0.IsDifferentiable_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : IsDifferentiable K fun x => ForInStep.yield (a0 x) := by sorry_proof

-- this is a hack as with Id monad sometimes you do not need `pure` which trips `fprop` up
@[fprop]
theorem ForInStep.yield.arg_a0.IsDifferentiableM_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : IsDifferentiableM (m:=Id) K fun x => ForInStep.yield (a0 x) := by sorry_proof

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

-- this is a hack as with Id monad sometimes you do not need `pure` which trips `fprop` up
@[fprop]
theorem ForInStep.done.arg_a0.IsDifferentiableM_rule
  (a0 : X → Y) (ha0 : IsDifferentiable K a0)
  : IsDifferentiableM (m:=Id) K fun x => ForInStep.done (a0 x) := by sorry_proof

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

end OnVec



section OnSemiInnerProductSpace

variable 
  {K : Type _} [IsROrC K]
  {m m'} [Monad m] [Monad m'] [RevDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {ρ : Type _} {α : Type _} [ForIn m ρ α] [ForIn m' ρ α] {β : Type _}
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]


-- we need some kind of lawful version of `ForIn` to be able to prove this
@[fprop]
theorem ForIn.forIn.arg_bf.HasAdjDiffM_rule
  (range : ρ) (init : X → Y) (f : X → α → Y → m (ForInStep Y))
  (hinit : HasAdjDiff K init) (hf : ∀ a, HasAdjDiffM K (fun (xy : X×Y) => f xy.1 a xy.2))
  : HasAdjDiffM K (fun x => forIn range (init x) (f x)) := sorry_proof


-- we need some kind of lawful version of `ForIn` to be able to prove this
@[ftrans]
theorem ForIn.forIn.arg_bf.revDerivM_rule
  (range : ρ) (init : X → Y) (f : X → α → Y → m (ForInStep Y))
  (hinit : HasAdjDiff K init) (hf : ∀ a, HasAdjDiffM K (fun (xy : X×Y) => f xy.1 a xy.2))
  : revDerivM K (fun x => forIn range (init x) (f x)) 
    =
    (fun x => do
      let ydinit := revCDeriv K init x
      let ydf ← forIn range (ydinit.1, fun (dy:Y) => pure (f:=m') ((0:X),dy))
        (fun a ydf => do
          let ydf' ← revDerivM K (fun (xy : X×Y) => f xy.1 a xy.2) (x,ydf.1)
          let df : Y → m' (X×Y) := 
            fun dy : Y => do
              let dxy  ← ydf'.2 (.yield dy)
              let dxy' ← ydf.2 dxy.2
              pure (dxy.1 + dxy'.1, dxy'.2)
          match ydf'.1 with
          | .yield y => pure (ForInStep.yield (y, df))
          | .done  y => pure (ForInStep.done (y, df)))
      pure (ydf.1, 
            fun dy => do
              let dxy ← ydf.2 dy
              pure (dxy.1 + ydinit.2 dxy.2))) :=
by
  sorry_proof

theorem ForIn.forIn.arg_bf.revDerivM_rule_alternative [ForIn Id ρ α]
  (init : X → Y) (f : X → Nat → Y → Y)
  (hinit : HasAdjDiff K init) (hf : ∀ a, HasAdjDiff K (fun (xy : X×Y) => f xy.1 a xy.2))
  : revDerivM K (fun x => forIn (m:=Id) (Std.Range.mk start stop step) (init x) (fun i y => .yield (f x i y))) 
    =
    (fun x => Id.run do
      let (y₀,dinit') := revCDeriv K init x
      let (y,ys) ← forIn (Std.Range.mk start stop step) (y₀,#[]) (fun i (y,ys) => 
        let y' := f x i y
        .yield (y', ys.push y'))
      pure (y, 
            fun dy => do
              let (dx,dy) ← forIn (Std.Range.mk start stop step) ((0:X),dy) (fun i (dx,dy) => do 
                let j := stop - ((i-start) + 1)
                let yᵢ : Y := ys[j]!
                let (dx',dy) := (revCDeriv K (fun (xy : X×Y) => f xy.1 i xy.2) (x,yᵢ)).2 dy
                .yield (dx + dx', dy))
              pure (dx + dinit' dy))) :=
by
  sorry_proof

  

-- Proof that the above theorem is true for the range [0:3] and function that does not break the for loop
example
  (init : X → Y) (f : X → Nat → Y → m Y)
  (hinit : HasAdjDiff K init) (hf : ∀ a, HasAdjDiffM K (fun (xy : X×Y) => f xy.1 a xy.2))
  : revDerivM K (fun x => forIn [0:3] (init x) (fun i y => do pure (ForInStep.yield (← f x i y)))) 
    = 
    (fun x => do
      let ydinit := revCDeriv K init x
      let ydf ← forIn [0:3] (ydinit.1, fun (dy:Y) => pure (f:=m') ((0:X),dy))
        (fun a ydf => do
          let ydf' ← revDerivM K (fun (xy : X×Y) => f xy.1 a xy.2) (x,ydf.1)
          let df : Y → m' (X×Y) := 
            fun dy : Y => do
              let dxy  ← ydf'.2 dy
              let dxy' ← ydf.2 dxy.2
              pure (dxy.1 + dxy'.1, dxy'.2)
          pure (ForInStep.yield (ydf'.1, df)))
      pure (ydf.1, 
            fun dy => do
              let dxy ← ydf.2 dy
              pure (dxy.1 + ydinit.2 dxy.2))) :=
by
  simp [revCDeriv,forIn,Std.Range.forIn,Std.Range.forIn.loop,Std.Range.forIn.loop.match_1, revCDeriv]
  ftrans
  simp[add_assoc, revCDeriv]


@[fprop]
theorem ForInStep.yield.arg_a0.HasAdjDiff_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : HasAdjDiff K fun x => ForInStep.yield (a0 x) := by sorry_proof

@[ftrans]
theorem ForInStep.yield.arg_a0.revCDeriv_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : revCDeriv K (fun x => ForInStep.yield (a0 x))
    =
    fun x => 
      let ydf := revCDeriv K a0 x
      (.yield ydf.1, fun y => ydf.2 y.val)
  := by sorry_proof

@[fprop]
theorem ForInStep.done.arg_a0.HasAdjDiff_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : HasAdjDiff K fun x => ForInStep.done (a0 x) := by sorry_proof

@[ftrans]
theorem ForInStep.done.arg_a0.revCDeriv_rule
  (a0 : X → Y) (ha0 : HasAdjDiff K a0)
  : revCDeriv K (fun x => ForInStep.done (a0 x))
    =
    fun x => 
      let ydf := revCDeriv K a0 x
      (.done ydf.1, fun y => ydf.2 y.val)
  := by sorry_proof

end OnSemiInnerProductSpace
