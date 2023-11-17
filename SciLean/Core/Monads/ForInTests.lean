import SciLean.Core.Monads.ForIn
import SciLean.Tactic.LetNormalize
import SciLean.Core.FloatAsReal
import SciLean.Core.Notation

open SciLean


variable 
  {K : Type} [IsROrC K]
  {m m'} [Monad m] [Monad m'] [FwdDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {ρ : Type} {α : Type _} [ForIn m ρ α] [ForIn m' ρ α] {β : Type _}
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]

variable [PlainDataType K]

#check
  ((gradient K (fun x : K => Id.run do
    let mut y := 1.0
    for i in fullRange (Idx 3) do
      if i.1 = 1 then
        break
      y := y * x 
    y))
    rewrite_by
      unfold gradient
      ftrans
      ftrans
      ftrans
      unfold gradient
      ftrans
      ftrans)

set_option trace.Meta.Tactic.fprop.step true in
example (z) :
  SciLean.HasAdjDiff K fun (w : K) =>
        forIn (m:=Id) (fullRange (Idx 3)) (MProd.mk 1.0 z) fun (i : SciLean.Idx 3) (r : MProd K K) =>
          let y := r.fst * w + r.snd;
          let z := r.snd + y;
          ForInStep.yield (MProd.mk y z) := by fprop
variable [PlainDataType (MProd K K)]
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.ftrans.step true in
set_option pp.funBinderTypes true in
#check
  ((gradient K (fun x : K => Id.run do
    let mut y := 1.0
    let mut z := y + 10.0
    for i in fullRange (Idx 3) do
      y := y * x + z
      z := z + y
    y))
    rewrite_by
      unfold gradient
      ftrans
      ftrans
      ftrans
      ftrans
      unfold gradient
      ftrans)

#check MProd

-- 
set_option pp.notation false in
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


example 
  : IsDifferentiable K (fun x : K => Id.run do
  let mut y := x
  for i in [0:5] do
    y := i * y * y + x - x + i
    for j in [0:3] do
      y := y * j + x
  pure y) := 
by
  fprop

example 
  : IsDifferentiableM K (fun x : K => show m K from do
  let mut y := x
  for i in [0:5] do
    y := i * y * y + x - x + i
    for j in [0:3] do
      y := y * j + x
  pure y) := 
by
  fprop


example : fwdDerivM K (fun x : K => show m K from do
  let mut y := x
  for i in [0:5] do
    let z := y * x
    y := z + x + y + i
  pure y) 
  = 
  (fun x dx => do
    let mut ydy := (x,dx)
    for i in [0:5] do
      let z  := ydy.1 * x
      let dz := dx * ydy.1 + ydy.2 * x
      ydy := (z + x + ydy.1 + i, dz + dx + ydy.2)
    pure ydy)
  := 
by
  (conv => lhs; ftrans; ftrans; simp (config := {zeta := false}))
  simp

-- @[ftrans_simp]
-- theorem revDerivM_eq_revCDeriv_on_Id' 
--   [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] (x : X) (f : X → Y)
--   : revDerivM K fun f = revCDeriv K f := by set_option pp.all true in rfl


#eval
  ((gradient Float (fun x : Float ^ Idx 3 => Id.run do
    let mut y := 1.0
    for i in fullRange (Idx 3) do
      y := y * x[i]
    y))
    rewrite_by
      unfold gradient
      ftrans
      ftrans
      ftrans
      unfold gradient
      ftrans)
  ⊞[5.0,6,7] 1


set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.fprop.discharge true in
-- set_option trace.Meta.Tactic.fprop.step true in
set_option trace.Meta.Tactic.ftrans.step true in
set_option pp.notation false in
#eval
  ((gradient Float (fun x : Float ^ Idx 10 => Id.run do
    let mut s := x[(⟨0,sorry⟩ : Idx 10)]
    for i in [0:9] do
      let i : Idx 10 := ⟨i.toUSize+1,sorry⟩
      s := s + x[i]
    s))
    rewrite_by
      unfold gradient
      ftrans
      ftrans
      ftrans
      unfold gradient
      ftrans)
  ⊞[5.0,6,7,8,9,10,11,12,13,14] 1


-- example : fwdDerivM K (fun x : K => show m K from do
--   let mut y := x
--   for i in [0:5] do
--     let z := y * x
--     y := z + x + y
--   pure y) 
--   = 
--   (fun x dx => do
--     let mut y := x
--     let mut dy := dx
--     for i in [0:5] do
--       let z  := y * x
--       let dz := dx * y + dy * x
--       y := z + x + y
--       dy := dz + dx + dy
--     pure (y,dy))
--   := 
-- by
--   ftrans only; ftrans only
--   simp[bind]; funext x dx;  congr
