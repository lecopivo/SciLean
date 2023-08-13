import SciLean.Core.Monads.ForIn

open SciLean


variable 
  {K : Type _} [IsROrC K]
  {m m'} [Monad m] [Monad m'] [FwdDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {ρ : Type _} {α : Type _} [ForIn m ρ α] [ForIn m' ρ α] {β : Type _}
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]

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
  (conv => lhs; ftrans only; ftrans only)
  simp; funext x dx; congr; funext i (y,dy); congr; simp


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
