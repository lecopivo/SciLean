import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.Monad.DifferentiableMonad

namespace SciLean

set_option linter.unusedVariables false

/-- `FwdFDerivMonad K m m'` states that the monad `m'` allows us to compute reverse pass of the
 reverse derivative of functions in the  monad `m`. The rought idea is that if the monad `m` reads
some state `S` then the monad `m'` should write into `S`. State monad reads and writes, so for
`m = StateM S` we have `m' = StateM S`.

This class provides two main functions, such that monadic function `(f : X → m Y)`:
  - `revFDerivM K f` is generalization of reverse mode derivative of `f`
  - `DifferentiableM K f` is generalization of differentiability of `f`

For `StateM S` the `revFDerivM` and `DifferentiableM` is:
```
   revFDerivM K f
   =
   fun x s =>
     let ((y,s),df) := revFDeriv K (fun (x,s) => f x s) (x,s)
     ((y,s), fun dy ds => df (dy,ds))

   DifferentiableM K f
   =
   Differentiable K (fun (x,s) => f x s)
```
In short, `revFDerviM` also differentiates w.r.t. to the state variable and `DifferentiableM` checks
that a function is differentiable also w.r.t. to the state variable too.

-/
class RevFDerivMonad (K : Type) [RCLike K] (m : Type → Type) (m' : outParam $ Type → Type) [Monad m] [Monad m'] [DifferentiableMonad K m]  where

  revFDerivM
    {X : Type} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
    {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
    (f : X → m Y) (x : X) : m (Y × (Y → m' X))

  revFDerivM_pure
    {X : Type} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
    {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
    (f : X → Y) (hf : Differentiable K f) :
    revFDerivM (fun x => pure (f:=m) (f x)) = fun x => let ydf := revFDeriv K f x; pure (ydf.1, fun dy => pure (ydf.2 dy))

  revFDerivM_bind
    {X : Type} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
    {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
    {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]
    (f : Y → m Z) (g : X → m Y) (hf : DifferentiableM K f) (hg : DifferentiableM K g)
     : revFDerivM (fun x => g x >>= f)
       =
       fun x => do
         let ydg ← revFDerivM g x
         let zdf ← revFDerivM f ydg.1
         pure (zdf.1, fun dz => zdf.2 dz >>= ydg.2)

  revFDerivM_pair
    {X : Type} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
    {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
    (f : X → m Y) (hf : DifferentiableM K f)
    : revFDerivM (fun x => do let y ← f x; pure (x,y))
      =
      (fun x => do
        let ydf ← revFDerivM f x
        pure ((x,ydf.1), fun dxy : X×Y => do let dx ← ydf.2 dxy.2; pure (dxy.1 + dx)))


export RevFDerivMonad (revFDerivM)

attribute [fun_trans] revFDerivM

set_option deprecated.oldSectionVars true

variable
  (K : Type _) [RCLike K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m']
  [DifferentiableMonad K m] [RevFDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]

open RevFDerivMonad DifferentiableMonad

def revFDerivValM (x : m X) : m (X × (X → m' Unit)) := do
  revFDerivM K (fun _ : Unit => x) ()



--------------------------------------------------------------------------------
-- revFDerivM -------------------------------------------------------------------
--------------------------------------------------------------------------------
namespace revFDerivM

-- id_rule does not make sense


@[fun_trans]
theorem const_rule (y : m Y) (hy : DifferentiableValM K y)
  : revFDerivM K (fun _ : X => y)
    =
    (fun _ => do
      let ydy ← revFDerivValM K y
      pure (ydy.1,
            fun dy' => do
              let _ ← ydy.2 dy'
              pure 0)) :=
by
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  rw[revFDerivM_bind]
  rw[revFDerivM_pure]
  fun_trans
  simp [revFDerivValM]
  fun_prop
  apply hy
  apply DifferentiableM_pure; fun_prop

@[fun_trans]
theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : DifferentiableM K f) (hg : Differentiable K g)
  : revFDerivM K (fun x => f (g x))
    =
    (fun x => do
      let ydg := revFDeriv K g x
      let zdf ← revFDerivM K f ydg.1
      pure (zdf.1,
            fun dz => do
              let dy ← zdf.2 dz
              pure (ydg.2 dy))) :=
by
  conv =>
    lhs
    rw[show ((fun x => f (g x))
             =
             fun x => pure (g x) >>= f) by simp]
    rw[revFDerivM_bind f (fun x => pure (g x))
         hf (DifferentiableM_pure _ hg)]
    rw[revFDerivM_pure g hg]
  simp

@[fun_trans]
theorem let_rule
  (f : X → Y → m Z) (g : X → Y)
  (hf : DifferentiableM K (fun xy : X×Y => f xy.1 xy.2)) (hg : Differentiable K g)
  : revFDerivM K (fun x => let y := g x; f x y)
    =
    (fun x => do
      let ydg := revFDeriv K g x
      let zdf ← revFDerivM K (fun xy : X×Y => f xy.1 xy.2) (x,ydg.1)
      pure (zdf.1,
            fun dz => do
              let dxy ← zdf.2 dz
              let dx := ydg.2 dxy.2
              pure (dxy.1 + dx))) :=
by
  let f' := (fun xy : X×Y => f xy.1 xy.2)
  let g' := (fun x => (x,g x))
  have hg' : Differentiable K g' := by rw[show g' = (fun x => (x,g x)) by rfl]; fun_prop
  conv =>
    lhs
    rw[show ((fun x => f x (g x))
             =
             fun x => pure (g' x) >>= f') by simp[f',g']]
    rw[revFDerivM_bind f' (fun x => pure (g' x)) hf (DifferentiableM_pure g' hg')]
    simp[revFDerivM_pure (K:=K) g' hg']
    -- fun_trans; simp
  sorry_proof

end revFDerivM


end SciLean


--------------------------------------------------------------------------------

section CoreFunctionProperties

open SciLean DifferentiableMonad

set_option deprecated.oldSectionVars true

variable
  (K : Type _) [RCLike K]
  {m m'} [Monad m] [Monad m'] [DifferentiableMonad K m] [RevFDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]


--------------------------------------------------------------------------------
-- Pure.pure -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Pure.pure.arg_a0.revFDerivM_rule
  (a0 : X → Y)
  (ha0 : Differentiable K a0)
  : revFDerivM K (fun x => pure (f:=m) (a0 x))
    =
    (fun x => do
      let ydf := revFDeriv K a0 x
      pure (ydf.1, fun dy => pure (ydf.2 dy))):=
by
  apply RevFDerivMonad.revFDerivM_pure a0 ha0

@[simp, simp_core]
theorem Pure.pure.arg.revFDerivValM_rule (x : X)
  : revFDerivValM K (pure (f:=m) x)
    =
    pure (x,fun _dy => pure 0) :=
by
  unfold revFDerivValM; rw[RevFDerivMonad.revFDerivM_pure]; fun_trans; fun_prop


--------------------------------------------------------------------------------
-- Bind.bind -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Bind.bind.arg_a0a1.revFDerivM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : DifferentiableM K a0) (ha1 : DifferentiableM K (fun (xy : X×Y) => a1 xy.1 xy.2))
  : (revFDerivM K (fun x => Bind.bind (a0 x) (a1 x)))
    =
    (fun x => do
      let ydg ← revFDerivM K a0 x
      let zdf ← revFDerivM K (fun (xy : X×Y) => a1 xy.1 xy.2) (x,ydg.1)
      pure (zdf.1,
            fun dz => do
              let dxy ← zdf.2 dz
              let dx ← ydg.2 dxy.2
              pure (dxy.1 + dx))) :=
by
  let g := fun x => do
    let y ← a0 x
    pure (x,y)
  let f := fun xy : X×Y => a1 xy.1 xy.2

  rw[show (fun x => Bind.bind (a0 x) (a1 x))
          =
          fun x => g x >>= f by simp[f,g]]

  have hg : DifferentiableM K (fun x => do let y ← a0 x; pure (x,y)) :=
    by apply DifferentiableM_pair a0 ha0
  have hf : DifferentiableM K f := by simp[f]; fun_prop

  rw [RevFDerivMonad.revFDerivM_bind _ _ hf hg]
  rw [RevFDerivMonad.revFDerivM_pair a0 ha0]
  simp[f]


-- Functor.map -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Functor.map.arg_a0a1.revFDerivM_rule
  (a0 : X → Y → Z) (a1 : X → m Y)
  (ha0 : Differentiable K (fun (x,y) => a0 x y)) (ha1 : DifferentiableM K a1) :
  revFDerivM K (fun x => (a0 x) <$> (a1 x))
  =
  fun x => do
    let ydy ← revFDerivM K a1 x
    let y := ydy.1; let dy' := ydy.2
    let zdz := revFDeriv K (fun (x,y) => a0 x y) (x,y)
    let z := zdz.1; let dz' := zdz.2
    return (z, fun dz => do
          let dxdy := dz' dz
          let dx₁ := dxdy.1
          let dy := dxdy.2
          let dx₂ ← dy' dy
          return dx₁ + dx₂) :=
by
  simp only [← bind_pure_comp]; fun_trans


--------------------------------------------------------------------------------
-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_trans]
theorem ite.arg_te.revFDerivM_rule
  (c : Prop) [dec : Decidable c] (t e : X → m Y)
  : revFDerivM K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revFDerivM K t y) (revFDerivM K e y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]


@[fun_trans]
theorem dite.arg_te.revFDerivM_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → m Y) (e : ¬c → X → m Y)
  : revFDerivM K (fun x => dite c (fun h => t h x) (fun h => e h x))
    =
    fun y =>
      dite c (fun h => revFDerivM K (t h) y) (fun h => revFDerivM K (e h) y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]
