import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.Monad.DifferentiableMonad

namespace SciLean


/-- `FwdFDerivMonad K m m'` states that the monad `m'` allows us to compute forward mode derivative
of functions in the monad `m`. The rought idea is that if the monad `m` stores some state `S` then
the monad `m'` should store `S⨯S` corresponding to the state and its derivative. Concretelly, for
`m = StateM S` we have `m' = StateM S×S`.

This class provides two main functions, such that monadic function `(f : X → m Y)`:
  - `fwdFDerivM K f` is generalization of forward mode derivative of `f`
  - `DifferentiableM K f` is generalization of differentiability of `f`

For `StateM S` the `fwdFDerivM` and `DifferentiableM` is:
```
   fwdFDerivM K f
   =
   fun x dx (s,ds) =>
     let ((y,s),(dy,ds)) := fwdFDeriv K (fun (x,s) => f x s) (x,s) (dx,ds)
     ((y,dy),(s,ds))

   DifferentiableM K f
   =
   Differentiable K (fun (x,s) => f x s)
```
In short, `fwdFDerviM` also differentiates w.r.t. to the state variable and `DifferentiableM` checks
that a function is differentiable also w.r.t. to the state variable too.

The nice property of this general definition is that it generalized to monad tranformer `StateT`.
Therefore we can nest state monads and still differentiate them.
-/
class FwdFDerivMonad (K : Type) [RCLike K] (m : Type → Type) (m' : outParam $ Type → Type) [Monad m] [Monad m'] [DifferentiableMonad K m] where
  /-- Forward mode derivative for monadic functions.

  For state monad, `m = StateM S`, this derivative also differentiates w.r.t to the state variable
  ```
    fwdFDerivM K f
    =
    fun x dx (s,ds) =>
      let ((y,s),(dy,ds)) := fwdFDeriv K (fun (x,s) => f x s) (x,s) (dx,ds)
      ((y,dy),(s,ds))
  ```
  -/
  fwdFDerivM {X Y : Type} [NormedAddCommGroup X] [NormedSpace K X] [NormedAddCommGroup Y] [NormedSpace K Y]
    (f : X → m Y) (x dx : X) : m' (Y × Y)

  /-- Monadic derivative of pure function is normal derivative. -/
  fwdFDerivM_pure {X Y : Type} [NormedAddCommGroup X] [NormedSpace K X] [NormedAddCommGroup Y] [NormedSpace K Y]
      (f : X → Y) (hf : Differentiable K f) :
      fwdFDerivM (fun x => pure (f:=m) (f x)) = fun x dx => pure (f:=m') (fwdFDeriv K f x dx)

  /-- Monadic chain rule. -/
  fwdFDerivM_bind
      {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace K X] [NormedAddCommGroup Y] [NormedSpace K Y]
      [NormedAddCommGroup Z] [NormedSpace K Z]
      (f : Y → m Z) (g : X → m Y) (hf : DifferentiableM K f) (hg : DifferentiableM K g) :
      fwdFDerivM (fun x => g x >>= f)
      =
      fun x dx => do
        let ydy ← fwdFDerivM g x dx
        fwdFDerivM f ydy.1 ydy.2

  /-- Theorem allowing us to differentiate let bindings.

  Note: The role of this is still not completely clear to us. Is this really independent of the
        previous two requirements? -/
  fwdFDerivM_pair {X Y : Type} [NormedAddCommGroup X] [NormedSpace K X] [NormedAddCommGroup Y] [NormedSpace K Y]
      (f : X → m Y) (hf : DifferentiableM K f) :
      fwdFDerivM (fun x => do let y ← f x; pure (x,y))
      =
      (fun x dx => do
        let ydy ← fwdFDerivM f x dx
        pure ((x,ydy.1),(dx,ydy.2)))


export FwdFDerivMonad (fwdFDerivM)

attribute [fun_trans] fwdFDerivM

set_option deprecated.oldSectionVars true

variable
  (K : Type) [RCLike K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m']
  [DifferentiableMonad K m] [FwdFDerivMonad K m m'] [LawfulMonad m] [LawfulMonad m']
  {X : Type} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace K Z]

open FwdFDerivMonad

/-- Monadic derivative of a value. For example, in case of state monad the value `x : StateM S X`
is a function in `S` and it makes sense to take derivative of it. -/
def fwdFDerivValM (x : m X) : m' (X × X) := do
  fwdFDerivM K (fun _ : Unit => x) () ()

--------------------------------------------------------------------------------
-- fwdFDerivM -------------------------------------------------------------------
--------------------------------------------------------------------------------
namespace fwdFDerivM

open DifferentiableMonad

@[fun_trans]
theorem pure_rule
  : fwdFDerivM (m:=m) K (fun x : X => pure x) = fun x dx => pure (x, dx) :=
by
  rw [fwdFDerivM_pure _ (by fun_prop)]
  fun_trans

@[fun_trans]
theorem const_rule (y : m Y) (hy : DifferentiableValM K y)
  : fwdFDerivM K (fun _ : X => y) = fun _ _ => fwdFDerivValM K y :=
by
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  rw[fwdFDerivM_bind]
  rw[fwdFDerivM_pure]
  fun_trans
  simp [fwdFDerivValM]
  fun_prop
  apply hy
  apply DifferentiableM_pure; fun_prop

@[fun_trans]
theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : DifferentiableM K f) (hg : Differentiable K g)
  : fwdFDerivM K (fun x => f (g x))
    =
    fun x dx =>
      let ydy := fwdFDeriv K g x dx
      fwdFDerivM K f ydy.1 ydy.2 :=
by
  conv =>
    lhs
    rw[show ((fun x => f (g x))
             =
             fun x => pure (g x) >>= f) by simp]
    rw[FwdFDerivMonad.fwdFDerivM_bind f (fun x => pure (g x))
         hf (DifferentiableM_pure _ hg)]
    simp[FwdFDerivMonad.fwdFDerivM_pure g hg]

@[fun_trans]
theorem let_rule
  (f : X → Y → m Z) (g : X → Y)
  (hf : DifferentiableM K (fun xy : X×Y => f xy.1 xy.2)) (hg : Differentiable K g)
  : fwdFDerivM K (fun x => let y := g x; f x y)
    =
    fun x dx =>
      let ydy := fwdFDeriv K g x dx
      fwdFDerivM K (fun xy : X×Y => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2) :=
by
  let f' := (fun xy : X×Y => f xy.1 xy.2)
  let g' := (fun x => (x,g x))
  have hg' : Differentiable K g' := by rw[show g' = (fun x => (x,g x)) by rfl]; fun_prop
  conv =>
    lhs
    rw[show ((fun x => f x (g x))
             =
             fun x => pure (g' x) >>= f') by simp[f',g']]
    rw[fwdFDerivM_bind f' (fun x => pure (g' x)) hf (DifferentiableM_pure g' hg')]
    simp[fwdFDerivM_pure (K:=K) g' hg']
    fun_trans
    simp


end fwdFDerivM

end SciLean



--------------------------------------------------------------------------------

section CoreFunctionProperties

open SciLean DifferentiableMonad

set_option deprecated.oldSectionVars true

variable
  (K : Type) [RCLike K]
  {m m'} [Monad m] [Monad m']
  [DifferentiableMonad K m] [FwdFDerivMonad K m m'] [LawfulMonad m] [LawfulMonad m']
  {X : Type} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace K Z]


--------------------------------------------------------------------------------
-- Pure.pure -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Pure.pure.arg_a0.fwdFDerivM_rule
  (a0 : X → Y)
  (ha0 : Differentiable K a0)
  : fwdFDerivM K (fun x => pure (f:=m) (a0 x))
    =
    fun x dx => pure (fwdFDeriv K a0 x dx) :=
by
  apply FwdFDerivMonad.fwdFDerivM_pure a0 ha0

@[simp, simp_core]
theorem Pure.pure.arg.fwdFDerivValM_rule (x : X)
  : fwdFDerivValM K (pure (f:=m) x)
    =
    pure (x,0) :=
by
  unfold fwdFDerivValM; rw[FwdFDerivMonad.fwdFDerivM_pure]; fun_trans; fun_prop


--------------------------------------------------------------------------------
-- Bind.bind -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Bind.bind.arg_a0a1.fwdFDerivM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : DifferentiableM K a0) (ha1 : DifferentiableM K (fun (xy : X×Y) => a1 xy.1 xy.2))
  : (fwdFDerivM K (fun x => Bind.bind (a0 x) (a1 x)))
    =
    (fun x dx => do
      let ydy ← fwdFDerivM K a0 x dx
      fwdFDerivM K (fun (xy : X×Y) => a1 xy.1 xy.2) (x, ydy.1) (dx, ydy.2)) :=
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
  have hf : DifferentiableM K f := by simp [f]; fun_prop

  rw [FwdFDerivMonad.fwdFDerivM_bind _ _ hf hg]
  rw[FwdFDerivMonad.fwdFDerivM_pair a0 ha0]
  simp[f]


-- Functor.map -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Functor.map.arg_a0a1.fwdFDerivM_rule
    (a0 : X → Y → Z) (a1 : X → m Y)
    (ha0 : Differentiable K (fun (x,y) => a0 x y)) (ha1 : DifferentiableM K a1) :
    fwdFDerivM K (fun x => (a0 x) <$> (a1 x))
    =
    fun x dx => do
      let ydy ← fwdFDerivM K a1 x dx
      let y := ydy.1; let dy := ydy.2
      return (fwdFDeriv K (fun (x,y) => a0 x y) (x,y) (dx,dy)) := by
  simp only [← bind_pure_comp];
  fun_trans only


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem ite.arg_te.fwdFDerivM_rule
  (c : Prop) [dec : Decidable c] (t e : X → m Y)
  : fwdFDerivM K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (fwdFDerivM K t y) (fwdFDerivM K e y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]

@[fun_trans]
theorem dite.arg_te.fwdFDerivM_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → m Y) (e : ¬c → X → m Y)
  : fwdFDerivM K (fun x => dite c (fun h => t h x) (fun h => e h x))
    =
    fun y =>
      dite c (fun h => fwdFDerivM K (t h) y) (fun h => fwdFDerivM K (e h) y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]
