import SciLean.Analysis.Calculus.FwdFDeriv

namespace SciLean


/-- `DifferentiableMonad K m` states that the monad `m` has the notion of differentiability.
The rought idea is that if the monad `m` stores some state `S` then a function `(f : X → m Y)`
should be also differentiable w.r.t. to the state `S`.

This class provide proposition `DifferentiableM K f` which is monadic generalization of
differentiability.

For `StateM S` the `DifferentiableM` is:
```
   DifferentiableM K f
   =
   Differentiable K (fun (x,s) => f x s)
```
-/
class DifferentiableMonad (K : Type) [RCLike K] (m : Type → Type) [Monad m] where
  /-- Differentiability of monatic functions.

  For state monad, `m = StateM S`, this predicate says that the function is also differentiable
  w.r.t. to the state variable.
  ```
    DifferentiableM K f
    =
    Differentiable K (fun (x,s) => f x s)
  ```
  -/
  DifferentiableM {X Y : Type} [NormedAddCommGroup X] [NormedSpace K X] [NormedAddCommGroup Y] [NormedSpace K Y]
    (f : X → m Y) : Prop

  /-- Monadic differentiable pure function is differentiable. -/
  DifferentiableM_pure {X Y : Type} [NormedAddCommGroup X] [NormedSpace K X] [NormedAddCommGroup Y] [NormedSpace K Y]
      (f : X → Y) (hf : Differentiable K f) :
      DifferentiableM (fun x : X => pure (f x))

  /-- Composition of monadic differentiable functions is monadic differentiable. -/
  DifferentiableM_bind     {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace K X] [NormedAddCommGroup Y] [NormedSpace K Y]
      [NormedAddCommGroup Z] [NormedSpace K Z]
      (f : Y → m Z) (g : X → m Y)
      (hf : DifferentiableM f) (hg : DifferentiableM g) :
      DifferentiableM (fun x => g x >>= f)

  /-- Theorem allowing us to differentiate let bindings.

  Note: The role of this is still not completely clear to us. Is this really independent of the
        previous two requirements? -/
  DifferentiableM_pair {X Y : Type} [NormedAddCommGroup X] [NormedSpace K X] [NormedAddCommGroup Y] [NormedSpace K Y]
      (f : X → m Y) (hf : DifferentiableM f) :
      DifferentiableM (fun x => do let y ← f x; pure (x,y))


export DifferentiableMonad (DifferentiableM)

attribute [fun_prop] DifferentiableM

set_option deprecated.oldSectionVars true

variable
  (K : Type) [RCLike K]
  {m : Type → Type} [Monad m] [DifferentiableMonad K m]
  [LawfulMonad m]
  {X : Type} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace K Z]

open DifferentiableMonad

/-- Monadic differentiable value. For example, in case of state monad the value `x : StateM S X`
is a function in `S` and it makes sense to ask about differentiability. -/
def DifferentiableValM (x : m X) : Prop :=
  DifferentiableM K (fun _ : Unit => x)


--------------------------------------------------------------------------------
-- DifferentiableM -----------------------------------------------------------
--------------------------------------------------------------------------------
namespace DifferentiableM

@[fun_prop]
theorem pure_rule
  : DifferentiableM (m:=m) K (fun x : X => pure x) :=
by
  apply DifferentiableM_pure
  fun_prop

@[fun_prop]
theorem const_rule (y : m Y) (hy : DifferentiableValM K y)
  : DifferentiableM K (fun _ : X => y) :=
by
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  apply DifferentiableM_bind
  apply hy
  apply DifferentiableM_pure
  fun_prop

@[fun_prop]
theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : DifferentiableM K f) (hg : Differentiable K g)
  : DifferentiableM K (fun x => f (g x)) :=
by
  rw[show ((fun x => f (g x))
           =
           fun x => pure (g x) >>= f) by simp]
  apply DifferentiableM_bind _ _ hf
  apply DifferentiableM_pure g hg

end DifferentiableM

end SciLean



--------------------------------------------------------------------------------

section CoreFunctionProperties

open SciLean

set_option deprecated.oldSectionVars true

variable
  (K : Type) [RCLike K]
  {m } [Monad m] [DifferentiableMonad K m]
  [LawfulMonad m]
  {X : Type} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace K Z]
  {E : ι → Type}


--------------------------------------------------------------------------------
-- Pure.pure -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Pure.pure.arg_a0.DifferentiableM_rule
  (a0 : X → Y)
  (ha0 : Differentiable K a0)
  : DifferentiableM K (fun x => Pure.pure (f:=m) (a0 x)) :=
by
  apply DifferentiableMonad.DifferentiableM_pure a0 ha0

@[simp, simp_core]
theorem Pure.pure.arg.DifferentiableValM_rule (x : X)
  : DifferentiableValM K (pure (f:=m) x) :=
by
  unfold DifferentiableValM
  apply DifferentiableMonad.DifferentiableM_pure
  fun_prop


--------------------------------------------------------------------------------
-- Bind.bind -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Bind.bind.arg_a0a1.DifferentiableM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : DifferentiableM K a0) (ha1 : DifferentiableM K (fun (xy : X×Y) => a1 xy.1 xy.2))
  : DifferentiableM K (fun x => Bind.bind (a0 x) (a1 x)) :=
by
  let g := fun x => do
    let y ← a0 x
    pure (x,y)
  let f := fun xy : X×Y => a1 xy.1 xy.2

  rw[show (fun x => Bind.bind (a0 x) (a1 x))
          =
          fun x => g x >>= f by simp[f,g]]

  have hg : DifferentiableM K (fun x => do let y ← a0 x; pure (x,y)) :=
    by apply DifferentiableMonad.DifferentiableM_pair a0 ha0
  have hf : DifferentiableM K f := by simp[f]; fun_prop

  apply DifferentiableMonad.DifferentiableM_bind _ _ hf hg


-- Functor.map -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Functor.map.arg_a0a1.DifferentiableM_rule
  (a0 : X → Y → Z) (a1 : X → m Y)
  (ha0 : Differentiable K (fun (x,y) => a0 x y)) (ha1 : DifferentiableM K a1)
  : DifferentiableM K (fun x => (a0 x) <$> (a1 x)) :=
by
  simp only [← bind_pure_comp]; fun_prop


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem ite.arg_te.DifferentiableM_rule
  (c : Prop) [dec : Decidable c] (t e : X → m Y)
  (ht : DifferentiableM K t) (he : DifferentiableM K e)
  : DifferentiableM K (fun x => ite c (t x) (e x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]


@[fun_prop]
theorem dite.arg_te.DifferentiableM_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → m Y) (e : ¬c → X → m Y)
  (ht : ∀ h, DifferentiableM K (t h)) (he : ∀ h, DifferentiableM K (e h))
  : DifferentiableM K (fun x => dite c (fun h => t h x) (fun h => e h x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]
