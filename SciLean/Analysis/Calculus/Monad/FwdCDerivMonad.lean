import SciLean.Analysis.Calculus.FwdCDeriv

namespace SciLean

set_option linter.unusedVariables false in
class FwdCDerivMonad (K : Type) [RCLike K] (m : Type → Type) (m' : outParam $ Type → Type) [Monad m] [Monad m'] where
  fwdCDerivM {X : Type} {Y : Type} [Vec K X] [Vec K Y] : ∀ (f : X → m Y) (x dx : X), m' (Y × Y)

  CDifferentiableM {X : Type} {Y : Type} [Vec K X] [Vec K Y]
    : ∀ (f : X → m Y), Prop

  fwdCDerivM_pure {X Y : Type} [Vec K X] [Vec K Y] (f : X → Y) (hf : CDifferentiable K f)
    : fwdCDerivM (fun x => pure (f:=m) (f x)) = fun x dx => pure (f:=m') (fwdCDeriv K f x dx)
  fwdCDerivM_bind
    {X Y Z : Type} [Vec K X] [Vec K Y] [Vec K Z]
    (f : Y → m Z) (g : X → m Y) (hf : CDifferentiableM f) (hg : CDifferentiableM g)
     : fwdCDerivM (fun x => g x >>= f)
       =
       fun x dx => do
         let ydy ← fwdCDerivM g x dx
         fwdCDerivM f ydy.1 ydy.2
  fwdCDerivM_pair {X : Type} {Y : Type} [Vec K X] [Vec K Y] -- is this really necessary?
    (f : X → m Y) (hf : CDifferentiableM f)
    : fwdCDerivM (fun x => do let y ← f x; pure (x,y))
      =
      (fun x dx => do
        let ydy ← fwdCDerivM f x dx
        pure ((x,ydy.1),(dx,ydy.2)))


  CDifferentiableM_pure {X : Type} {Y : Type} [Vec K X] [Vec K Y]
    (f : X → Y) (hf : CDifferentiable K f)
    : CDifferentiableM (fun x : X => pure (f x))
  CDifferentiableM_bind {X Y Z: Type} [Vec K X] [Vec K Y] [Vec K Z]
    (f : Y → m Z) (g : X → m Y)
    (hf : CDifferentiableM f) (hg : CDifferentiableM g)
    : CDifferentiableM (fun x => g x >>= f)
  CDifferentiableM_pair {X : Type} {Y : Type} [Vec K X] [Vec K Y] -- is this really necessary?
    (f : X → m Y) (hf : CDifferentiableM f)
    : CDifferentiableM (fun x => do let y ← f x; pure (x,y))

export FwdCDerivMonad (fwdCDerivM CDifferentiableM)

attribute [fun_prop] CDifferentiableM
attribute [fun_trans] fwdCDerivM


variable
  (K : Type _) [RCLike K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m'] [FwdCDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]
  {E : ι → Type} [∀ i, Vec K (E i)]

open FwdCDerivMonad


def fwdCDerivValM (x : m X) : m' (X × X) := do
  fwdCDerivM K (fun _ : Unit => x) () ()

def CDifferentiableValM (x : m X) : Prop :=
  CDifferentiableM K (fun _ : Unit => x)


--------------------------------------------------------------------------------
-- CDifferentiableM -----------------------------------------------------------
--------------------------------------------------------------------------------
namespace CDifferentiableM

@[fun_prop]
theorem pure_rule
  : CDifferentiableM (m:=m) K (fun x : X => pure x) :=
by
  apply CDifferentiableM_pure
  fun_prop

@[fun_prop]
theorem const_rule (y : m Y) (hy : CDifferentiableValM K y)
  : CDifferentiableM K (fun _ : X => y) :=
by
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  apply CDifferentiableM_bind
  apply hy
  apply CDifferentiableM_pure
  fun_prop

@[fun_prop]
theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : CDifferentiableM K f) (hg : CDifferentiable K g)
  : CDifferentiableM K (fun x => f (g x)) :=
by
  rw[show ((fun x => f (g x))
           =
           fun x => pure (g x) >>= f) by simp]
  apply CDifferentiableM_bind _ _ hf
  apply CDifferentiableM_pure g hg

end CDifferentiableM


--------------------------------------------------------------------------------
-- fwdCDerivM -------------------------------------------------------------------
--------------------------------------------------------------------------------
namespace fwdCDerivM

@[fun_trans]
theorem pure_rule
  : fwdCDerivM (m:=m) K (fun x : X => pure x) = fun x dx => pure (x, dx) :=
by
  rw [fwdCDerivM_pure _ (by fun_prop)]
  fun_trans

@[fun_trans]
theorem const_rule (y : m Y) (hy : CDifferentiableValM K y)
  : fwdCDerivM K (fun _ : X => y) = fun _ _ => fwdCDerivValM K y :=
by
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  rw[fwdCDerivM_bind]
  rw[fwdCDerivM_pure]
  fun_trans
  simp [fwdCDerivValM]
  fun_prop
  apply hy
  apply CDifferentiableM_pure; fun_prop

@[fun_trans]
theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : CDifferentiableM K f) (hg : CDifferentiable K g)
  : fwdCDerivM K (fun x => f (g x))
    =
    fun x dx =>
      let ydy := fwdCDeriv K g x dx
      fwdCDerivM K f ydy.1 ydy.2 :=
by
  conv =>
    lhs
    rw[show ((fun x => f (g x))
             =
             fun x => pure (g x) >>= f) by simp]
    rw[FwdCDerivMonad.fwdCDerivM_bind f (fun x => pure (g x))
         hf (FwdCDerivMonad.CDifferentiableM_pure _ hg)]
    simp[FwdCDerivMonad.fwdCDerivM_pure g hg]

@[fun_trans]
theorem let_rule
  (f : X → Y → m Z) (g : X → Y)
  (hf : CDifferentiableM K (fun xy : X×Y => f xy.1 xy.2)) (hg : CDifferentiable K g)
  : fwdCDerivM K (fun x => let y := g x; f x y)
    =
    fun x dx =>
      let ydy := fwdCDeriv K g x dx
      fwdCDerivM K (fun xy : X×Y => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2) :=
by
  let f' := (fun xy : X×Y => f xy.1 xy.2)
  let g' := (fun x => (x,g x))
  have hg' : CDifferentiable K g' := by rw[show g' = (fun x => (x,g x)) by rfl]; fun_prop
  conv =>
    lhs
    rw[show ((fun x => f x (g x))
             =
             fun x => pure (g' x) >>= f') by simp]
    rw[fwdCDerivM_bind f' (fun x => pure (g' x)) hf (CDifferentiableM_pure g' hg')]
    simp[fwdCDerivM_pure (K:=K) g' hg']
    -- fun_trans
    -- simp
  sorry_proof

end fwdCDerivM

end SciLean



--------------------------------------------------------------------------------

section CoreFunctionProperties

open SciLean

variable
  (K : Type _) [RCLike K]
  {m m'} [Monad m] [Monad m'] [FwdCDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]
  {E : ι → Type} [∀ i, Vec K (E i)]


--------------------------------------------------------------------------------
-- Pure.pure -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Pure.pure.arg_a0.CDifferentiableM_rule
  (a0 : X → Y)
  (ha0 : CDifferentiable K a0)
  : CDifferentiableM K (fun x => Pure.pure (f:=m) (a0 x)) :=
by
  apply FwdCDerivMonad.CDifferentiableM_pure a0 ha0


@[fun_trans]
theorem Pure.pure.arg_a0.fwdCDerivM_rule
  (a0 : X → Y)
  (ha0 : CDifferentiable K a0)
  : fwdCDerivM K (fun x => pure (f:=m) (a0 x))
    =
    fun x dx => pure (fwdCDeriv K a0 x dx) :=
by
  apply FwdCDerivMonad.fwdCDerivM_pure a0 ha0

@[simp, simp_core]
theorem Pure.pure.arg.CDifferentiableValM_rule (x : X)
  : CDifferentiableValM K (pure (f:=m) x) :=
by
  unfold CDifferentiableValM
  apply FwdCDerivMonad.CDifferentiableM_pure
  fun_prop

@[simp, simp_core]
theorem Pure.pure.arg.fwdCDerivValM_rule (x : X)
  : fwdCDerivValM K (pure (f:=m) x)
    =
    pure (x,0) :=
by
  unfold fwdCDerivValM; rw[FwdCDerivMonad.fwdCDerivM_pure]; fun_trans; fun_prop


--------------------------------------------------------------------------------
-- Bind.bind -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Bind.bind.arg_a0a1.CDifferentiableM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : CDifferentiableM K a0) (ha1 : CDifferentiableM K (fun (xy : X×Y) => a1 xy.1 xy.2))
  : CDifferentiableM K (fun x => Bind.bind (a0 x) (a1 x)) :=
by
  let g := fun x => do
    let y ← a0 x
    pure (x,y)
  let f := fun xy : X×Y => a1 xy.1 xy.2

  rw[show (fun x => Bind.bind (a0 x) (a1 x))
          =
          fun x => g x >>= f by simp[f,g]]

  have hg : CDifferentiableM K (fun x => do let y ← a0 x; pure (x,y)) :=
    by apply FwdCDerivMonad.CDifferentiableM_pair a0 ha0
  have hf : CDifferentiableM K f := by simp[f]; fun_prop

  apply FwdCDerivMonad.CDifferentiableM_bind _ _ hf hg



@[fun_trans]
theorem Bind.bind.arg_a0a1.fwdCDerivM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : CDifferentiableM K a0) (ha1 : CDifferentiableM K (fun (xy : X×Y) => a1 xy.1 xy.2))
  : (fwdCDerivM K (fun x => Bind.bind (a0 x) (a1 x)))
    =
    (fun x dx => do
      let ydy ← fwdCDerivM K a0 x dx
      fwdCDerivM K (fun (xy : X×Y) => a1 xy.1 xy.2) (x, ydy.1) (dx, ydy.2)) :=
by
  let g := fun x => do
    let y ← a0 x
    pure (x,y)
  let f := fun xy : X×Y => a1 xy.1 xy.2

  rw[show (fun x => Bind.bind (a0 x) (a1 x))
          =
          fun x => g x >>= f by simp[f,g]]

  have hg : CDifferentiableM K (fun x => do let y ← a0 x; pure (x,y)) :=
    by apply FwdCDerivMonad.CDifferentiableM_pair a0 ha0
  have hf : CDifferentiableM K f := by simp [f]; fun_prop

  rw [FwdCDerivMonad.fwdCDerivM_bind _ _ hf hg]
  simp [FwdCDerivMonad.fwdCDerivM_pair a0 ha0]


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem ite.arg_te.CDifferentiableM_rule
  (c : Prop) [dec : Decidable c] (t e : X → m Y)
  (ht : CDifferentiableM K t) (he : CDifferentiableM K e)
  : CDifferentiableM K (fun x => ite c (t x) (e x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]


@[fun_trans]
theorem ite.arg_te.fwdCDerivM_rule
  (c : Prop) [dec : Decidable c] (t e : X → m Y)
  : fwdCDerivM K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (fwdCDerivM K t y) (fwdCDerivM K e y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]


@[fun_prop]
theorem dite.arg_te.CDifferentiableM_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → m Y) (e : ¬c → X → m Y)
  (ht : ∀ h, CDifferentiableM K (t h)) (he : ∀ h, CDifferentiableM K (e h))
  : CDifferentiableM K (fun x => dite c (fun h => t h x) (fun h => e h x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]


@[fun_trans]
theorem dite.arg_te.fwdCDerivM_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → m Y) (e : ¬c → X → m Y)
  : fwdCDerivM K (fun x => dite c (fun h => t h x) (fun h => e h x))
    =
    fun y =>
      dite c (fun h => fwdCDerivM K (t h) y) (fun h => fwdCDerivM K (e h) y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]
