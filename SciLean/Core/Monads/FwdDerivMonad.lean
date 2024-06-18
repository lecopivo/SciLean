import SciLean.Core.FunctionTransformations.FwdDeriv

namespace SciLean

set_option linter.unusedVariables false in
class FwdDerivMonad (K : Type) [RCLike K] (m : Type → Type) (m' : outParam $ Type → Type) [Monad m] [Monad m'] where
  fwdDerivM {X : Type} {Y : Type} [Vec K X] [Vec K Y] : ∀ (f : X → m Y) (x dx : X), m' (Y × Y)

  CDifferentiableM {X : Type} {Y : Type} [Vec K X] [Vec K Y]
    : ∀ (f : X → m Y), Prop

  fwdDerivM_pure {X Y : Type} [Vec K X] [Vec K Y] (f : X → Y) (hf : CDifferentiable K f)
    : fwdDerivM (fun x => pure (f:=m) (f x)) = fun x dx => pure (f:=m') (fwdDeriv K f x dx)
  fwdDerivM_bind
    {X Y Z : Type} [Vec K X] [Vec K Y] [Vec K Z]
    (f : Y → m Z) (g : X → m Y) (hf : CDifferentiableM f) (hg : CDifferentiableM g)
     : fwdDerivM (fun x => g x >>= f)
       =
       fun x dx => do
         let ydy ← fwdDerivM g x dx
         fwdDerivM f ydy.1 ydy.2
  fwdDerivM_pair {X : Type} {Y : Type} [Vec K X] [Vec K Y] -- is this really necessary?
    (f : X → m Y) (hf : CDifferentiableM f)
    : fwdDerivM (fun x => do let y ← f x; pure (x,y))
      =
      (fun x dx => do
        let ydy ← fwdDerivM f x dx
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

export FwdDerivMonad (fwdDerivM CDifferentiableM)

attribute [fun_prop] CDifferentiableM
attribute [fun_trans] fwdDerivM


variable
  (K : Type _) [RCLike K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m'] [FwdDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]
  {E : ι → Type} [∀ i, Vec K (E i)]

open FwdDerivMonad


def fwdDerivValM (x : m X) : m' (X × X) := do
  fwdDerivM K (fun _ : Unit => x) () ()

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


-- theorem let_rule
--   (f : X → Y → m Z) (g : X → Y)
--   (hf : CDifferentiableM K (fun xy : X×Y => f xy.1 xy.2)) (hg : CDifferentiable K g)
--   : CDifferentiableM K (fun x => let y := g x; f x y) :=
-- by
--   let f' := (fun xy : X×Y => f xy.1 xy.2)
--   let g' := (fun x => (x, g x))
--   rw[show ((fun x => f x (g x))
--            =
--            fun x => pure (g' x) >>= f') by simp]
--   apply CDifferentiableM_bind _ _ hf
--   apply CDifferentiableM_pure g'
--   try fun_prop -- this should finish the proof
--   apply Prod.mk.arg_fstsnd.CDifferentiable_rule
--   apply hg
--   fun_prop

end CDifferentiableM


--------------------------------------------------------------------------------
-- fwdDerivM -------------------------------------------------------------------
--------------------------------------------------------------------------------
namespace fwdDerivM

@[fun_trans]
theorem pure_rule
  : fwdDerivM (m:=m) K (fun x : X => pure x) = fun x dx => pure (x, dx) :=
by
  rw [fwdDerivM_pure _ (by fun_prop)]
  fun_trans

@[fun_trans]
theorem const_rule (y : m Y) (hy : CDifferentiableValM K y)
  : fwdDerivM K (fun _ : X => y) = fun _ _ => fwdDerivValM K y :=
by
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  rw[fwdDerivM_bind]
  rw[fwdDerivM_pure]
  fun_trans
  simp [fwdDerivValM]
  fun_prop
  apply hy
  apply CDifferentiableM_pure; fun_prop

@[fun_trans]
theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : CDifferentiableM K f) (hg : CDifferentiable K g)
  : fwdDerivM K (fun x => f (g x))
    =
    fun x dx =>
      let ydy := fwdDeriv K g x dx
      fwdDerivM K f ydy.1 ydy.2 :=
by
  conv =>
    lhs
    rw[show ((fun x => f (g x))
             =
             fun x => pure (g x) >>= f) by simp]
    rw[FwdDerivMonad.fwdDerivM_bind f (fun x => pure (g x))
         hf (FwdDerivMonad.CDifferentiableM_pure _ hg)]
    simp[FwdDerivMonad.fwdDerivM_pure g hg]

@[fun_trans]
theorem let_rule
  (f : X → Y → m Z) (g : X → Y)
  (hf : CDifferentiableM K (fun xy : X×Y => f xy.1 xy.2)) (hg : CDifferentiable K g)
  : fwdDerivM K (fun x => let y := g x; f x y)
    =
    fun x dx =>
      let ydy := fwdDeriv K g x dx
      fwdDerivM K (fun xy : X×Y => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2) :=
by
  let f' := (fun xy : X×Y => f xy.1 xy.2)
  let g' := (fun x => (x,g x))
  have hg' : CDifferentiable K g' := by rw[show g' = (fun x => (x,g x)) by rfl]; fun_prop
  conv =>
    lhs
    rw[show ((fun x => f x (g x))
             =
             fun x => pure (g' x) >>= f') by simp]
    rw[fwdDerivM_bind f' (fun x => pure (g' x)) hf (CDifferentiableM_pure g' hg')]
    simp[fwdDerivM_pure (K:=K) g' hg']
    -- fun_trans
    -- simp
  sorry_proof

end fwdDerivM

end SciLean



--------------------------------------------------------------------------------

section CoreFunctionProperties

open SciLean

variable
  (K : Type _) [RCLike K]
  {m m'} [Monad m] [Monad m'] [FwdDerivMonad K m m']
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
  apply FwdDerivMonad.CDifferentiableM_pure a0 ha0


@[fun_trans]
theorem Pure.pure.arg_a0.fwdDerivM_rule
  (a0 : X → Y)
  (ha0 : CDifferentiable K a0)
  : fwdDerivM K (fun x => pure (f:=m) (a0 x))
    =
    fun x dx => pure (fwdDeriv K a0 x dx) :=
by
  apply FwdDerivMonad.fwdDerivM_pure a0 ha0

@[simp, ftrans_simp]
theorem Pure.pure.arg.CDifferentiableValM_rule (x : X)
  : CDifferentiableValM K (pure (f:=m) x) :=
by
  unfold CDifferentiableValM
  apply FwdDerivMonad.CDifferentiableM_pure
  fun_prop

@[simp, ftrans_simp]
theorem Pure.pure.arg.fwdDerivValM_rule (x : X)
  : fwdDerivValM K (pure (f:=m) x)
    =
    pure (x,0) :=
by
  unfold fwdDerivValM; rw[FwdDerivMonad.fwdDerivM_pure]; fun_trans; fun_prop


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
    by apply FwdDerivMonad.CDifferentiableM_pair a0 ha0
  have hf : CDifferentiableM K f := by simp[f]; fun_prop

  apply FwdDerivMonad.CDifferentiableM_bind _ _ hf hg



@[fun_trans]
theorem Bind.bind.arg_a0a1.fwdDerivM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : CDifferentiableM K a0) (ha1 : CDifferentiableM K (fun (xy : X×Y) => a1 xy.1 xy.2))
  : (fwdDerivM K (fun x => Bind.bind (a0 x) (a1 x)))
    =
    (fun x dx => do
      let ydy ← fwdDerivM K a0 x dx
      fwdDerivM K (fun (xy : X×Y) => a1 xy.1 xy.2) (x, ydy.1) (dx, ydy.2)) :=
by
  let g := fun x => do
    let y ← a0 x
    pure (x,y)
  let f := fun xy : X×Y => a1 xy.1 xy.2

  rw[show (fun x => Bind.bind (a0 x) (a1 x))
          =
          fun x => g x >>= f by simp[f,g]]

  have hg : CDifferentiableM K (fun x => do let y ← a0 x; pure (x,y)) :=
    by apply FwdDerivMonad.CDifferentiableM_pair a0 ha0
  have hf : CDifferentiableM K f := by simp [f]; fun_prop

  rw [FwdDerivMonad.fwdDerivM_bind _ _ hf hg]
  simp [FwdDerivMonad.fwdDerivM_pair a0 ha0]


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
theorem ite.arg_te.fwdDerivM_rule
  (c : Prop) [dec : Decidable c] (t e : X → m Y)
  : fwdDerivM K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (fwdDerivM K t y) (fwdDerivM K e y) :=
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
theorem dite.arg_te.fwdDerivM_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → m Y) (e : ¬c → X → m Y)
  : fwdDerivM K (fun x => dite c (fun h => t h x) (fun h => e h x))
    =
    fun y =>
      dite c (fun h => fwdDerivM K (t h) y) (fun h => fwdDerivM K (e h) y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]
