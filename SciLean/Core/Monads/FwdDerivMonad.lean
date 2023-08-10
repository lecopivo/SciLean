import SciLean.Core.FunctionTransformations.FwdCDeriv

namespace SciLean


set_option linter.unusedVariables false in
class FwdDerivMonad (K : Type _) [IsROrC K] (m : Type _ → Type _) (m' : outParam $ Type _ → Type _) [Monad m] [Monad m'] where
  fwdDerivM {X : Type} {Y : Type} [Vec K X] [Vec K Y] : ∀ (f : X → m Y) (x dx : X), m' (Y × Y)
  fwdDerivValM : ∀ {X} [Vec K X], m X → m' (X × X)

  IsDifferentiableM {X : Type} {Y : Type} [Vec K X] [Vec K Y]
    : ∀ (f : X → m Y), Prop
  IsDifferentiableValM {X : Type} [Vec K X]
    : ∀ (x : m X), Prop

  fwdDerivM_pure {X Y : Type} [Vec K X] [Vec K Y] (f : X → Y) (hf : IsDifferentiable K f)
    : fwdDerivM (fun x => pure (f:=m) (f x)) = fun x dx => pure (f:=m') (fwdCDeriv K f x dx)
  fwdDerivM_bind 
    {X Y Z : Type} [Vec K X] [Vec K Y] [Vec K Z] 
    (f : Y → m Z) (g : X → m Y) (hf : IsDifferentiableM f) (hg : IsDifferentiableM g)
     : fwdDerivM (fun x => g x >>= f) 
       = 
       fun x dx => do
         let ydy ← fwdDerivM g x dx
         fwdDerivM f ydy.1 ydy.2
  fwdDerivM_const {X Y : Type} [Vec K X] [Vec K Y] (y : m Y) (hy : IsDifferentiableValM y)
    : fwdDerivM (fun _ : X => y) = fun _ _ => fwdDerivValM y
  fwdDerivM_pair {X : Type} {Y : Type} [Vec K X] [Vec K Y] -- is this really necessary?
    (f : X → m Y) (hf : IsDifferentiableM f)
    : fwdDerivM (fun x => do let y ← f x; pure (x,y))
      =
      (fun x dx => do
        let ydy ← fwdDerivM f x dx
        pure ((x,ydy.1),(dx,ydy.2)))


  IsDifferentiableM_pure {X : Type} {Y : Type} [Vec K X] [Vec K Y] (f : X → Y)
    : IsDifferentiable K f ↔ IsDifferentiableM (fun x : X => pure (f x))
  IsDifferentiableM_bind {X Y Z: Type} [Vec K X] [Vec K Y] [Vec K Z]
    (f : Y → m Z) (g : X → m Y) 
    (hf : IsDifferentiableM f) (hg : IsDifferentiableM g)
    : IsDifferentiableM (fun x => g x >>= f)
  IsDifferentiableM_const {X : Type} {Y : Type} [Vec K X] [Vec K Y]
    : ∀ (y : m Y), IsDifferentiableValM y ↔ IsDifferentiableM (fun _ : X => y)
  IsDifferentiableM_pair {X : Type} {Y : Type} [Vec K X] [Vec K Y] -- is this really necessary?
    (f : X → m Y) (hf : IsDifferentiableM f)
    : IsDifferentiableM (fun x => do let y ← f x; pure (x,y))

export FwdDerivMonad (fwdDerivM IsDifferentiableM fwdDerivValM IsDifferentiableValM)


variable 
  (K : Type _) [IsROrC K]
  {m m'} [Monad m] [Monad m'] [FwdDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]
  {E : ι → Type} [∀ i, Vec K (E i)]

open FwdDerivMonad


--------------------------------------------------------------------------------
-- IsDifferentiableM -----------------------------------------------------------
--------------------------------------------------------------------------------
namespace IsDifferentiableM 

-- id_rule does not make sense

variable (X)
theorem const_rule (y : m Y) (hy : IsDifferentiableValM K y)
  : IsDifferentiableM K (fun _ : X => y) := 
by 
  apply (IsDifferentiableM_const y).1 hy
variable {X}

theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : IsDifferentiableM K f) (hg : IsDifferentiable K g)
  : IsDifferentiableM K (fun x => f (g x)) :=
by
  rw[show ((fun x => f (g x))
           =
           fun x => pure (g x) >>= f) by simp]
  apply IsDifferentiableM_bind _ _ hf
  apply (IsDifferentiableM_pure g).1 hg


theorem let_rule 
  (f : X → Y → m Z) (g : X → Y)
  (hf : IsDifferentiableM K (fun xy : X×Y => f xy.1 xy.2)) (hg : IsDifferentiable K g)
  : IsDifferentiableM K (fun x => let y := g x; f x y) :=
by
  let f' := (fun xy : X×Y => f xy.1 xy.2)
  let g' := (fun x => (x, g x))
  rw[show ((fun x => f x (g x))
           =
           fun x => pure (g' x) >>= f') by simp]
  apply IsDifferentiableM_bind _ _ hf
  apply (IsDifferentiableM_pure g').1 
  try fprop -- this should finish the proof 
  apply Prod.mk.arg_fstsnd.IsDifferentiable_rule
  apply hg
  fprop
  

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``IsDifferentiableM
  getFPropFun? e := 
    if e.isAppOf ``IsDifferentiableM then

      if let .some f := e.getArg? 11 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``IsDifferentiableM then
      e.modifyArg (fun _ => f) 11 
    else          
      e

  identityRule _ := return none 

  constantRule e := 
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``const_rule
      origin := .decl ``const_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  projRule _ := return none

  compRule e f g := do
    let .some K := e.getArg? 0 | return none

    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``comp_rule #[K, f, g]
      origin := .decl ``comp_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLetRule e f g := do
    let .some K := e.getArg? 0 | return none

    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``let_rule #[K, f,g]
      origin := .decl ``let_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLambdaRule _ _ := return none

  discharger e := 
    FProp.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption") e


-- Register IsDiferentiableM --
-------------------------------
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``IsDifferentiableM, fpropExt))


end IsDifferentiableM 


--------------------------------------------------------------------------------
-- fwdDerivM -------------------------------------------------------------------
--------------------------------------------------------------------------------
namespace fwdDerivM

-- id_rule does not make sense


variable (X)
theorem const_rule (y : m Y) (hy : IsDifferentiableValM K y)
  : fwdDerivM K (fun _ : X => y) = fun _ _ => fwdDerivValM K y := by apply FwdDerivMonad.fwdDerivM_const _ hy
variable {X}

theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : IsDifferentiableM K f) (hg : IsDifferentiable K g)
  : fwdDerivM K (fun x => f (g x)) 
    =
    fun x dx =>
      let ydy := fwdCDeriv K g x dx
      fwdDerivM K f ydy.1 ydy.2 :=
by
  conv =>
    lhs
    rw[show ((fun x => f (g x))
             =
             fun x => pure (g x) >>= f) by simp]
    rw[FwdDerivMonad.fwdDerivM_bind f (fun x => pure (g x)) 
         hf ((FwdDerivMonad.IsDifferentiableM_pure _).1 hg)]
    simp[FwdDerivMonad.fwdDerivM_pure g hg]


theorem let_rule 
  (f : X → Y → m Z) (g : X → Y)
  (hf : IsDifferentiableM K (fun xy : X×Y => f xy.1 xy.2)) (hg : IsDifferentiable K g)
  : fwdDerivM K (fun x => f x (g x))
    =
    fun x dx =>
      let ydy := fwdCDeriv K g x dx
      fwdDerivM K (fun xy : X×Y => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2) :=
by
  let f' := (fun xy : X×Y => f xy.1 xy.2)
  let g' := (fun x => (x,g x))
  have hg' : IsDifferentiable K g' := by rw[show g' = (fun x => (x,g x)) by rfl]; fprop
  conv =>
    lhs
    rw[show ((fun x => f x (g x))
             =
             fun x => pure (g' x) >>= f') by simp]
    rw[fwdDerivM_bind f' (fun x => pure (g' x)) hf ((IsDifferentiableM_pure g').1 hg')]
    simp[fwdDerivM_pure (K:=K) g' hg']
    ftrans; simp


open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `fwdDeriv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
  let cache := (← get).cache
  let config : FProp.Config := {}
  let state  : FProp.State := { cache := cache }
  let (proof?, state) ← FProp.fprop e |>.run config |>.run state
  modify (fun simpState => { simpState with cache := state.cache })
  if proof?.isSome then
    return proof?
  else
    -- if `fprop` fails try assumption
    let tac := FTrans.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption")
    let proof? ← tac e
    return proof?

set_option linter.unusedVariables false in
open Lean Meta FTrans in
def ftransExt : FTransExt where
  ftransName := ``fwdDerivM

  getFTransFun? e := 
    if e.isAppOf ``fwdDerivM then

      if let .some f := e.getArg? 11 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``fwdDerivM then
      e.modifyArg (fun _ => f) 11
    else          
      e

  idRule  e X := return none

  constRule e X y := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[K, X, y], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := return none

  compRule e f g := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``comp_rule #[K, f, g], origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[K, f, g], origin := .decl ``let_rule, rfl := false} ]
      discharger e

  piRule  e f := return none

  discharger := fwdDerivM.discharger


-- register fwdDerivM
open Lean in
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``fwdDerivM, ftransExt))


end fwdDerivM
end SciLean


--------------------------------------------------------------------------------

section CoreFunctionProperties 

open SciLean

variable 
  (K : Type _) [IsROrC K]
  {m m'} [Monad m] [Monad m'] [FwdDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]
  {E : ι → Type} [∀ i, Vec K (E i)]


--------------------------------------------------------------------------------
-- Pure.pure -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Pure.pure.arg_a0.IsDifferentiableM_rule
  (a0 : X → Y)
  (ha0 : IsDifferentiable K a0) 
  : IsDifferentiableM K (fun x => Pure.pure (f:=m) (a0 x)) := 
by 
  apply (FwdDerivMonad.IsDifferentiableM_pure a0).1 ha0

@[ftrans]
theorem Pure.pure.arg_a0.fwdDerivM_rule
  (a0 : X → Y)
  (ha0 : IsDifferentiable K a0) 
  : fwdDerivM K (fun x => pure (f:=m) (a0 x))
    =
    fun x dx => pure (fwdCDeriv K a0 x dx) := 
by 
  apply FwdDerivMonad.fwdDerivM_pure a0 ha0


--------------------------------------------------------------------------------
-- Bind.bind -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop] 
theorem Bind.bind.arg_a0a1.IsDifferentiableM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : IsDifferentiableM K a0) (ha1 : IsDifferentiableM K (fun (xy : X×Y) => a1 xy.1 xy.2))
  : IsDifferentiableM K (fun x => Bind.bind (a0 x) (a1 x)) := 
by 
  let g := fun x => do
    let y ← a0 x
    pure (x,y)
  let f := fun xy : X×Y => a1 xy.1 xy.2

  rw[show (fun x => Bind.bind (a0 x) (a1 x)) 
          = 
          fun x => g x >>= f by simp]

  have hg : IsDifferentiableM K (fun x => do let y ← a0 x; pure (x,y)) := 
    by apply FwdDerivMonad.IsDifferentiableM_pair a0 ha0
  have hf : IsDifferentiableM K f := by fprop

  apply FwdDerivMonad.IsDifferentiableM_bind _ _ hf hg



@[ftrans] 
theorem Bind.bind.arg_a0a1.fwdDerivM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : IsDifferentiableM K a0) (ha1 : IsDifferentiableM K (fun (xy : X×Y) => a1 xy.1 xy.2))
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
          fun x => g x >>= f by simp]

  have hg : IsDifferentiableM K (fun x => do let y ← a0 x; pure (x,y)) :=
    by apply FwdDerivMonad.IsDifferentiableM_pair a0 ha0
  have hf : IsDifferentiableM K f := by fprop

  rw [FwdDerivMonad.fwdDerivM_bind _ _ hf hg]
  simp [FwdDerivMonad.fwdDerivM_pair a0 ha0]
