import SciLean.Core.FunctionTransformations.FwdCDeriv

namespace SciLean


set_option linter.unusedVariables false in
class FwdDerivMonad (K : Type) [IsROrC K] (m : Type → Type) (m' : outParam $ Type → Type) [Monad m] [Monad m'] where
  fwdDerivM {X : Type} {Y : Type} [Vec K X] [Vec K Y] : ∀ (f : X → m Y) (x dx : X), m' (Y × Y)

  IsDifferentiableM {X : Type} {Y : Type} [Vec K X] [Vec K Y]
    : ∀ (f : X → m Y), Prop

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
  fwdDerivM_pair {X : Type} {Y : Type} [Vec K X] [Vec K Y] -- is this really necessary?
    (f : X → m Y) (hf : IsDifferentiableM f)
    : fwdDerivM (fun x => do let y ← f x; pure (x,y))
      =
      (fun x dx => do
        let ydy ← fwdDerivM f x dx
        pure ((x,ydy.1),(dx,ydy.2)))


  IsDifferentiableM_pure {X : Type} {Y : Type} [Vec K X] [Vec K Y] 
    (f : X → Y) (hf : IsDifferentiable K f)
    : IsDifferentiableM (fun x : X => pure (f x))
  IsDifferentiableM_bind {X Y Z: Type} [Vec K X] [Vec K Y] [Vec K Z]
    (f : Y → m Z) (g : X → m Y) 
    (hf : IsDifferentiableM f) (hg : IsDifferentiableM g)
    : IsDifferentiableM (fun x => g x >>= f)
  IsDifferentiableM_pair {X : Type} {Y : Type} [Vec K X] [Vec K Y] -- is this really necessary?
    (f : X → m Y) (hf : IsDifferentiableM f)
    : IsDifferentiableM (fun x => do let y ← f x; pure (x,y))

export FwdDerivMonad (fwdDerivM IsDifferentiableM)



variable 
  (K : Type _) [IsROrC K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m'] [FwdDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]
  {E : ι → Type} [∀ i, Vec K (E i)]

open FwdDerivMonad


def fwdDerivValM (x : m X) : m' (X × X) := do
  fwdDerivM K (fun _ : Unit => x) () ()

def IsDifferentiableValM (x : m X) : Prop := 
  IsDifferentiableM K (fun _ : Unit => x)


--------------------------------------------------------------------------------
-- IsDifferentiableM -----------------------------------------------------------
--------------------------------------------------------------------------------
namespace IsDifferentiableM 

variable (X)
theorem pure_rule 
  : IsDifferentiableM (m:=m) K (fun x : X => pure x) := 
by
  apply IsDifferentiableM_pure
  fprop


theorem const_rule (y : m Y) (hy : IsDifferentiableValM K y)
  : IsDifferentiableM K (fun _ : X => y) := 
by 
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  apply IsDifferentiableM_bind
  apply hy
  apply IsDifferentiableM_pure
  fprop
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
  apply IsDifferentiableM_pure g hg


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
  apply IsDifferentiableM_pure g'
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
      e.setArg 11  f
    else          
      e

  identityRule e := do
    let .some K := e.getArg? 0 | return none
    let .some m := e.getArg? 2 | return none
    let .some m' := e.getArg? 3 | return none
    let .some X := e.getArg? 7 | return none
    let prf ← mkAppOptM ``pure_rule #[K, none, m, m', none, none, none, X, none]
    return prf 

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
    let .some m' := e.getArg? 3 | return none
    let .some monadM := e.getArg? 4 | return none
    let .some monadM' := e.getArg? 5 | return none
    let .some X := e.getArg? 7 | return none
    let .some Z := e.getArg? 8 | return none
    let .some vecZ := e.getArg? 10 | return none
    let .some (_,Y) := (← inferType g).arrow? | return none

    let prf ← mkAppOptM ``comp_rule #[K, none,none,m',monadM,monadM',none,none,X,none,Y,none,Z,vecZ]
    let prf := prf.mkApp2 f g

    let thm : SimpTheorem :=
    {
      proof  := prf -- ← mkAppM ``comp_rule #[K, f, g]
      origin := .decl ``comp_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLetRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some m' := e.getArg? 3 | return none
    let .some monadM := e.getArg? 4 | return none
    let .some monadM' := e.getArg? 5 | return none
    let .some X := e.getArg? 7 | return none
    let .some Z := e.getArg? 8 | return none
    let .some vecZ := e.getArg? 10 | return none
    let .some (_,Y) := (← inferType g).arrow? | return none

    let prf ← mkAppOptM ``let_rule #[K, none,none,m',monadM,monadM',none,none,X,none,Y,none,Z,vecZ]
    let prf := prf.mkApp2 f g

    let thm : SimpTheorem :=
    {
      proof  := prf
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
-- IsDifferentiableValM -----------------------------------------------------------
--------------------------------------------------------------------------------
namespace IsDifferentiableValM 

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``IsDifferentiableValM
  getFPropFun? e := 
    if e.isAppOf ``IsDifferentiableValM then

      if let .some f := e.getArg? 9 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``IsDifferentiableValM then
      e.setArg 9  f
    else          
      e
  identityRule _ := return none 
  constantRule _ := return none
  projRule _ := return none
  compRule _ _ _ := return none
  lambdaLetRule _ _ _ := return none
  lambdaLambdaRule _ _ := return none

  discharger e := 
    FProp.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption") e


-- Register IsDiferentiableM --
-------------------------------
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``IsDifferentiableValM, fpropExt))


end IsDifferentiableValM 


--------------------------------------------------------------------------------
-- fwdDerivM -------------------------------------------------------------------
--------------------------------------------------------------------------------
namespace fwdDerivM

variable (X)
theorem pure_rule 
  : fwdDerivM (m:=m) K (fun x : X => pure x) = fun x dx => pure (x, dx) := 
by 
  rw [fwdDerivM_pure _ (by fprop)]
  ftrans


theorem const_rule (y : m Y) (hy : IsDifferentiableValM K y)
  : fwdDerivM K (fun _ : X => y) = fun _ _ => fwdDerivValM K y := 
by
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  rw[fwdDerivM_bind]
  rw[fwdDerivM_pure]
  ftrans
  simp [fwdDerivValM]
  fprop
  apply hy
  apply IsDifferentiableM_pure; fprop
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
         hf (FwdDerivMonad.IsDifferentiableM_pure _ hg)]
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
    rw[fwdDerivM_bind f' (fun x => pure (g' x)) hf (IsDifferentiableM_pure g' hg')]
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
      let fn := e.getAppFn'
      let args := e.getAppArgs'
      let args := args.set! 11 f
      let e' := mkAppN fn args
      e'
    else          
      e

  idRule  e X := do
    -- let .some K := e.getArg? 0 | return none
    -- let .some m := e.getArg? 2 | return none
    -- let .some m' := e.getArg? 3 | return none
    -- let .some X := e.getArg? 7 | return none
    -- let prf ← mkAppOptM ``pure_rule #[K, none, m, m', none, none, none, X, none]
    -- let .some (_,_,rhs) := (← inferType prf).eq? | return none
    -- return .some (.visit {expr := rhs, proof? := prf})
    return none

  constRule e X y := do
    let .some K := e.getArg? 0 | return none
    let .some m' := e.getArg? 3 | return none
    let .some M' := e.getArg? 5 | return none
    let .some FDM := e.getArg? 6 | return none

    let prf ← mkAppOptM ``const_rule #[K, none, none, m', none, M', FDM, none, none, X, none, none, none, y]

    tryTheorems
      #[ { proof := prf, origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := return none

  compRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some m := e.getArg? 2 | return none
    let .some m' := e.getArg? 3 | return none
    let .some M' := e.getArg? 5 | return none
    let .some FDM := e.getArg? 6 | return none
    let .some X := e.getArg? 7 | return none
    let .some Z := e.getArg? 8 | return none
    let .some (Y,_) := (←inferType f).arrow? | return none
    let .some vecZ := e.getArg? 10 | return none

    let prf ← mkAppOptM ``comp_rule #[K, none, none, m', none, M', FDM, none, none, X, none, Y, none, Z, vecZ]
    let prf := prf.mkApp2 f g

    tryTheorems
      #[ { proof := prf, origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some m := e.getArg? 2 | return none
    let .some m' := e.getArg? 3 | return none
    let .some M' := e.getArg? 5 | return none
    let .some FDM := e.getArg? 6 | return none
    let .some (X,YmZ) := (←inferType f).arrow? | return none
    let .some (Y,mZ) := (YmZ).arrow? | return none
    let .some Z := e.getArg? 8 | return none
    let .some vecZ := e.getArg? 10 | return none

    let prf ← mkAppOptM ``let_rule #[K, none, m, m', none, M', FDM, none, none, X, none, Y, none, Z, vecZ]
    let prf := prf.mkApp2 f g

    tryTheorems
      #[ { proof := prf, origin := .decl ``let_rule, rfl := false} ]
      discharger e

  piRule  e f := return none

  discharger := fwdDerivM.discharger


-- register fwdDerivM
open Lean in
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``fwdDerivM, ftransExt))


end fwdDerivM


--------------------------------------------------------------------------------
-- fwdDerivValM ----------------------------------------------------------------
--------------------------------------------------------------------------------
namespace fwdDerivValM

open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `fwdDerivValM_discharger (fun _ => return s!"discharge {← ppExpr e}") do
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
  ftransName := ``fwdDerivValM

  getFTransFun? e := 
    if e.isAppOf ``fwdDerivValM then

      if let .some f := e.getArg? 9 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``fwdDerivValM then
      let fn := e.getAppFn'
      let args := e.getAppArgs'
      let args := args.set! 9 f
      let e' := mkAppN fn args
      e'
    else          
      e

  idRule  e X := return none
  constRule e X y := return none
  projRule e X i := return none
  compRule e f g := return none
  letRule e f g := return none
  piRule  e f := return none

  discharger := discharger


-- register fwdDerivValM
open Lean in
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``fwdDerivValM, ftransExt))

end fwdDerivValM


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
  apply FwdDerivMonad.IsDifferentiableM_pure a0 ha0


@[ftrans]
theorem Pure.pure.arg_a0.fwdDerivM_rule
  (a0 : X → Y)
  (ha0 : IsDifferentiable K a0) 
  : fwdDerivM K (fun x => pure (f:=m) (a0 x))
    =
    fun x dx => pure (fwdCDeriv K a0 x dx) := 
by 
  apply FwdDerivMonad.fwdDerivM_pure a0 ha0

set_option linter.fpropDeclName false in
@[fprop]
theorem Pure.pure.arg.IsDifferentiableValM_rule (x : X)
  : IsDifferentiableValM K (pure (f:=m) x) :=  
by
  unfold IsDifferentiableValM
  apply FwdDerivMonad.IsDifferentiableM_pure
  fprop


@[ftrans]
theorem Pure.pure.arg.fwdDerivValM_rule (x : X)
  : fwdDerivValM K (pure (f:=m) x)
    =
    pure (x,0) := 
by 
  unfold fwdDerivValM; rw[FwdDerivMonad.fwdDerivM_pure]; ftrans; fprop


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


-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem ite.arg_te.IsDifferentiableM_rule
  (c : Prop) [dec : Decidable c] (t e : X → m Y)
  (ht : IsDifferentiableM K t) (he : IsDifferentiableM K e)
  : IsDifferentiableM K (fun x => ite c (t x) (e x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]


@[ftrans]
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


@[fprop]
theorem dite.arg_te.IsDifferentiableM_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → m Y) (e : ¬c → X → m Y)
  (ht : ∀ h, IsDifferentiableM K (t h)) (he : ∀ h, IsDifferentiableM K (e h))
  : IsDifferentiableM K (fun x => dite c (fun h => t h x) (fun h => e h x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]


@[ftrans]
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
