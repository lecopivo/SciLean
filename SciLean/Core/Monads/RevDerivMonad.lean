import SciLean.Core.FunctionTransformations.RevCDeriv

namespace SciLean


set_option linter.unusedVariables false in
class RevDerivMonad (K : Type) [IsROrC K] (m : Type → Type) (m' : outParam $ Type → Type) [Monad m] [Monad m'] where
  revDerivM {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] : ∀ (f : X → m Y) (x : X), m (Y × (Y → m' X))

  HasAdjDiffM {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
    : ∀ (f : X → m Y), Prop

  revDerivM_pure {X Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] (f : X → Y) (hf : HasAdjDiff K f)
    : revDerivM (fun x => pure (f:=m) (f x)) = fun x => let ydf := revCDeriv K f x; pure (ydf.1, fun dy => pure (ydf.2 dy))
  revDerivM_bind 
    {X Y Z : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] [SemiInnerProductSpace K Z] 
    (f : Y → m Z) (g : X → m Y) (hf : HasAdjDiffM f) (hg : HasAdjDiffM g)
     : revDerivM (fun x => g x >>= f) 
       = 
       fun x => do
         let ydg ← revDerivM g x
         let zdf ← revDerivM f ydg.1
         pure (zdf.1, fun dz => zdf.2 dz >>= ydg.2)
  revDerivM_pair {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] -- is this really necessary?
    (f : X → m Y) (hf : HasAdjDiffM f)
    : revDerivM (fun x => do let y ← f x; pure (x,y))
      =
      (fun x => do
        let ydf ← revDerivM f x
        pure ((x,ydf.1), fun dxy : X×Y => do let dx ← ydf.2 dxy.2; pure (dxy.1 + dx)))


  HasAdjDiffM_pure {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] 
    (f : X → Y) (hf : HasAdjDiff K f)
    : HasAdjDiffM (fun x : X => pure (f x))
  HasAdjDiffM_bind {X Y Z: Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] [SemiInnerProductSpace K Z]
    (f : Y → m Z) (g : X → m Y) 
    (hf : HasAdjDiffM f) (hg : HasAdjDiffM g)
    : HasAdjDiffM (fun x => g x >>= f)
  HasAdjDiffM_pair {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] -- is this really necessary?
    (f : X → m Y) (hf : HasAdjDiffM f)
    : HasAdjDiffM (fun x => do let y ← f x; pure (x,y))


export RevDerivMonad (revDerivM HasAdjDiffM)


variable 
  (K : Type _) [IsROrC K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m'] [RevDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {E : ι → Type} [∀ i, SemiInnerProductSpace K (E i)]

open RevDerivMonad



def revDerivValM (x : m X) : m (X × (X → m' Unit)) := do
  revDerivM K (fun _ : Unit => x) ()

def HasAdjDiffValM (x : m X) : Prop := 
  HasAdjDiffM K (fun _ : Unit => x)


--------------------------------------------------------------------------------
-- HasAdjDiffM -----------------------------------------------------------
--------------------------------------------------------------------------------
namespace HasAdjDiffM 

-- id_rule does not make sense

variable (X)
theorem const_rule (y : m Y) (hy : HasAdjDiffValM K y)
  : HasAdjDiffM K (fun _ : X => y) := 
by 
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  apply HasAdjDiffM_bind
  apply hy
  apply HasAdjDiffM_pure
  fprop
variable {X}

theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : HasAdjDiffM K f) (hg : HasAdjDiff K g)
  : HasAdjDiffM K (fun x => f (g x)) :=
by
  rw[show ((fun x => f (g x))
           =
           fun x => pure (g x) >>= f) by simp]
  apply HasAdjDiffM_bind _ _ hf
  apply HasAdjDiffM_pure g hg


theorem let_rule 
  (f : X → Y → m Z) (g : X → Y)
  (hf : HasAdjDiffM K (fun xy : X×Y => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : HasAdjDiffM K (fun x => let y := g x; f x y) :=
by
  let f' := (fun xy : X×Y => f xy.1 xy.2)
  let g' := (fun x => (x, g x))
  rw[show ((fun x => f x (g x))
           =
           fun x => pure (g' x) >>= f') by simp]
  apply HasAdjDiffM_bind _ _ hf
  apply HasAdjDiffM_pure g'
  try fprop -- this should finish the proof 
  apply Prod.mk.arg_fstsnd.HasAdjDiff_rule
  fprop; apply hg
  

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``HasAdjDiffM
  getFPropFun? e := 
    if e.isAppOf ``HasAdjDiffM then

      if let .some f := e.getArg? 11 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``HasAdjDiffM then
      e.setArg 11  f
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
    let .some m' := e.getArg? 3 | return none

    let prf ← mkAppOptM ``comp_rule #[K, none,none,m',none,none,none,none,none,none,none,none,none,none, f,g]


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
    let .some M' := e.getArg? 5 | return none
    let .some FDM := e.getArg? 6 | return none

    let prf ← mkAppOptM ``let_rule #[K, none,none,m',none,M',FDM,none,none,none,none,none,none,none, f,g]

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
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``HasAdjDiffM, fpropExt))


end HasAdjDiffM 



--------------------------------------------------------------------------------
-- HasAdjDiffValM -----------------------------------------------------------
--------------------------------------------------------------------------------
namespace HasAdjDiffValM 

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``HasAdjDiffValM
  getFPropFun? e := 
    if e.isAppOf ``HasAdjDiffValM then

      if let .some f := e.getArg? 9 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``HasAdjDiffValM then
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
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``HasAdjDiffValM, fpropExt))


end HasAdjDiffValM 


--------------------------------------------------------------------------------
-- revDerivM -------------------------------------------------------------------
--------------------------------------------------------------------------------
namespace revDerivM

-- id_rule does not make sense


variable (X)
theorem const_rule (y : m Y) (hy : HasAdjDiffValM K y)
  : revDerivM K (fun _ : X => y) 
    = 
    (fun _ => do 
      let ydy ← revDerivValM K y
      pure (ydy.1, 
            fun dy' => do 
              let _ ← ydy.2 dy'
              pure 0)) := 
by
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  rw[revDerivM_bind]
  rw[revDerivM_pure]
  ftrans
  simp [revDerivValM]
  fprop
  apply hy
  apply HasAdjDiffM_pure; fprop
variable {X}

theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : HasAdjDiffM K f) (hg : HasAdjDiff K g)
  : revDerivM K (fun x => f (g x)) 
    =
    (fun x => do
      let ydg := revCDeriv K g x
      let zdf ← revDerivM K f ydg.1
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
    rw[revDerivM_bind f (fun x => pure (g x)) 
         hf (HasAdjDiffM_pure _ hg)]
    simp[revDerivM_pure g hg]


theorem let_rule 
  (f : X → Y → m Z) (g : X → Y)
  (hf : HasAdjDiffM K (fun xy : X×Y => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : revDerivM K (fun x => f x (g x))
    =
    (fun x => do
      let ydg := revCDeriv K g x
      let zdf ← revDerivM K (fun xy : X×Y => f xy.1 xy.2) (x,ydg.1)
      pure (zdf.1,
            fun dz => do
              let dxy ← zdf.2 dz
              let dx := ydg.2 dxy.2
              pure (dxy.1 + dx))) :=
by
  let f' := (fun xy : X×Y => f xy.1 xy.2)
  let g' := (fun x => (x,g x))
  have hg' : HasAdjDiff K g' := by rw[show g' = (fun x => (x,g x)) by rfl]; fprop
  conv =>
    lhs
    rw[show ((fun x => f x (g x))
             =
             fun x => pure (g' x) >>= f') by simp]
    rw[revDerivM_bind f' (fun x => pure (g' x)) hf (HasAdjDiffM_pure g' hg')]
    simp[revDerivM_pure (K:=K) g' hg']
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
  ftransName := ``revDerivM

  getFTransFun? e := 
    if e.isAppOf ``revDerivM then

      if let .some f := e.getArg? 11 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``revDerivM then
      let fn := e.getAppFn'
      let args := e.getAppArgs'
      let args := args.set! 11 f
      let e' := mkAppN fn args
      e'
    else          
      e

  idRule  e X := return none

  constRule e X y := do
    let .some K := e.getArg? 0 | return none
    let .some m := e.getArg? 2 | return none
    let .some m' := e.getArg? 3 | return none
    let .some M' := e.getArg? 5 | return none
    let .some RDM := e.getArg? 6 | return none
    let .some Y := e.getArg? 8 | return none


    let prf ← mkAppOptM ``const_rule #[K, none, m, m', none, M', RDM, none, X, none, Y, none]
    -- this is a hack to deal with Id monad
    let prf := prf.app y

    tryTheorems
      #[ { proof := prf, origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := return none

  compRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some m' := e.getArg? 3 | return none
    let .some M' := e.getArg? 5 | return none
    let .some RDM := e.getArg? 6 | return none

    let prf ← mkAppOptM ``comp_rule #[K, none, none, m', none, M', RDM, none, none, none, none, none, none, none, f, g]

    tryTheorems
      #[ { proof := prf, origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some m' := e.getArg? 3 | return none
    let .some M' := e.getArg? 5 | return none
    let .some RDM := e.getArg? 6 | return none

    let prf ← mkAppOptM ``let_rule #[K, none, none, m', none, M', RDM, none, none, none, none, none, none, none, f, g]

    tryTheorems
      #[ { proof := prf, origin := .decl ``let_rule, rfl := false} ]
      discharger e

  piRule  e f := return none

  discharger := revDerivM.discharger


-- register revDerivM
open Lean in
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revDerivM, ftransExt))


end revDerivM


--------------------------------------------------------------------------------
-- revDerivValM ----------------------------------------------------------------
--------------------------------------------------------------------------------
namespace revDerivValM

open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `revDerivValM_discharger (fun _ => return s!"discharge {← ppExpr e}") do
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
  ftransName := ``revDerivValM

  getFTransFun? e := 
    if e.isAppOf ``revDerivValM then

      if let .some f := e.getArg? 9 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``revDerivValM then
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


-- register revDerivValM
open Lean in
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revDerivValM, ftransExt))

end revDerivValM


end SciLean



--------------------------------------------------------------------------------

section CoreFunctionProperties 

open SciLean

variable 
  (K : Type _) [IsROrC K]
  {m m'} [Monad m] [Monad m'] [RevDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {E : ι → Type} [∀ i, SemiInnerProductSpace K (E i)]


--------------------------------------------------------------------------------
-- Pure.pure -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Pure.pure.arg_a0.HasAdjDiffM_rule
  (a0 : X → Y)
  (ha0 : HasAdjDiff K a0) 
  : HasAdjDiffM K (fun x => Pure.pure (f:=m) (a0 x)) := 
by 
  apply RevDerivMonad.HasAdjDiffM_pure a0 ha0


@[ftrans]
theorem Pure.pure.arg_a0.revDerivM_rule
  (a0 : X → Y)
  (ha0 : HasAdjDiff K a0) 
  : revDerivM K (fun x => pure (f:=m) (a0 x))
    =
    (fun x => do
      let ydf := revCDeriv K a0 x
      pure (ydf.1, fun dy => pure (ydf.2 dy))):= 
by 
  apply RevDerivMonad.revDerivM_pure a0 ha0


set_option linter.fpropDeclName false in
@[fprop]
theorem Pure.pure.HasAdjDiffValM_rule (x : X)
  : HasAdjDiffValM K (pure (f:=m) x) :=  
by
  unfold HasAdjDiffValM
  apply RevDerivMonad.HasAdjDiffM_pure
  fprop


@[ftrans]
theorem Pure.pure.arg.revDerivValM_rule (x : X)
  : revDerivValM K (pure (f:=m) x)
    =
    pure (x,fun dy => pure 0) := 
by 
  unfold revDerivValM; rw[RevDerivMonad.revDerivM_pure]; ftrans; fprop


--------------------------------------------------------------------------------
-- Bind.bind -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop] 
theorem Bind.bind.arg_a0a1.HasAdjDiffM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : HasAdjDiffM K a0) (ha1 : HasAdjDiffM K (fun (xy : X×Y) => a1 xy.1 xy.2))
  : HasAdjDiffM K (fun x => Bind.bind (a0 x) (a1 x)) := 
by 
  let g := fun x => do
    let y ← a0 x
    pure (x,y)
  let f := fun xy : X×Y => a1 xy.1 xy.2

  rw[show (fun x => Bind.bind (a0 x) (a1 x)) 
          = 
          fun x => g x >>= f by simp]

  have hg : HasAdjDiffM K (fun x => do let y ← a0 x; pure (x,y)) := 
    by apply RevDerivMonad.HasAdjDiffM_pair a0 ha0
  have hf : HasAdjDiffM K f := by fprop

  apply RevDerivMonad.HasAdjDiffM_bind _ _ hf hg



@[ftrans] 
theorem Bind.bind.arg_a0a1.revDerivM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : HasAdjDiffM K a0) (ha1 : HasAdjDiffM K (fun (xy : X×Y) => a1 xy.1 xy.2))
  : (revDerivM K (fun x => Bind.bind (a0 x) (a1 x)))
    = 
    (fun x => do
      let ydg ← revDerivM K a0 x 
      let zdf ← revDerivM K (fun (xy : X×Y) => a1 xy.1 xy.2) (x,ydg.1)
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
          fun x => g x >>= f by simp]

  have hg : HasAdjDiffM K (fun x => do let y ← a0 x; pure (x,y)) :=
    by apply RevDerivMonad.HasAdjDiffM_pair a0 ha0
  have hf : HasAdjDiffM K f := by fprop

  rw [RevDerivMonad.revDerivM_bind _ _ hf hg]
  simp [RevDerivMonad.revDerivM_pair a0 ha0]


-------------------------------------------------------------------------------- 
-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem ite.arg_te.HasAdjDiffM_rule
  (c : Prop) [dec : Decidable c] (t e : X → m Y)
  (ht : HasAdjDiffM K t) (he : HasAdjDiffM K e)
  : HasAdjDiffM K (fun x => ite c (t x) (e x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]


@[ftrans]
theorem ite.arg_te.revDerivM_rule
  (c : Prop) [dec : Decidable c] (t e : X → m Y)
  : revDerivM K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDerivM K t y) (revDerivM K e y) := 
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]


@[fprop]
theorem dite.arg_te.HasAdjDiffM_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → m Y) (e : ¬c → X → m Y)
  (ht : ∀ h, HasAdjDiffM K (t h)) (he : ∀ h, HasAdjDiffM K (e h))
  : HasAdjDiffM K (fun x => dite c (fun h => t h x) (fun h => e h x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]


@[ftrans]
theorem dite.arg_te.revDerivM_rule
  (c : Prop) [dec : Decidable c] 
  (t : c → X → m Y) (e : ¬c → X → m Y)
  : revDerivM K (fun x => dite c (fun h => t h x) (fun h => e h x))
    =
    fun y =>
      dite c (fun h => revDerivM K (t h) y) (fun h => revDerivM K (e h) y) := 
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]
