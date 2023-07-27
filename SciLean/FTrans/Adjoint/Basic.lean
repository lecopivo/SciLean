import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

import SciLean.FunctionSpaces.ContinuousLinearMap.Basic
import SciLean.FunctionSpaces.ContinuousLinearMap.Notation

import SciLean.Tactic.FTrans.Basic

import SciLean.Mathlib.Analysis.InnerProductSpace.Prod
import SciLean.Profile


namespace  ContinuousLinearMap.adjoint

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]


-- TODO: move to mathlib
instance {E : ι → Type _} [∀ i, UniformSpace (E i)] [∀ i, CompleteSpace (E i)] : CompleteSpace (PiLp 2 E) := by unfold PiLp; infer_instance


-- Set up custom notation for adjoint. Mathlib's notation for adjoint seems to be broken
instance (f : X →L[K] Y) : SciLean.Dagger f (ContinuousLinearMap.adjoint f : Y →L[K] X) := ⟨⟩
variable (g : X → Y) (hg : SciLean.IsContinuousLinearMap K g)


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

theorem id_rule 
  : (fun (x : X) =>L[K] x)† = fun x =>L[K] x := 
by
  have h : (fun (x : X) =>L[K] x) = ContinuousLinearMap.id K X := by rfl
  rw[h]; simp


theorem const_rule 
  : (fun (x : X) =>L[K] (0 : Y))† = fun x =>L[K] 0 := 
by
  sorry

theorem prod_rule
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : X → Z) (hf : IsContinuousLinearMap K f)
  : ((fun x =>L[K] (g x, f x)) : X →L[K] Y×₂Z)†
    =
    fun yz : Y×₂Z =>L[K]
      let x₁ := (fun x =>L[K] g x)† yz.1
      let x₂ := (fun x =>L[K] f x)† yz.2
      x₁ + x₂ := 
by 
  sorry


theorem comp_rule 
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : Y → Z) (hf : IsContinuousLinearMap K f)
  : (fun x =>L[K] f (g x))†
    =
    fun z =>L[K]
      let y := (fun y =>L[K] f y)† z
      let x := (fun x =>L[K] g x)† y
      x := 
by
  have h : (fun x =>L[K] f (g x))
           =
           (fun y =>L[K] f y).comp (fun x =>L[K] g x)
         := by rfl
  rw[h]
  rw[ContinuousLinearMap.adjoint_comp]
  ext dx; simp


theorem let_rule 
  (g : X → Y)      (hg : IsContinuousLinearMap K g)
  (f : X → Y → Z) (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2))
  : (fun x =>L[K] let y := g x; f x y)†
    =
    fun z =>L[K]
      let xy := ((fun xy : X×₂Y =>L[K] f xy.1 xy.2)†) z
      let x' := ((fun x =>L[K] g x)†) xy.2
      xy.1 + x' := 
by
  have h : (fun x =>L[K] let y := g x; f x y)
           =
           (fun xy : X×₂Y =>L[K] f xy.1 xy.2).comp (fun x =>L[K] (x, g x))
         := by rfl
  rw[h, ContinuousLinearMap.adjoint_comp]
  have h' : ((fun x =>L[K] (x, g x)) : X →L[K] X×₂Y)† 
            = 
            (fun (xy : X×₂Y) =>L[K] xy.1 + (fun x =>L[K] g x)† xy.2)
          := by rw[prod_rule (fun x => x) (by fprop) g hg]; simp[id_rule]
  rw[h']; rfl



example : CompleteSpace ((i :ι) → E i) := by infer_instance

open BigOperators

-- set_option trace.Meta.Tactic.fprop.discharge true in
-- set_option trace.Meta.Tactic.fprop.step true in
theorem pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, IsContinuousLinearMap K (f i))
  : ((fun (x : X) =>L[K] fun (i : ι) => f i x) : X →L[K] PiLp 2 E)†
    = 
    (fun x' =>L[K] ∑ i, (fun x =>L[K] f i x)† (x' i))
  := sorry


set_option trace.Meta.Tactic.fprop.discharge true in
-- theorem proj_rule [DecidableEq ι]
--    (i : ι) 
--   : (fun (f : PiLp 2 E) =>L[K] f i)†
--     = 
--     fun y =>L[K] ((fun j => if h : i=j then (h ▸ y) else (0 : E j)) : PiLp 2 E)
--   := sorry

theorem proj_rule [DecidableEq ι]
   (i : ι) 
  : (fun (f : PiLp 2 (fun _ => X)) =>L[K] f i)†
    = 
    fun x =>L[K] (fun j => if h : i=j then x else (0 : X))
  := sorry


-- Register `adjoint` as function transformation -------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq

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

open Lean Elab Term FTrans
def ftransExt : FTransExt where
  ftransName := ``adjoint

  getFTransFun? e := Id.run do
    let (name, args) := e.getAppFnArgs
    if name == ``FunLike.coe && args.size = 6 then
      
      if ¬(args[4]!.isAppOf ``adjoint) then
        return none

      let f := args[5]!
      if f.isAppOf ``ContinuousLinearMap.mk' then
        if let .some f' := f.getArg? 10 then
          return f'
        else
          return f
      else
        return f

    return none

  replaceFTransFun e f := Id.run do
    let (name, args) := e.getAppFnArgs
    if name == ``FunLike.coe && args.size = 6 then
      
      if ¬(args[4]!.isAppOf ``adjoint) then
        return e         
      
      return e.modifyArg (fun _ => f) 5
    else
      return e

  identityRule     := .some <| .thm ``adjoint.id_rule
  constantRule     := .some <| .thm ``adjoint.const_rule
  compRule         := .some <| .thm ``adjoint.comp_rule
  lambdaLetRule    := .some <| .thm ``adjoint.let_rule
  lambdaLambdaRule := .some <| .thm ``adjoint.pi_rule

  discharger := adjoint.discharger


-- register adjoint
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``adjoint, adjoint.ftransExt))

end ContinuousLinearMap.adjoint


--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]

open SciLean

-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------



example
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : X → Z) (hf : IsContinuousLinearMap K f)
  : IsContinuousLinearMap K
    fun yz : Y×₂Z =>
      (fun x =>L[K] g x)† yz.1 + (fun x =>L[K] f x)† yz.2 := by fprop


set_option trace.Meta.Tactic.fprop.step true in
set_option trace.Meta.Tactic.fprop.discharge true in
@[ftrans_rule]
theorem Prod.mk.arg_fstsnd.adjoint_comp
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : X → Z) (hf : IsContinuousLinearMap K f)
  : ((fun x =>L[K] (g x, f x)) : X →L[K] Y×₂Z)†
    =
    fun yz =>L[K] 
      -- (fun x =>L[K] g x)† yz.1 + (fun x =>L[K] f x)† yz.2 :=
      let x₁ := (fun x =>L[K] g x)† yz.1
      let x₂ := (fun x =>L[K] f x)† yz.2
      x₁ + x₂ := 
by sorry




-- set_option trace.Meta.Tactic.ftrans.step true in
set_option trace.Meta.flattenLet.step true in
example
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : X → Z) (hf : IsContinuousLinearMap K f)
  : ((fun x =>L[K] (g x, f x)) : X →L[K] Y×₂Z)†
    =
    fun yz =>L[K]
      (fun x =>L[K] g x)† yz.1 + (fun x =>L[K] f x)† yz.2 :=
by ftrans only

