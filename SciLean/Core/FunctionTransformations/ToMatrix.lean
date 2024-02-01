import SciLean.Core.Objects.FinVec
import SciLean.Core.FunctionPropositions.IsLinearMap

import SciLean.Tactic.FTrans.Basic
import SciLean.Tactic.FProp.Basic

namespace SciLean

-- this ordering does not seem to work
-- variable
--   {K : Type _} {IX IX IZ : Type} {X Y Z : Type _}
--   [IsROrC K]
--   [EnumType IX] [FinVec IX K X]
--   [EnumType IY] [FinVec IY K Y]
--   [EnumType IZ] [FinVec IZ K Z]


-- having index sets unverse polymorphic trips up simplifier
variable
  {K : Type _} [IsROrC K]
  {IX : Type} [EnumType IX] {X : Type _} [FinVec IX K X]
  {IY : Type} [EnumType IY] {Y : Type _} [FinVec IY K Y]
  {IZ : Type} [EnumType IZ] {Z : Type _} [FinVec IZ K Z]

def mulMat (A : IZ → IY → K) (B : IY → IX → K) (i : IZ) (j : IX) : K := ∑ k, A i k * B k j
def mulVec (A : IY → IX → K) (x : IX → K) (i : IY) : K := ∑ j, A i j * x j

variable (K)
def toMatrix (f : X → Y) (i : IY) (j : IX) : K := ℼ i (f (ⅇ j))

namespace toMatrix
--------------------------------------------------------------------------------

variable (X)
theorem id_rule
  : toMatrix K (fun x : X => x)
    =
    fun i j => if i = j then 1 else 0 :=
by
  simp[toMatrix]


variable (Y)
theorem const_zero_rule
  : toMatrix K (fun x : X => (0 : Y))
    =
    fun i j => 0 :=
by
  simp[toMatrix]
variable {Y}


theorem proj_rule [EnumType ι] (i : ι)
  : toMatrix K (fun f : ι → X => f i)
    =
    fun ix (j,jx) => (if j = i ∧ jx = ix then 1 else 0) :=
by
  funext ix (j,jx)
  simp[toMatrix,Basis.basis,Basis.proj]
  sorry_proof


theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : IsLinearMap K f) (hg : IsLinearMap K g)
  : toMatrix K (fun x => f (g x))
    =
    mulMat (toMatrix K f) (toMatrix K g) :=
by
  simp[toMatrix,mulMat]
  funext i j
  symm
  calc ∑ k, ℼ i (f ⅇ k) * ℼ k (g ⅇ j)
    _ = ℼ i (f (∑ k, ℼ k (g ⅇ j) • ⅇ k)) := by sorry_proof
    _ = ℼ i (f (g ⅇ j)) := by sorry_proof -- simp[FinVec.is_basis]


-- Register `toMatrix` as function transformation ------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq

def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `toMatrix_discharger (fun _ => return s!"discharge {← ppExpr e}") do
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
  ftransName := ``toMatrix

  getFTransFun? e :=
    if e.isAppOf ``toMatrix then

      if let .some f := e.getArg? 10 then
        some f
      else
        none
    else
      none

  replaceFTransFun e f :=
    if e.isAppOf ``toMatrix then
      e.setArg 10 f
    else
      e

  idRule  e X := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``id_rule #[K, X], origin := .decl ``id_rule, rfl := false} ]
      discharger e

  constRule e X y := do
    let .some K := e.getArg? 0 | return none
    let Y ← inferType y
    tryTheorems
      #[ { proof := ← mkAppM ``const_zero_rule #[K, X, Y], origin := .decl ``const_zero_rule, rfl := false} ]
      discharger e

  projRule e X i := do
    let .some K := e.getArg? 0 | return none
    let X' := X.bindingBody!
    if X'.hasLooseBVars then
      trace[Meta.Tactic.ftrans.step] "can't handle this bvar app case, projection rule for dependent function of type {← ppExpr X} is not supported"
      return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[K, X', i], origin := .decl ``proj_rule, rfl := false} ]
      discharger e

  compRule e f g := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``comp_rule #[K, f, g], origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do return none

  piRule  e f := do return none

  discharger := discharger


-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``toMatrix, ftransExt))


end SciLean.toMatrix



open SciLean

variable
  {K : Type _} [IsROrC K]
  {IX : Type} [EnumType IX] {X : Type _} [FinVec IX K X]
  {IY : Type} [EnumType IY] {Y : Type _} [FinVec IY K Y]
  {IZ : Type} [EnumType IZ] {Z : Type _} [FinVec IZ K Z]
  {IW : Type} [EnumType IW] {W : Type _} [FinVec IW K W]


@[ftrans]
theorem Prod.mk.arg_fstsnd.toMatrix_rule
  (g : X → Y) (hg : IsLinearMap K g)
  (f : X → Z) (hf : IsLinearMap K f)
  : toMatrix K (fun x => (g x, f x))
    =
    fun i jx =>
      match i with
      | .inl iy => toMatrix K g iy jx
      | .inr iz => toMatrix K f iz jx :=
    -- this would be nice notation inspired by dex-lang
    -- fun (iy|iz) jx => (toMatrix K g iy jx | toMatrix K f iz jx) :=
by
  simp[toMatrix,Basis.basis,Basis.proj]
  rfl


@[ftrans]
theorem Prod.fst.arg_self.toMatrix_rule
  (f : X → Y×Z) (hf : IsLinearMap K f)
  : toMatrix K (fun x => (f x).1)
    =
    fun iy ix => toMatrix K f (.inl iy) ix :=
by
  simp[toMatrix,Basis.basis,Basis.proj]


@[ftrans]
theorem Prod.snd.arg_self.toMatrix_rule
  (f : X → Y×Z) (hf : IsLinearMap K f)
  : toMatrix K (fun x => (f x).2)
    =
    fun iz ix => toMatrix K f (.inr iz) ix :=
by
  simp[toMatrix,Basis.basis,Basis.proj]



-- id.arg_a.toMatrix_rule
-- Function.comp.arg_f.toMatrix_rule
-- Function.comp.arg_g.toMatrix_rule
-- Function.comp.arg_x.toMatrix_rule

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.toMatrix_rule
  (f g : X → Y) (hf : IsLinearMap K f) (hg : IsLinearMap K g)
  : (toMatrix K fun x => f x + g x)
    =
    fun i j => toMatrix K f i j + toMatrix K g i j :=
by
  simp[toMatrix, (Basis.proj.arg_x.IsLinearMap_rule _).map_add]


@[ftrans]
theorem HSub.hSub.arg_a0a1.toMatrix_rule
  (f g : X → Y) (hf : IsLinearMap K f) (hg : IsLinearMap K g)
  : (toMatrix K fun x => f x - g x)
    =
    fun i j => toMatrix K f i j - toMatrix K g i j :=
by
  simp[toMatrix, (Basis.proj.arg_x.IsLinearMap_rule _).map_sub]


@[ftrans]
theorem Neg.neg.arg_a0.toMatrix_rule
  (f : X → Y) (hf : IsLinearMap K f)
  : (toMatrix K fun x => - f x)
    =
    fun i j => - toMatrix K f i j :=
by
  simp[toMatrix, (Basis.proj.arg_x.IsLinearMap_rule _).map_neg]


@[ftrans]
theorem HSMul.hSMul.arg_a1.toMatrix_rule
  (k : K) (f : X → Y) (hf : IsLinearMap K f)
  : (toMatrix K fun x => k • f x)
    =
    fun i j => k * toMatrix K f i j :=
by
  simp[toMatrix, (Basis.proj.arg_x.IsLinearMap_rule _).map_smul]


@[ftrans]
theorem HSMul.hSMul.arg_a0.toMatrix_rule
  (f : X → K) (y : Y) (hf : IsLinearMap K f)
  : (toMatrix K fun x => f x • y)
    =
    fun i j => f (ⅇ j) * ℼ i y :=
by
  simp[toMatrix, (Basis.proj.arg_x.IsLinearMap_rule _).map_smul]


@[ftrans]
theorem SciLean.EnumType.sum.arg_f.toMatrix_rule [EnumType ι]
  (f : X → ι → Y) (hf : ∀ i, IsLinearMap K (f · i))
  : toMatrix K (fun x => ∑ i, f x i)
    =
    fun i j => ∑ i', toMatrix K (f · i') i j :=
by
  simp[toMatrix]
  sorry_proof


@[ftrans]
theorem SciLean.mulVec.arg_x_i.toMatrix_rule
  (A : IY → IX → K) (x : W → IX → K) (hx : ∀ ix, IsLinearMap K (x · ix))
  : toMatrix K (fun x' iy => mulVec A (x x') iy)
    =
    fun _ iw => ∑ ix', A iy ix' * x (ⅇ iw) ix' :=
by
  sorry_proof
