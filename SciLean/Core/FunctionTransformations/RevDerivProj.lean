import SciLean.Core.FunctionTransformations.RevCDeriv
import SciLean.Core.FunctionTransformations.RevDerivUpdate
import SciLean.Data.StructLike

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [EnumType ι]
  {E I : Type _} {EI : I → Type _} 
  [StructLike E I EI] [EnumType I]
  [SemiInnerProductSpace K E] [∀ i, SemiInnerProductSpace K (EI i)]
  [SemiInnerProductSpaceStruct K E I EI]
  {F J : Type _} {FJ : J → Type _} 
  [StructLike F J FJ] [EnumType J]
  [SemiInnerProductSpace K F] [∀ j, SemiInnerProductSpace K (FJ j)]
  [SemiInnerProductSpaceStruct K F J FJ]

noncomputable
def revDerivProj
  (f : X → E) (x : X) : E×((i : I)→EI i→X) :=
  let ydf' := revCDeriv K f x
  (ydf'.1, fun i de => 
    have := Classical.propDecidable
    ydf'.2 (StructLike.make fun i' => if h:i=i' then h▸de else 0))

noncomputable
def revDerivProjUpdate
  (f : X → E) (x : X) : E×((i : I)→EI i→X→X) :=
  let ydf' := revDerivProj K f x
  (ydf'.1, fun i de dx => dx + ydf'.2 i de)



@[simp, ftrans_simp]
theorem revDerivProj_fst (f : X → E) (x : X)
  : (revDerivProj K f x).1 = f x :=
by
  rfl

@[simp, ftrans_simp]
theorem revDerivProjUpdate_fst (f : X → E) (x : X)
  : (revDerivProjUpdate K f x).1 = f x :=
by
  rfl


--------------------------------------------------------------------------------


variable (E)
theorem revDerivProj.id_rule 
  : revDerivProj K (fun x : E => x)
    =
    fun x => 
      (x,
       fun i de => 
         have := Classical.propDecidable
         StructLike.make fun i' => if h : i=i' then h▸de else 0):= 
by
  simp[revDerivProj]
  ftrans


theorem revDerivProjUpdate.id_rule 
  : revDerivProjUpdate K (fun x : E => x)
    =
    fun x => 
      (x,
       fun i de dx => 
         StructLike.modify i (fun ei => ei + de) dx) := 
by
  funext x
  simp[revDerivProjUpdate, revDerivProj.id_rule]
  funext i de dx
  apply StructLike.ext
  intro i'
  if h : i=i' then
    subst h; simp
  else
    simp[StructLike.proj_modify' _ _ _ _ h, h]

variable {E}


variable (Y)
theorem revDerivProj.const_rule (x : E)
  : revDerivProj K (fun _ : Y => x)
    =
    fun _ => 
      (x,
       fun i (de : EI i) => 0) := 
by
  simp[revDerivProj]
  ftrans

theorem revDerivProjUpdate.const_rule (x : E)
  : revDerivProjUpdate K (fun _ : Y => x)
    =
    fun _ => 
      (x,
       fun i de dx => dx) := 
by
  simp[revDerivProjUpdate,revDerivProj.const_rule]

variable {Y}


theorem revDerivProj.proj_rule [DecidableEq I] (i : ι)
  : revDerivProj K (fun (f : ι → E) => f i)
    = 
    fun f => 
      (f i, fun j dxj i' => 
        if i=i' then
          StructLike.make fun j' =>
            if h : j=j' then
              (h▸dxj)
            else
              0
        else 
          0) := 
by
  simp[revDerivProj]
  ftrans
  funext x; simp
  funext j dxj i'
  apply StructLike.ext
  intro j'
  if h:i=i' then
    subst h; simp
    if h:j=j' then
      subst h; simp
    else
      simp[h]
  else
    simp[h]



theorem revDerivProjUpdate.proj_rule [DecidableEq I] (i : ι)
  : revDerivProjUpdate K (fun (f : ι → E) => f i)
    = 
    fun f => 
      (f i, fun j dxj df i' =>
        if i=i' then
          StructLike.modify j (fun xj => xj + dxj) (df i')
        else 
          df i') := 
by
  funext x;
  simp[revDerivProjUpdate, revDerivProj.proj_rule]
  funext j dxj f i'
  apply StructLike.ext
  intro j'
  if h :i=i' then
    subst h; simp
    if h:j=j' then
      subst h; simp
    else
      simp[h]
  else
    simp[h]


theorem revDerivProj.comp_rule
  (f : Y → E) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDerivProj K (fun x => f (g x))
    =
    fun x => 
      let ydg' := revCDeriv K g x
      let zdf' := revDerivProj K f ydg'.1
      (zdf'.1,
       fun i de => 
         ydg'.2 (zdf'.2 i de)) := 
by
  simp[revDerivProj]
  ftrans


theorem revDerivProjUpdate.comp_rule
  (f : Y → E) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDerivProjUpdate K (fun x => f (g x))
    =
    fun x => 
      let ydg' := revDerivUpdate K g x
      let zdf' := revDerivProj K f ydg'.1
      (zdf'.1,
       fun i de dx => 
         ydg'.2 (zdf'.2 i de) dx) := 
by
  funext x
  simp[revDerivProjUpdate,revDerivProj.comp_rule _ _ _ hf hg]
  constructor
  . sorry
  . 
    funext i de dx
    if h :i=i' then
      subst h; simp
    else
      simp[h]


theorem revDerivProj.let_rule
  (f : X → Y → E) (g : X → Y)
  (hf : HasAdjDiff K (fun (x,y) => f x y)) (hg : HasAdjDiff K g)
  : revDerivProj K (fun x => let y := g x; f x y)
    =
    fun x => 
      let ydg' := revDerivUpdate K g x
      let zdf' := revDerivProj K (fun (x,y) => f x y) (x,ydg'.1)
      (zdf'.1,
       fun i dei => 
         let dxy := zdf'.2 i dei
         ydg'.2 dxy.2 1 dxy.1) := 
by
  sorry_proof


theorem revDerivProjUpdate.let_rule
  (f : X → Y → E) (g : X → Y)
  (hf : HasAdjDiff K (fun (x,y) => f x y)) (hg : HasAdjDiff K g)
  : revDerivProjUpdate K (fun x => let y := g x; f x y)
    =
    fun x => 
      let ydg' := revDerivUpdate K g x
      let zdf' := revDerivProjUpdate K (fun (x,y) => f x y) (x,ydg'.1)
      (zdf'.1,
       fun i dei dx => 
         let dxy := zdf'.2 i dei (dx,0)
         ydg'.2 dxy.2 1 dxy.1) := 
by
  sorry_proof


theorem revDerivProj.pi_rule
  (f :  X → ι → E) (hf : ∀ i, HasAdjDiff K (f · i))
  : (revDerivProj K fun (x : X) (i : ι) => f x i)
    =
    revDerivProj K fun x => f x := by rfl


theorem revDerivProjUpdate.pi_rule
  (f :  X → ι → E) (hf : ∀ i, HasAdjDiff K (f · i))
  : (revDerivProjUpdate K fun (x : X) (i : ι) => f x i)
    =
    revDerivProjUpdate K fun x => f x := by rfl



--------------------------------------------------------------------------------

-- Register `revDerivProj` as function transformation --------------------------
--------------------------------------------------------------------------------

namespace revDerivProj

open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `revDerivProj_discharger (fun _ => return s!"discharge {← ppExpr e}") do
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


open Lean Meta FTrans in
def ftransExt : FTransExt where
  ftransName := ``revDerivProj

  getFTransFun? e := 
    if e.isAppOf ``revDerivProj then

      if let .some f := e.getArg? 10 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``revDerivProj then
      e.setArg 6 f
    else          
      e

  idRule  e X := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``id_rule #[K, X], origin := .decl ``id_rule, rfl := false} ]
      discharger e

  constRule e X y := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[K, X, y], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[K, X, i], origin := .decl ``proj_rule, rfl := false} ]
      discharger e

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

  piRule  e f := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[K, f], origin := .decl ``pi_rule, rfl := false} ]
      discharger e

  discharger := discharger


-- register revDerivProj
open Lean in
#eval show CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revDerivProj, ftransExt))

end revDerivProj


namespace revDerivProjUpdate

open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `revDerivProjUpdate_discharger (fun _ => return s!"discharge {← ppExpr e}") do
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


open Lean Meta FTrans in
def ftransExt : FTransExt where
  ftransName := ``revDerivProjUpdate

  getFTransFun? e := 
    if e.isAppOf ``revDerivProjUpdate then

      if let .some f := e.getArg? 10 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``revDerivProjUpdate then
      e.setArg 6 f
    else          
      e

  idRule  e X := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``id_rule #[K, X], origin := .decl ``id_rule, rfl := false} ]
      discharger e

  constRule e X y := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[K, X, y], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[K, X, i], origin := .decl ``proj_rule, rfl := false} ]
      discharger e

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

  piRule  e f := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[K, f], origin := .decl ``pi_rule, rfl := false} ]
      discharger e

  discharger := discharger


-- register revDerivProjUpdate
open Lean in
#eval show CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revDerivProjUpdate, ftransExt))

end revDerivProjUpdate



--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
end SciLean
open SciLean

variable 
  {K : Type _} [IsROrC K]
  {X Xi : Type} {XI : Xi → Type} [StructLike X Xi XI] [DecidableEq Xi]
  {Y Yi : Type} {YI : Yi → Type} [StructLike Y Yi YI] [DecidableEq Yi]
  {Z Zi : Type} {ZI : Zi → Type} [StructLike Z Zi ZI] [DecidableEq Zi]
  [SemiInnerProductSpace K X] [∀ i, SemiInnerProductSpace K (XI i)]
  [SemiInnerProductSpace K Y] [∀ i, SemiInnerProductSpace K (YI i)]
  [SemiInnerProductSpace K Z] [∀ i, SemiInnerProductSpace K (ZI i)]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [EnumType ι]

@[simp]
theorem StruckLike.make_zero
  {X I : Type}  {XI : I → Type} [StructLike X I XI] 
  [Zero X] [∀ i, Zero (XI i)]
  : StructLike.make (E:=X) (fun _ => 0)
    =
    0 :=
by
  sorry

@[simp]
theorem revCDeriv_snd_zero
  (f : X → Y) (x : X)
  : (revCDeriv K f x).2 0 = 0 := sorry

@[simp]
theorem revDerivUpdate_snd_zero 
  (f : X → Y) (x : X)
  : (revDerivUpdate K f x).2 0 k dy = dy := sorry


-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.revDerivProj_rule
  (g : X → Y) (f : X → Z)
  (hg : HasAdjDiff K g) (hf : HasAdjDiff K f)
  : revDerivProj K (fun x => (g x, f x))
    =
    fun x => 
      let ydg := revDerivProj K g x
      let zdf := revDerivProj K f x
      ((ydg.1,zdf.1), 
       fun i dyz => 
         match i with
         | .inl j => ydg.2 j dyz
         | .inr j => zdf.2 j dyz) := 
by
  unfold revDerivProj
  funext x; ftrans; simp
  funext i dyz
  induction i <;>
    { simp[StructLike.make]
      apply congr_arg
      congr; funext i; congr; funext h
      subst h; rfl
    }

@[ftrans]
theorem Prod.mk.arg_fstsnd.revDerivProjUpdate_rule
  (g : X → Y) (f : X → Z)
  (hg : HasAdjDiff K g) (hf : HasAdjDiff K f)
  : revDerivProjUpdate K (fun x => (g x, f x))
    =
    fun x => 
      let ydg := revDerivProjUpdate K g x
      let zdf := revDerivProjUpdate K f x
      ((ydg.1,zdf.1), 
       fun i dyz dx => 
         match i with
         | .inl j => ydg.2 j dyz dx
         | .inr j => zdf.2 j dyz dx) := 
by
  unfold revDerivProjUpdate
  funext x; ftrans; simp
  funext i de dx
  induction i <;>
  { simp[StructLike.make]
    sorry_proof
  }


------------------------

@[ftrans]
theorem Prod.fst.arg_self.revDerivProj_rule
  (f : W → X×Y) (hf : HasAdjDiff K f)
  : revDerivProj K (fun x => (f x).1)
    =
    fun w => 
      let xydf := revDerivProj K f w
      (xydf.1.1,
       fun i dxy => xydf.2 (.inl i) dxy) := 
by
  unfold revDerivProj
  funext x; ftrans; simp
  funext e dxy
  simp[StructLike.make]
  apply congr_arg
  congr; funext i; congr; funext h; subst h; rfl


@[ftrans]
theorem Prod.fst.arg_self.revDerivProjUpdate_rule
  (f : W → X×Y) (hf : HasAdjDiff K f)
  : revDerivProjUpdate K (fun x => (f x).1)
    =
    fun w => 
      let xydf := revDerivProjUpdate K f w
      (xydf.1.1,
       fun i dxy dw => xydf.2 (.inl i) dxy dw) := 
by
  unfold revDerivProjUpdate
  funext x; ftrans; simp
  funext e dxy dw
  simp[StructLike.make]
  -- apply congr_arg -- this fails for some reason :(
  -- congr; funext i; congr; funext h; subst h; rfl
  sorry_proof




theorem Prod.fst.arg_self.revDeriv_rule 
  (f : W → X×Y) (hf : HasAdjDiff K f)
  : revCDeriv K (fun w => (f w).1)
    =
    fun w => 
      let xydf' := revDerivProj K f w
      (xydf'.1.1, fun dx => xydf'.2 (.inl ()) dx) :=
by
  sorry_proof


theorem Prod.fst.arg_self.revDerivProj_rule
  {X I : Type _} {XI : I → Type _} 
  [StructLike X I XI] [SemiInnerProductSpace K X] [∀ i, SemiInnerProductSpace K (XI i)]
  (f : W → X×Y) (hf : HasAdjDiff K f)
  : revDerivProj K (fun w => (f w).1)
    =
    fun w => 
      let xydf' := revDerivProj K f w
      (xydf'.1.1,
       fun i dx => xydf'.2 (.inl i) dx) :=
by
  sorry_proof
