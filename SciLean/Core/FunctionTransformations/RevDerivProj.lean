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
theorem revDerivProj_snd_zero (f : X → E) (x : X) (i : I)
  : (revDerivProj K f x).2 i 0 = 0 := 
by
  simp[revDerivProj]
  conv in (StructLike.make _) => 
    equals (0:E) =>
      apply StructLike.ext
      intro i'; simp
      if h : i=i' then subst h; simp else simp[h]
  simp

@[simp, ftrans_simp]
theorem revDerivProjUpdate_fst (f : X → E) (x : X)
  : (revDerivProjUpdate K f x).1 = f x :=
by
  rfl

@[simp, ftrans_simp]
theorem revDerivProjUpdate_snd_zero (f : X → E) (x dx : X) (i : I)
  : (revDerivProjUpdate K f x).2 i 0 dx = dx := 
by
  simp[revDerivProjUpdate]

@[simp, ftrans_simp]
theorem revDerivProjUpdate_snd_zero' (f : X → Y) (x : X) (dy : Y)
  : (revDerivUpdate K f x).2 dy 0 = (revCDeriv K f x).2 dy := 
by
  simp[revDerivUpdate]


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
  rfl 


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
  rfl

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
         ydg'.2 dxy.2 dxy.1) := 
by
  unfold revDerivProj
  ftrans
  rfl

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
         ydg'.2 dxy.2 dxy.1) := 
by
  unfold revDerivProjUpdate
  simp [revDerivProj.let_rule _ _ _ hf hg,add_assoc,add_comm,revDerivUpdate]


theorem revDerivProj.pi_rule
  (f :  X → ι → Y) (hf : ∀ i, HasAdjDiff K (f · i))
  : (@revDerivProj K _ _ _ _ Unit (fun _ => ι→Y) (instStrucLikeDefault) _ _ fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let ydf := revDerivProjUpdate K f x
      (fun i => ydf.1 i, 
       fun _ df => Id.run do
         let mut dx : X := 0
         for i in fullRange ι do
           dx := ydf.2 (i,()) (df i) dx
         dx) := 
by
  sorry_proof


theorem revDerivProjUpdate.pi_rule
  (f :  X → ι → Y) (hf : ∀ i, HasAdjDiff K (f · i))
  : (@revDerivProjUpdate K _ _ _ _ Unit (fun _ => ι→Y) (StructLike.instStructLikeDefault) _ _ fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let ydf := revDerivProjUpdate K f x
      (fun i => ydf.1 i, 
       fun _ df dx => Id.run do
         let mut dx : X := dx
         for i in fullRange ι do
           dx := ydf.2 (i,()) (df i) dx
         dx) := 
by
  sorry_proof



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
    IO.println "hih"
    let proof ← mkAppOptM ``id_rule #[K,none, X,none,none,none,none,none]
    IO.println s!"proof of {← inferType proof}"
    tryTheorems
      #[ { proof := ← mkAppOptM ``id_rule #[K,none, X,none,none,none,none,none], origin := .decl ``id_rule, rfl := false} ]
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
    IO.println "hih"
    let proof ← mkAppOptM ``id_rule #[K,none, X,none,none,none,none,none,none,none]
    IO.println s!"proof of {← inferType proof}"
    tryTheorems
      #[ { proof := ← mkAppOptM ``id_rule #[K,none, X,none,none,none,none,none,none,none], origin := .decl ``id_rule, rfl := false} ]
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
  {X Xi : Type _} {XI : Xi → Type _} [StructLike X Xi XI] [EnumType Xi]
  {Y Yi : Type _} {YI : Yi → Type _} [StructLike Y Yi YI] [EnumType Yi]
  {Z Zi : Type _} {ZI : Zi → Type _} [StructLike Z Zi ZI] [EnumType Zi]
  [SemiInnerProductSpace K X] [∀ i, SemiInnerProductSpace K (XI i)] [SemiInnerProductSpaceStruct K X Xi XI]
  [SemiInnerProductSpace K Y] [∀ i, SemiInnerProductSpace K (YI i)] [SemiInnerProductSpaceStruct K Y Yi YI]
  [SemiInnerProductSpace K Z] [∀ i, SemiInnerProductSpace K (ZI i)] [SemiInnerProductSpaceStruct K Z Zi ZI]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [EnumType ι]


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
  induction i <;> simp


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

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


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.revDerivProj_rule
  (f : W → X×Y) (hf : HasAdjDiff K f)
  : revDerivProj K (fun x => (f x).2)
    =
    fun w => 
      let xydf := revDerivProj K f w
      (xydf.1.2,
       fun i dxy => xydf.2 (.inr i) dxy) := 
by
  unfold revDerivProj
  funext x; ftrans; simp
  funext e dxy
  simp[StructLike.make]
  apply congr_arg
  congr; funext i; congr; funext h; subst h; rfl


@[ftrans]
theorem Prod.snd.arg_self.revDerivProjUpdate_rule
  (f : W → X×Y) (hf : HasAdjDiff K f)
  : revDerivProjUpdate K (fun x => (f x).2)
    =
    fun w => 
      let xydf := revDerivProjUpdate K f w
      (xydf.1.2,
       fun i dxy dw => xydf.2 (.inr i) dxy dw) := 
by
  unfold revDerivProjUpdate
  funext x; ftrans; simp



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revDerivProj_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProj K fun x => f x + g x)
    =
    fun x => 
      let ydf := revDerivProj K f x
      let ydg := revDerivProjUpdate K g x
      (ydf.1 + ydg.1, 
       fun i dy => (ydg.2 i dy (ydf.2 i dy))) := 
by 
  unfold revDerivProjUpdate; unfold revDerivProj
  ftrans


@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revDerivProjUpdate_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProjUpdate K fun x => f x + g x)
    =
    fun x => 
      let ydf := revDerivProjUpdate K f x
      let ydg := revDerivProjUpdate K g x
      (ydf.1 + ydg.1, fun i dy dx => ydg.2 i dy (ydf.2 i dy dx)) := 
by 
  unfold revDerivProjUpdate
  ftrans; simp[revDerivProjUpdate, add_assoc]


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.revDerivProj_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProj K fun x => f x - g x)
    =
    fun x => 
      let ydf := revDerivProj K f x
      let ydg := revDerivProjUpdate K g x
      (ydf.1 - ydg.1, 
       fun i dy => (ydg.2 i (-dy) (ydf.2 i dy))) := 
by 
  unfold revDerivProjUpdate; unfold revDerivProj
  ftrans; simp; sorry_proof -- pulling the minus out is just tedious ...


@[ftrans]
theorem HSub.hSub.arg_a0a1.revDerivProjUpdate_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProjUpdate K fun x => f x - g x)
    =
    fun x => 
      let ydf := revDerivProjUpdate K f x
      let ydg := revDerivProjUpdate K g x
      (ydf.1 - ydg.1, fun i dy dx => ydg.2 i (-dy) (ydf.2 i dy dx)) := 
by 
  unfold revDerivProjUpdate
  ftrans; simp[revDerivProjUpdate, add_assoc]


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.revDerivProj_rule
  (f : X → Y)
  : (revDerivProj K fun x => - f x)
    =
    fun x => 
      let ydf := revDerivProj K f x
      (-ydf.1, fun i dy => ydf.2 i (-dy)) :=
by 
  unfold revDerivProj; ftrans; simp; sorry_proof -- pulling the minus out is just tedious ...

@[ftrans]
theorem Neg.neg.arg_a0.revDerivProjUpdate_rule
  (f : X → Y)
  : (revDerivProjUpdate K fun x => - f x)
    =
    fun x => 
      let ydf := revDerivProjUpdate K f x
      (-ydf.1, fun i dy dx => ydf.2 i (-dy) dx) :=
by 
  unfold revDerivProjUpdate; ftrans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------
open ComplexConjugate

@[ftrans]
theorem HMul.hMul.arg_a0a1.revDerivProj_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProj K fun x => f x * g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revCDeriv K g x
      (ydf.1 * zdg.1, fun _ dy => ydf.2 ((conj zdg.1)*dy) (zdg.2 (conj ydf.1* dy))) :=
by 
  unfold revDerivProj
  ftrans; funext x; simp[revDerivUpdate,StructLike.make]; funext _ dy
  sorry_proof -- just need to pull those multiplcations out


@[ftrans]
theorem HMul.hMul.arg_a0a1.revDerivProjUpdate_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProjUpdate K fun x => f x * g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 * zdg.1, fun _ dy dx => ydf.2 ((conj zdg.1)*dy) (zdg.2 (conj ydf.1* dy) dx)) :=
by 
  unfold revDerivProjUpdate
  ftrans; simp[revDerivUpdate,add_assoc]
  

-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revDerivProj_rule
  {Y Yi : Type _} {YI : Yi → Type _} [StructLike Y Yi YI] [EnumType Yi]
  [SemiHilbert K Y] [∀ i, SemiHilbert K (YI i)] [SemiInnerProductSpaceStruct K Y Yi YI]
  (f : X → K) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProj K fun x => f x • g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivProj K g x
      (ydf.1 • zdg.1, fun i (dy : YI i) => ydf.2 (inner (StructLike.proj zdg.1 i) dy) (zdg.2 i (conj ydf.1•dy))) :=
by 
  unfold revDerivProj
  ftrans; funext x; simp; funext i dy
  simp[revDerivUpdate]
  sorry_proof -- this requires some lemma about inner product with StruckLike types

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revDerivProjUpdate_rule
  {Y Yi : Type} {YI : Yi → Type} [StructLike Y Yi YI] [EnumType Yi]
  [SemiHilbert K Y] [∀ i, SemiHilbert K (YI i)] [SemiInnerProductSpaceStruct K Y Yi YI]
  (f : X → K) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProjUpdate K fun x => f x • g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivProjUpdate K g x
      (ydf.1 • zdg.1, fun i (dy : YI i) dx => ydf.2 (inner (StructLike.proj zdg.1 i) dy) (zdg.2 i (conj ydf.1•dy) dx)) :=
by 
  unfold revDerivProjUpdate
  ftrans; simp[revDerivUpdate]; funext x; simp; funext i dy dx
  simp[add_assoc]



-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------


@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revDerivProj_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0)
  : (revDerivProj K fun x => f x / g x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 / zdg.1, 
       -- fun dy k dx => (1 / (conj zdg.1)^2) • (conj zdg.1 • ydf.2 dy - conj ydf.1 • zdg.2 dy)) :=
       fun _ dy =>  
         let factor := ((conj zdg.1)^2)⁻¹
         let dy := factor * dy
         zdg.2 (-conj ydf.1 * dy) (ydf.2 (conj zdg.1 * dy))) :=
by 
  sorry_proof

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revDerivProjUpdate_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0)
  : (revDerivProjUpdate K fun x => f x / g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 / zdg.1, 
       fun _ dy dx =>  
         let factor := ((conj zdg.1)^2)⁻¹
         let dy := factor * dy
         zdg.2 (-conj ydf.1 * dy) (ydf.2 (conj zdg.1 * dy) dx)) :=
by 
  sorry_proof


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HPow.hPow.arg_a0.revDerivProj_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f) 
  : revDerivProj K (fun x => f x ^ n)
    =
    fun x => 
      let ydf := revCDeriv K f x
      (ydf.1 ^ n, 
       fun _ dy => ydf.2 (n * (conj ydf.1 ^ (n-1)) * dy)) :=
by 
  sorry_proof


@[ftrans]
def HPow.hPow.arg_a0.revDerivProjUpdate_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f) 
  : revDerivProjUpdate K (fun x => f x ^ n)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      (ydf.1 ^ n, 
       fun _ dy dx => ydf.2 (n * (conj ydf.1 ^ (n-1)) * dy) dx) :=
by 
  unfold revDerivProjUpdate; 
  ftrans; simp[revDerivUpdate]


-- EnumType.sum ----------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem SciLean.EnumType.sum.arg_f.revDerivProj_rule {ι : Type _} [EnumType ι]
  (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDerivProj K (fun x => ∑ i, f x i)
    =
    fun x => 
      let ydf := revDerivProjUpdate K f x
      (∑ i, ydf.1 i, 
       fun i dy => Id.run do
         let mut dx : X := 0
         for j in fullRange ι do
           dx := ydf.2 (j,i) dy dx
         dx) :=
by
  sorry_proof


@[ftrans]
theorem SciLean.EnumType.sum.arg_f.revDerivProjUpdate_rule {ι : Type _} [EnumType ι]
  (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDerivProjUpdate K (fun x => ∑ i, f x i)
    =
    fun x => 
      let ydf := revDerivProjUpdate K f x
      (∑ i, ydf.1 i, 
       fun i dy dx => Id.run do
         let mut dx : X := dx
         for j in fullRange ι do
           dx := ydf.2 (j,i) dy dx
         dx) :=
by
  sorry_proof


--------------------------------------------------------------------------------

section InnerProductSpace

variable 
  {R : Type _} [RealScalar R]
  -- {K : Type _} [Scalar R K]
  {X : Type _} [SemiInnerProductSpace R X]
  {X Xi : Type _} {XI : Xi → Type _} [StructLike X Xi XI] [EnumType Xi]
  {Y Yi : Type _} {YI : Yi → Type _} [StructLike Y Yi YI] [EnumType Yi]
  [SemiHilbert R Y] [∀ i, SemiHilbert R (YI i)] [SemiInnerProductSpaceStruct R Y Yi YI]
  [SemiInnerProductSpace R X] [∀ i, SemiInnerProductSpace R (XI i)] [SemiInnerProductSpaceStruct R X Xi XI]

  -- [SemiInnerProductSpace K Y] [∀ i, SemiInnerProductSpace K (YI i)] [SemiInnerProductSpaceStruct K Y Yi YI]
  -- [SemiInnerProductSpace K Z] [∀ i, SemiInnerProductSpace K (ZI i)] [SemiInnerProductSpaceStruct K Z Zi ZI]
  -- {W : Type _} [SemiInnerProductSpace K W]


-- Inner -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate

@[ftrans]
theorem Inner.inner.arg_a0a1.revDerivProj_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDerivProj R fun x => ⟪f x, g x⟫[R])
    =
    fun x => 
      let y₁df := revCDeriv R f x
      let y₂dg := revDerivUpdate R g x
      let dx₁ := y₁df.2 y₂dg.1
      let dx₂ := y₂dg.2 y₁df.1
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun i dr => 
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (conj dr • y₂dg.1))) := 
by 
  sorry_proof

@[ftrans]
theorem Inner.inner.arg_a0a1.revDerivProjUpdate_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDerivProjUpdate R fun x => ⟪f x, g x⟫[R])
    =
    fun x => 
      let y₁df := revDerivUpdate R f x
      let y₂dg := revDerivUpdate R g x
      let dx₁ := y₁df.2 y₂dg.1
      let dx₂ := y₂dg.2 y₁df.1
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun i dr dx => 
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (conj dr • y₂dg.1) dx) ) := 
by       
  unfold revDerivProjUpdate
  ftrans; simp[add_assoc,revDerivUpdate]


@[ftrans]
theorem SciLean.Norm2.norm2.arg_a0.revDerivProj_rule
  (f : X → Y) (hf : HasAdjDiff R f)
  : (revDerivProj R fun x => ‖f x‖₂²[R])
    =
    fun x => 
      let ydf := revCDeriv R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr => 
          ydf.2 (((2:R)*dr)•ydf.1)) :=
by 
  sorry_proof

@[ftrans]
theorem SciLean.Norm2.norm2.arg_a0.revDerivProjUpdate_rule
  (f : X → Y) (hf : HasAdjDiff R f)
  : (revDerivProjUpdate R fun x => ‖f x‖₂²[R])
    =
    fun x => 
      let ydf := revDerivUpdate R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr dx => 
          ydf.2 (((2:R)*dr)•ydf.1) dx) :=
by 
  unfold revDerivProjUpdate
  ftrans; simp[revDerivUpdate, add_assoc]


@[ftrans]
theorem SciLean.norm₂.arg_x.revDerivProj_rule_at
  (f : X → Y) (x : X)
  (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDerivProj R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revCDeriv R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr => 
       ydf.2 ((ynorm⁻¹ * dr)•ydf.1)):=
by 
  sorry_proof


@[ftrans]
theorem SciLean.norm₂.arg_x.revDerivProjUpdate_rule_at
  (f : X → Y) (x : X)
  (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDerivProjUpdate R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDerivUpdate R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr dx => 
       ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
by 
  unfold revDerivProjUpdate
  ftrans; simp[revDerivUpdate, add_assoc]

end InnerProductSpace



#exit
section Test

variable {K : Type _} [RealScalar K]

set_option trace.Meta.Tactic.simp.discharge true in
#check 
  (revDerivProj K fun x : K×K => x.1 + x.2)
  rewrite_by ftrans only; simp[StructLike.modify,StructLike.make]


set_option trace.Meta.Tactic.simp.discharge true in
#check 
  (revDerivProj K fun x : K×K => x.1*x.2 + x.2)
  rewrite_by ftrans only; simp[StructLike.modify,StructLike.make]


set_option trace.Meta.Tactic.simp.rewrite true in
#check 
  (revDerivProj K fun x : K×K => x.1*x.2)
  rewrite_by
    ftrans only 
    simp only[StructLike.modify,StructLike.make,dite_eq_ite,eq_self,ite_true,dite_false]

#exit

set_option trace.Meta.Tactic.simp.rewrite true in
#check 
  (revDerivProj K fun x : K×K×K×K => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)
  rewrite_by 
    ftrans only 
    simp only[StructLike.modify,StructLike.make,dite_eq_ite,eq_self,ite_true,dite_false]


set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.fprop.discharge true in
#check 
  (revCDeriv K fun x : K×K×K×K => x.1^(2:ℕ) + x.2.1^2 + x.2.2.1^2 + x.2.2.2^2)
  rewrite_by ftrans only; simp


set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.fprop.discharge true in
#check 
  (revCDeriv K fun x : K×K => x.2^2 + x.1^2)
  rewrite_by ftrans only; simp





