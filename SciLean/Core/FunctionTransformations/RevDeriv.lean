import SciLean.Core.FunctionPropositions.HasAdjDiffAt
import SciLean.Core.FunctionPropositions.HasAdjDiff

import SciLean.Core.FunctionTransformations.SemiAdjoint

import SciLean.Data.StructType.Algebra

import SciLean.Data.Curry

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K I : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [EnumType ι]
  {κ : Type _} [EnumType κ]
  {E : Type _} {EI : I → Type _} 
  [StructType E I EI] [EnumType I]
  [SemiInnerProductSpace K E] [∀ i, SemiInnerProductSpace K (EI i)]
  [SemiInnerProductSpaceStruct K E I EI]
  {F J : Type _} {FJ : J → Type _} 
  [StructType F J FJ] [EnumType J]
  [SemiInnerProductSpace K F] [∀ j, SemiInnerProductSpace K (FJ j)]
  [SemiInnerProductSpaceStruct K F J FJ]


noncomputable
def revDeriv
  (f : X → Y) (x : X) : Y×(Y→X) :=
  (f x, semiAdjoint K (cderiv K f x))


noncomputable
def revDerivUpdate
  (f : X → Y) (x : X) : Y×(Y→X→X) :=
  let ydf := revDeriv K f x
  (ydf.1, fun dy dx => dx + ydf.2 dy)

noncomputable
def revDerivProj [DecidableEq I]
  (f : X → E) (x : X) : E×((i : I)→EI i→X) :=
  let ydf' := revDeriv K f x
  (ydf'.1, fun i de => 
    ydf'.2 (oneHot i de))

noncomputable
def revDerivProjUpdate [DecidableEq I]
  (f : X → E) (x : X) : E×((i : I)→EI i→X→X) :=
  let ydf' := revDerivProj K I f x
  (ydf'.1, fun i de dx => dx + ydf'.2 i de)

--------------------------------------------------------------------------------
-- simplification rules for individual components ------------------------------
--------------------------------------------------------------------------------

@[simp, ftrans_simp]
theorem revDeriv_fst (f : X → Y) (x : X)
  : (revDeriv K f x).1 = f x :=
by
  rfl

@[simp, ftrans_simp]
theorem revDeriv_snd_zero (f : X → Y) (x : X)
  : (revDeriv K f x).2 0 = 0 := 
by
  simp[revDeriv]

@[simp, ftrans_simp]
theorem revDerivUpdate_fst (f : X → Y) (x : X)
  : (revDerivUpdate K f x).1 = f x :=
by
  rfl

@[simp, ftrans_simp]
theorem revDerivUpdate_snd_zero (f : X → Y) (x dx : X)
  : (revDerivUpdate K f x).2 0 dx = dx := 
by
  simp[revDerivUpdate]

@[simp, ftrans_simp]
theorem revDerivUpdate_snd_zero' (f : X → Y) (x : X) (dy : Y)
  : (revDerivUpdate K f x).2 dy 0 = (revDeriv K f x).2 dy := 
by
  simp[revDerivUpdate]


@[simp, ftrans_simp]
theorem revDerivProj_fst (f : X → E) (x : X)
  : (revDerivProj K (I:=I) f x).1 = f x :=
by
  rfl

@[simp, ftrans_simp]
theorem revDerivProj_snd_zero (f : X → E) (x : X) (i : I)
  : (revDerivProj K I f x).2 i 0 = 0 := 
by
  simp[revDerivProj]

@[simp, ftrans_simp]
theorem revDerivProjUpdate_fst (f : X → E) (x : X)
  : (revDerivProjUpdate K I f x).1 = f x :=
by
  rfl

@[simp, ftrans_simp]
theorem revDerivProjUpdate_snd_zero (f : X → E) (x dx : X) (i : I)
  : (revDerivProjUpdate K I f x).2 i 0 dx = dx := 
by
  simp[revDerivProjUpdate]

@[simp, ftrans_simp]
theorem revDerivProjUpdate_snd_zero' (f : X → Y) (x : X) (dy : Y)
  : (revDerivUpdate K f x).2 dy 0 = (revDeriv K f x).2 dy := 
by
  simp[revDerivUpdate]


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDeriv ------------------------------------------
--------------------------------------------------------------------------------

namespace revDeriv

variable (X)
theorem id_rule 
  : revDeriv K (fun x : X => x) = fun x => (x, fun dx => dx) :=
by
  unfold revDeriv
  funext _; ftrans; ftrans

theorem const_rule (y : Y)
  : revDeriv K (fun _ : X => y) = fun x => (y, fun _ => 0) :=
by
  unfold revDeriv
  funext _; ftrans; ftrans
variable{X}

variable(EI)
variable {I}
theorem proj_rule (i : I)
  : revDeriv K (fun (x : (i:I) → EI i) => x i)
    = 
    fun x => 
      (x i, fun dxi => oneHot i dxi) :=
by
  unfold revDeriv
  funext _; ftrans; ftrans; simp[oneHot]
variable (I)
variable {EI}

theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDeriv K (fun x : X => f (g x))
    = 
    fun x =>
      let ydg := revDeriv K g x
      let zdf := revDeriv K f ydg.1
      (zdf.1,
       fun dz =>
         let dy := zdf.2 dz
         ydg.2 dy)  := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv
  funext _; ftrans; ftrans
  rfl

theorem let_rule 
  (f : X → Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : revDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revDerivUpdate K g x
      let zdf := revDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz => 
         let dxdy := zdf.2 dz
         let dx := ydg.2 dxdy.2 dxdy.1
         dx)  :=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv
  funext _; ftrans; ftrans; rfl

variable {I}
theorem pi_rule
  (f :  X → (i : I) → EI i) (hf : ∀ i, HasAdjDiff K (f · i))
  : (revDeriv K fun (x : X) (i : I) => f x i)
    =
    fun x =>
      let xdf := fun i => revDerivUpdate K (f · i) x
      (fun i => (xdf i).1, 
       fun dy => 
         Function.repeatIdx (fun (i : I) dx => (xdf i).2 (dy i) dx) 0) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  unfold revDeriv
  funext _; ftrans; ftrans
  sorry_proof
variable (I)

end revDeriv


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDerivUpdate ------------------------------------
--------------------------------------------------------------------------------

namespace revDerivUpdate

variable (X)
theorem id_rule
  : revDerivUpdate K (fun x : X => x) = fun x => (x, fun dx' dx => dx + dx') :=
by
  unfold revDerivUpdate
  simp [revDeriv.id_rule]


theorem const_rule (y : Y)
  : revDerivUpdate K (fun _ : X => y) = fun x => (y, fun _ dx => dx) :=
by
  unfold revDerivUpdate
  simp [revDeriv.const_rule]

variable {X}

variable (EI)
variable {I}
theorem proj_rule (i : I)
  : revDerivUpdate K (fun (x : (i:I) → EI i) => x i)
    = 
    fun x => 
      (x i, fun dxi dx => structModify i (fun dxi' => dxi' + dxi) dx) :=
by
  unfold revDerivUpdate
  simp [revDeriv.proj_rule]
variable (I)
variable {EI}

theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDerivUpdate K (fun x : X => f (g x))
    = 
    fun x =>
      let ydg := revDerivUpdate K g x
      let zdf := revDeriv K f ydg.1
      (zdf.1,
       fun dz dx =>
         let dy := zdf.2 dz
         ydg.2 dy dx)  := 
by
  unfold revDerivUpdate
  simp [revDeriv.comp_rule _ _ _ hf hg]

theorem let_rule 
  (f : X → Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : revDerivUpdate K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revDerivUpdate K g x
      let zdf := revDerivUpdate K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz dx => 
         let dxdy := zdf.2 dz (dx, 0)
         let dx := ydg.2 dxdy.2 dxdy.1
         dx)  :=
by
  unfold revDerivUpdate
  simp [revDeriv.let_rule _ _ _ hf hg, revDerivUpdate,add_assoc]

variable {I}
theorem pi_rule
  (f :  X → (i : I) → EI i) (hf : ∀ i, HasAdjDiff K (f · i))
  : (revDerivUpdate K fun (x : X) (i : I) => f x i)
    =
    fun x =>
      let xdf := fun i => revDerivUpdate K (f · i) x
      (fun i => (xdf i).1,
       fun dy dx => 
         Function.repeatIdx (fun (i : I) dx => (xdf i).2 (dy i) dx) dx) :=
by
  unfold revDerivUpdate
  simp [revDeriv.pi_rule _ _ hf, revDerivUpdate]
  sorry_proof
variable (I)

end revDerivUpdate


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDerivProj ------------------------------------
--------------------------------------------------------------------------------

namespace revDerivProj

variable (E)
theorem id_rule 
  : revDerivProj K I (fun x : E => x)
    =
    fun x => 
      (x,
       fun i de => 
         oneHot i de) := 
by
  unfold revDerivProj; simp[revDeriv.id_rule]

variable{E}

variable (Y)
theorem const_rule (x : E)
  : revDerivProj K I (fun _ : Y => x)
    =
    fun _ => 
      (x,
       fun i (de : EI i) => 0) := 
by
  unfold revDerivProj; simp[revDeriv.const_rule]
variable {Y}

theorem proj_rule [DecidableEq I] (i : ι)
  : revDerivProj K I (fun (f : ι → E) => f i)
    = 
    fun f : ι → E => 
      (f i, fun j dxj => oneHot (X:=ι→E) (I:=ι×I) (i,j) dxj) := 
by
  unfold revDerivProj; simp[revDeriv.proj_rule, oneHot]
  funext x; simp; funext j de i'
  if h:i=i' then
    subst h
    simp; congr; funext j'
    if h':j=j' then
      subst h'
      simp
    else
      simp[h']
  else
    simp[h]

theorem comp_rule
  (f : Y → E) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDerivProj K I (fun x => f (g x))
    =
    fun x => 
      let ydg' := revDeriv K g x
      let zdf' := revDerivProj K I f ydg'.1
      (zdf'.1,
       fun i de => 
         ydg'.2 (zdf'.2 i de)) := 
by
  unfold revDerivProj; simp[revDeriv.comp_rule _ _ _ hf hg]


theorem let_rule
  (f : X → Y → E) (g : X → Y)
  (hf : HasAdjDiff K (fun (x,y) => f x y)) (hg : HasAdjDiff K g)
  : revDerivProj K I (fun x => let y := g x; f x y)
    =
    fun x => 
      let ydg' := revDerivUpdate K g x
      let zdf' := revDerivProj K I (fun (x,y) => f x y) (x,ydg'.1)
      (zdf'.1,
       fun i dei => 
         let dxy := zdf'.2 i dei
         ydg'.2 dxy.2 dxy.1) := 
by
  unfold revDerivProj; simp[revDeriv.let_rule _ _ _ hf hg]

theorem pi_rule
  (f :  X → ι → Y) (hf : ∀ i, HasAdjDiff K (f · i))
  : (revDerivProj K Unit fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let ydf := fun i => revDerivUpdate K (f · i) x
      (fun i => (ydf i).1, 
       fun _ df => 
         Function.repeatIdx (fun i dx => (ydf i).2 (df i) dx) (0 : X)) := 
by
  sorry_proof

end revDerivProj


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDerivProjUpdate --------------------------------
--------------------------------------------------------------------------------

namespace revDerivProjUpdate


variable (E)
theorem id_rule 
  : revDerivProjUpdate K I (fun x : E => x)
    =
    fun x => 
      (x,
       fun i de dx => 
         structModify i (fun ei => ei + de) dx) := 
by
  funext x
  simp[revDerivProjUpdate, revDerivProj.id_rule]

variable {E}

variable (Y)
theorem const_rule (x : E)
  : revDerivProjUpdate K I (fun _ : Y => x)
    =
    fun _ => 
      (x,
       fun i de dx => dx) := 
by
  unfold revDerivProjUpdate; simp[revDerivProj.const_rule]

variable {Y}

theorem proj_rule [DecidableEq I] (i : ι)
  : revDerivProjUpdate K I (fun (f : ι → E) => f i)
    = 
    fun f => 
      (f i, fun j dxj df i' =>
        if i=i' then
          structModify j (fun xj => xj + dxj) (df i')
        else 
          df i') := 
by
  funext x;
  simp[revDerivProjUpdate, revDerivProj.proj_rule]
  funext j dxj f i'
  apply structExt (I:=I)
  intro j'
  if h :i'=i then
    subst h; simp
  else
    have h' : i≠i' := by intro h''; simp[h''] at h
    simp[h,h',Function.update]


theorem comp_rule
  (f : Y → E) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDerivProjUpdate K I (fun x => f (g x))
    =
    fun x => 
      let ydg' := revDerivUpdate K g x
      let zdf' := revDerivProj K I f ydg'.1
      (zdf'.1,
       fun i de dx => 
         ydg'.2 (zdf'.2 i de) dx) := 
by
  funext x
  simp[revDerivProjUpdate,revDerivProj.comp_rule _ _ _ _ hf hg]
  rfl


theorem let_rule
  (f : X → Y → E) (g : X → Y)
  (hf : HasAdjDiff K (fun (x,y) => f x y)) (hg : HasAdjDiff K g)
  : revDerivProjUpdate K I (fun x => let y := g x; f x y)
    =
    fun x => 
      let ydg' := revDerivUpdate K g x
      let zdf' := revDerivProjUpdate K I (fun (x,y) => f x y) (x,ydg'.1)
      (zdf'.1,
       fun i dei dx => 
         let dxy := zdf'.2 i dei (dx,0)
         ydg'.2 dxy.2 dxy.1) := 
by
  unfold revDerivProjUpdate
  simp [revDerivProj.let_rule _ _ _ _ hf hg,add_assoc,add_comm,revDerivUpdate]


theorem pi_rule
  (f :  X → ι → Y) (hf : ∀ i, HasAdjDiff K (f · i))
  : (revDerivProjUpdate K Unit fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let ydf := fun i => revDerivUpdate K (f · i) x
      (fun i => (ydf i).1, 
       fun _ df dx => Function.repeatIdx (fun i dx => (ydf i).2 (df i) dx) dx) := 
by
  conv => lhs; unfold revDerivProjUpdate
  simp [revDerivProj.pi_rule _ _ hf,add_assoc,add_comm]
  funext x; simp; funext i dei dx;
  sorry_proof


end revDerivProjUpdate


--------------------------------------------------------------------------------
-- Register `revCDeriv` as function transformation -----------------------------
--------------------------------------------------------------------------------
namespace revDeriv

open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `revDeriv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
  let cache := (← get).cache
  let config : FProp.Config := {}
  let state  : FProp.State := { cache := cache }
  let (proof?, state) ← FProp.fprop e |>.run config |>.run state
  modify (fun simpState => { simpState with cache := state.cache })
  if proof?.isSome then
    return proof?
  else
    if let .some prf ← Lean.Meta.findLocalDeclWithType? e then
      return .some (.fvar prf)
    else
      if e.isAppOf ``fpropParam then
        trace[Meta.Tactic.fprop.unsafe] s!"discharging with sorry: {← ppExpr e}"
        return .some <| ← mkAppOptM ``sorryProofAxiom #[e.appArg!]
      else
        return none


open Lean Meta FTrans in
def ftransExt : FTransExt where
  ftransName := ``revDeriv

  getFTransFun? e := 
    if e.isAppOf ``revDeriv then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``revDeriv then
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


-- register revDeriv
open Lean in
#eval show CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revDeriv, ftransExt))

end revDeriv



--------------------------------------------------------------------------------
-- Register `revDerivUpdate` as function transformation ------------------------
--------------------------------------------------------------------------------
namespace revDerivUpdate


open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `revDerivUpdate_discharger (fun _ => return s!"discharge {← ppExpr e}") do
  let cache := (← get).cache
  let config : FProp.Config := {}
  let state  : FProp.State := { cache := cache }
  let (proof?, state) ← FProp.fprop e |>.run config |>.run state
  modify (fun simpState => { simpState with cache := state.cache })
  if proof?.isSome then
    return proof?
  else
    if let .some prf ← Lean.Meta.findLocalDeclWithType? e then
      return .some (.fvar prf)
    else
      if e.isAppOf ``fpropParam then
        trace[Meta.Tactic.fprop.unsafe] s!"discharging with sorry: {← ppExpr e}"
        return .some <| ← mkAppOptM ``sorryProofAxiom #[e.appArg!]
      else
        return none


open Lean Meta FTrans in
def ftransExt : FTransExt where
  ftransName := ``revDerivUpdate

  getFTransFun? e := 
    if e.isAppOf ``revDerivUpdate then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``revDerivUpdate then
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


-- register revDerivUpdate
open Lean in
#eval show CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revDerivUpdate, ftransExt))

end revDerivUpdate


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
    if let .some prf ← Lean.Meta.findLocalDeclWithType? e then
      return .some (.fvar prf)
    else
      if e.isAppOf ``fpropParam then
        trace[Meta.Tactic.fprop.unsafe] s!"discharging with sorry: {← ppExpr e}"
        return .some <| ← mkAppOptM ``sorryProofAxiom #[e.appArg!]
      else
        return none


open Lean Meta FTrans in
def ftransExt : FTransExt where
  ftransName := ``revDerivProj

  getFTransFun? e := 
    if e.isAppOf ``revDerivProj then

      if let .some f := e.getArg? 11 then
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
    let .some I := e.getArg? 1 | return none
    let proof ← mkAppOptM ``id_rule #[K,I,none, X,none,none,none,none,none]
    tryTheorems
      #[ { proof := proof, origin := .decl ``id_rule, rfl := false} ]
      discharger e

  constRule e X y := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[K, I, X, y], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[K, I, X, i], origin := .decl ``proj_rule, rfl := false} ]
      discharger e

  compRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``comp_rule #[K, I, f, g], origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[K, I, f, g], origin := .decl ``let_rule, rfl := false} ]
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


--------------------------------------------------------------------------------
-- Register `revDerivProjUpdate` as function transformation --------------------
--------------------------------------------------------------------------------

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
    if let .some prf ← Lean.Meta.findLocalDeclWithType? e then
      return .some (.fvar prf)
    else
      if e.isAppOf ``fpropParam then
        trace[Meta.Tactic.fprop.unsafe] s!"discharging with sorry: {← ppExpr e}"
        return .some <| ← mkAppOptM ``sorryProofAxiom #[e.appArg!]
      else
        return none


open Lean Meta FTrans in
def ftransExt : FTransExt where
  ftransName := ``revDerivProjUpdate

  getFTransFun? e := 
    if e.isAppOf ``revDerivProjUpdate then

      if let .some f := e.getArg? 11 then
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
    let .some I := e.getArg? 1 | return none
    let proof ← mkAppOptM ``id_rule #[K,I,none, X,none,none,none,none,none]
    tryTheorems
      #[ { proof := proof, origin := .decl ``id_rule, rfl := false} ]
      discharger e

  constRule e X y := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[K, I, X, y], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[K, I, X, i], origin := .decl ``proj_rule, rfl := false} ]
      discharger e

  compRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``comp_rule #[K, I, f, g], origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[K, I, f, g], origin := .decl ``let_rule, rfl := false} ]
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
--------------------------------------------------------------------------------

end SciLean
open SciLean

variable 
  {K : Type} [IsROrC K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {X' Xi : Type} {XI : Xi → Type} [StructType X' Xi XI] [EnumType Xi]
  {Y' Yi : Type} {YI : Yi → Type} [StructType Y' Yi YI] [EnumType Yi]
  {Z' Zi : Type} {ZI : Zi → Type} [StructType Z' Zi ZI] [EnumType Zi]
  [SemiInnerProductSpace K X'] [∀ i, SemiInnerProductSpace K (XI i)] [SemiInnerProductSpaceStruct K X' Xi XI]
  [SemiInnerProductSpace K Y'] [∀ i, SemiInnerProductSpace K (YI i)] [SemiInnerProductSpaceStruct K Y' Yi YI]
  [SemiInnerProductSpace K Z'] [∀ i, SemiInnerProductSpace K (ZI i)] [SemiInnerProductSpaceStruct K Z' Zi ZI]
  {W : Type} [SemiInnerProductSpace K W]
  {ι : Type} [EnumType ι]



-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.revDeriv_rule
  (g : X → Y) (f : X → Z)
  (hg : HasAdjDiff K g) (hf : HasAdjDiff K f)
  : revDeriv K (fun x => (g x, f x))
    =
    fun x => 
      let ydg := revDeriv K g x
      let zdf := revDerivUpdate K f x
      ((ydg.1,zdf.1), 
       fun dyz => 
         let dx := ydg.2 dyz.1
         zdf.2 dyz.2 dx) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate; unfold revDeriv; simp; ftrans; ftrans; simp

@[ftrans]
theorem Prod.mk.arg_fstsnd.revDerivUpdate_rule
  (g : X → Y) (f : X → Z)
  (hg : HasAdjDiff K g) (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun x => (g x, f x))
    =
    fun x => 
      let ydg := revDerivUpdate K g x
      let zdf := revDerivUpdate K f x
      ((ydg.1,zdf.1), 
       fun dyz dx => 
         let dx := ydg.2 dyz.1 dx
         zdf.2 dyz.2 dx) := 
by 
  unfold revDerivUpdate; ftrans; simp[add_assoc, revDerivUpdate]

@[ftrans]
theorem Prod.mk.arg_fstsnd.revDerivProj_rule
  (g : X → Y') (f : X → Z')
  (hg : HasAdjDiff K g) (hf : HasAdjDiff K f)
  : revDerivProj K (Yi⊕Zi) (fun x => (g x, f x))
    =
    fun x => 
      let ydg := revDerivProj K Yi g x
      let zdf := revDerivProj K Zi f x
      ((ydg.1,zdf.1), 
       fun i dyz => 
         match i with
         | .inl j => ydg.2 j dyz
         | .inr j => zdf.2 j dyz) := 
by
  unfold revDerivProj
  funext x; ftrans; simp[revDerivUpdate]
  funext i dyz
  induction i <;>
    { simp[oneHot,structMake]
      apply congr_arg
      congr; funext i; congr; funext h
      subst h; rfl
    }

@[ftrans]
theorem Prod.mk.arg_fstsnd.revDerivProjUpdate_rule
  (g : X → Y') (f : X → Z')
  (hg : HasAdjDiff K g) (hf : HasAdjDiff K f)
  : revDerivProjUpdate K (Yi⊕Zi) (fun x => (g x, f x))
    =
    fun x => 
      let ydg := revDerivProjUpdate K Yi g x
      let zdf := revDerivProjUpdate K Zi f x
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
theorem Prod.fst.arg_self.revDeriv_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revDeriv K (fun x => (f x).1)
    =
    fun x => 
      let yzdf := revDerivProj K (Unit⊕Unit) f x
      (yzdf.1.1, fun dy => yzdf.2 (.inl ()) dy) := 
by 
  have ⟨_,_⟩ := hf
  unfold revDerivProj; unfold revDeriv; ftrans; ftrans; simp[structMake, oneHot]

@[ftrans]
theorem Prod.fst.arg_self.revDerivUpdate_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun x => (f x).1)
    =
    fun x => 
      let yzdf := revDerivProjUpdate K (Unit⊕Unit) f x
      (yzdf.1.1, fun dy dx => yzdf.2 (.inl ()) dy dx) := 
by 
  unfold revDerivProjUpdate; unfold revDerivUpdate;
  ftrans

@[ftrans]
theorem Prod.fst.arg_self.revDerivProj_rule
  (f : W → X'×Y) (hf : HasAdjDiff K f)
  : revDerivProj K Xi (fun x => (f x).1)
    =
    fun w => 
      let xydf := revDerivProj K (Xi⊕Unit) f w
      (xydf.1.1,
       fun i dxy => xydf.2 (.inl i) dxy) := 
by
  unfold revDerivProj
  funext x; ftrans; simp[revDerivProj]
 
@[ftrans]
theorem Prod.fst.arg_self.revDerivProjUpdate_rule
  (f : W → X'×Y) (hf : HasAdjDiff K f)
  : revDerivProjUpdate K Xi (fun x => (f x).1)
    =
    fun w => 
      let xydf := revDerivProjUpdate K (Xi⊕Unit) f w
      (xydf.1.1,
       fun i dxy dw => xydf.2 (.inl i) dxy dw) := 
by
  unfold revDerivProjUpdate
  funext x; ftrans; simp


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.revDeriv_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revDeriv K (fun x => (f x).2)
    =
    fun x => 
      let yzdf := revDerivProj K (Unit⊕Unit) f x
      (yzdf.1.2, fun dy => yzdf.2 (.inr ()) dy) := 
by 
  have ⟨_,_⟩ := hf
  unfold revDerivProj; unfold revDeriv; ftrans; ftrans; simp[structMake, oneHot]

@[ftrans]
theorem Prod.snd.arg_self.revDerivUpdate_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun x => (f x).2)
    =
    fun x => 
      let yzdf := revDerivProjUpdate K (Unit⊕Unit) f x
      (yzdf.1.2, fun dy dx => yzdf.2 (.inr ()) dy dx) := 
by 
  unfold revDerivProjUpdate; unfold revDerivUpdate;
  ftrans

@[ftrans]
theorem Prod.snd.arg_self.revDerivProj_rule
  (f : W → X×Y') (hf : HasAdjDiff K f)
  : revDerivProj K Yi (fun x => (f x).2)
    =
    fun w => 
      let xydf := revDerivProj K (Unit⊕Yi) f w
      (xydf.1.2,
       fun i dxy => xydf.2 (.inr i) dxy) := 
by
  unfold revDerivProj
  funext x; ftrans; simp[revDerivProj]

@[ftrans]
theorem Prod.snd.arg_self.revDerivProjUpdate_rule
  (f : W → X×Y') (hf : HasAdjDiff K f)
  : revDerivProjUpdate K Yi (fun x => (f x).2)
    =
    fun w => 
      let xydf := revDerivProjUpdate K (Unit⊕Yi) f w
      (xydf.1.2,
       fun i dxy dw => xydf.2 (.inr i) dxy dw) := 
by
  unfold revDerivProjUpdate
  funext x; ftrans; simp
 

-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revDeriv_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDeriv K fun x => f x + g x)
    =
    fun x => 
      let ydf := revDeriv K f x
      let ydg := revDerivUpdate K g x
      (ydf.1 + ydg.1, 
       fun dy => 
         let dx := ydf.2 dy
         ydg.2 dy dx) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate; unfold revDeriv; simp; ftrans; ftrans; simp

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revDerivUpdate_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivUpdate K fun x => f x + g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let ydg := revDerivUpdate K g x
      (ydf.1 + ydg.1, 
       fun dy dx => 
         let dx := ydf.2 dy dx
         ydg.2 dy dx) := 
by 
  unfold revDerivUpdate
  ftrans; funext x; simp[add_assoc,revDerivUpdate]

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revDerivProj_rule
  (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProj K Yi fun x => f x + g x)
    =
    fun x => 
      let ydf := revDerivProj K Yi f x
      let ydg := revDerivProjUpdate K Yi g x
      (ydf.1 + ydg.1, 
       fun i dy => 
         let dx := ydf.2 i dy
         (ydg.2 i dy dx)) := 
by 
  unfold revDerivProjUpdate; unfold revDerivProj
  ftrans; simp[revDerivUpdate]

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revDerivProjUpdate_rule
  (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProjUpdate K Yi fun x => f x + g x)
    =
    fun x => 
      let ydf := revDerivProjUpdate K Yi f x
      let ydg := revDerivProjUpdate K Yi g x
      (ydf.1 + ydg.1, 
       fun i dy dx => 
         let dx := ydf.2 i dy dx
         ydg.2 i dy dx) := 
by 
  unfold revDerivProjUpdate
  ftrans; simp[revDerivProjUpdate, add_assoc]


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.revDeriv_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDeriv K fun x => f x - g x)
    =
    fun x => 
      let ydf := revDeriv K f x
      let ydg := revDerivUpdate K g x
      (ydf.1 - ydg.1, 
       fun dy => 
         let dx := ydf.2 dy
         let dy' := -dy
         ydg.2 dy' dx) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate; unfold revDeriv; ftrans; ftrans
  funext x; simp; funext dy; simp only [neg_pull, ← sub_eq_add_neg]

@[ftrans]
theorem HSub.hSub.arg_a0a1.revDerivUpdate_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivUpdate K fun x => f x - g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let ydg := revDerivUpdate K g x
      (ydf.1 - ydg.1, 
       fun dy dx => 
         let dx := ydf.2 dy dx
         let dy' := -dy
         ydg.2 dy' dx) := 
by 
  unfold revDerivUpdate
  ftrans; funext x; simp[add_assoc,revDerivUpdate]

@[ftrans]
theorem HSub.hSub.arg_a0a1.revDerivProj_rule
  (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProj K Yi fun x => f x - g x)
    =
    fun x => 
      let ydf := revDerivProj K Yi f x
      let ydg := revDerivProjUpdate K Yi g x
      (ydf.1 - ydg.1, 
       fun i dy => 
         let dx := ydf.2 i dy
         let dy' := -dy
         (ydg.2 i dy' dx)) := 
by 
  unfold revDerivProjUpdate; unfold revDerivProj
  ftrans; simp[revDerivUpdate, neg_pull,revDeriv]


@[ftrans]
theorem HSub.hSub.arg_a0a1.revDerivProjUpdate_rule
  (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProjUpdate K Yi fun x => f x - g x)
    =
    fun x => 
      let ydf := revDerivProjUpdate K Yi f x
      let ydg := revDerivProjUpdate K Yi g x
      (ydf.1 - ydg.1, 
       fun i dy dx => 
         let dx := ydf.2 i dy dx
         let dy' := -dy
         ydg.2 i dy' dx) := 
by 
  unfold revDerivProjUpdate
  ftrans; simp[revDerivProjUpdate, neg_pull, revDerivProj, revDeriv,add_assoc]


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.revDeriv_rule
  (f : X → Y) (x : X) 
  : (revDeriv K fun x => - f x) x
    =
    let ydf := revDeriv K f x
    (-ydf.1, 
     fun dy => 
       let dx := ydf.2 dy
       (-dx)) :=
by 
  unfold revDeriv; simp; ftrans; ftrans

@[ftrans]
theorem Neg.neg.arg_a0.revDerivUpdate_rule
  (f : X → Y)
  : (revDerivUpdate K fun x => - f x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      (-ydf.1, 
       fun dy dx => 
         let dy' := -dy
         ydf.2 dy' dx) :=
by 
  unfold revDerivUpdate; funext x; ftrans; simp[neg_pull,revDeriv]

@[ftrans]
theorem Neg.neg.arg_a0.revDerivProj_rule
  (f : X → Y')
  : (revDerivProj K Yi fun x => - f x)
    =
    fun x => 
      let ydf := revDerivProj K Yi f x
      (-ydf.1, 
       fun i dy => 
         let dy' := -dy
         ydf.2 i dy') :=
by 
  unfold revDerivProj; ftrans; simp[neg_push,revDeriv]

@[ftrans]
theorem Neg.neg.arg_a0.revDerivProjUpdate_rule
  (f : X → Y')
  : (revDerivProjUpdate K Yi fun x => - f x)
    =
    fun x => 
      let ydf := revDerivProjUpdate K Yi f x
      (-ydf.1, 
       fun i dy dx => 
         let dy' := -dy
         ydf.2 i dy' dx) :=
by 
  unfold revDerivProjUpdate; ftrans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------
open ComplexConjugate

@[ftrans]
theorem HMul.hMul.arg_a0a1.revDeriv_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDeriv K fun x => f x * g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDeriv K g x
      (ydf.1 * zdg.1, 
       fun dx' => 
         let dx₁ := (conj zdg.1 * dx') 
         let dx₂ := (conj ydf.1 * dx')
         let dx := zdg.2 dx₂
         ydf.2 dx₁ dx) :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate; unfold revDeriv; simp; ftrans; ftrans;
  simp [smul_push]

@[ftrans]
theorem HMul.hMul.arg_a0a1.revDerivUpdate_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivUpdate K fun x => f x * g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 * zdg.1, 
       fun dx' dx => 
         let dx₁ := (conj zdg.1 * dx') 
         let dx₂ := (conj ydf.1 * dx')
         let dx := zdg.2 dx₂ dx
         ydf.2 dx₁ dx) :=
by 
  unfold revDerivUpdate; simp; ftrans; ftrans;
  simp [smul_push,add_assoc,revDerivUpdate]

@[ftrans]
theorem HMul.hMul.arg_a0a1.revDerivProj_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProj K Unit fun x => f x * g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDeriv K g x
      (ydf.1 * zdg.1, 
       fun _ dy => 
         let dy₁ := (conj zdg.1)*dy
         let dy₂ := (conj ydf.1)*dy
         let dx := zdg.2 dy₂
         ydf.2 dy₁ dx) :=
by 
  unfold revDerivProj
  ftrans; simp[oneHot, structMake]

@[ftrans]
theorem HMul.hMul.arg_a0a1.revDerivProjUpdate_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProjUpdate K Unit fun x => f x * g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 * zdg.1, 
       fun _ dy dx => 
         let dy₁ := (conj zdg.1)*dy
         let dy₂ := (conj ydf.1)*dy
         let dx := zdg.2 dy₂ dx
         ydf.2 dy₁ dx) :=
by 
  unfold revDerivProjUpdate
  ftrans; simp[revDerivUpdate,add_assoc]



-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revDeriv_rule
  {Y : Type} [SemiHilbert K Y]
  (f : X → K) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDeriv K fun x => f x • g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDeriv K g x
      (ydf.1 • zdg.1, 
       fun dy' => 
         let dk := inner zdg.1 dy'
         let dx := zdg.2 dy'
         let dx := conj ydf.1 • dx
         ydf.2 dk dx) :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv; unfold revDerivUpdate; ftrans; ftrans; simp[revDeriv]


@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revDerivUpdate_rule
  {Y : Type} [SemiHilbert K Y]
  (f : X → K) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivUpdate K fun x => f x • g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 • zdg.1, 
       fun dy dx => 
         let dk := inner zdg.1 dy
         let dy' := conj ydf.1 • dy
         let dx := zdg.2 dy' dx
         ydf.2 dk dx) :=
by 
  unfold revDerivUpdate; 
  funext x; ftrans; simp[mul_assoc,add_assoc,revDerivUpdate,revDeriv,smul_push]

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revDerivProj_rule
  {Y Yi : Type} {YI : Yi → Type} [StructType Y Yi YI] [EnumType Yi]
  [SemiHilbert K Y] [∀ i, SemiHilbert K (YI i)] [SemiInnerProductSpaceStruct K Y Yi YI]
  (f : X → K) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProj K Yi fun x => f x • g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivProj K Yi g x
      (ydf.1 • zdg.1, 
       fun i (dy : YI i) => 
         let dk := inner (structProj zdg.1 i) dy
         let dx := zdg.2 i dy
         let dx := conj ydf.1•dx
         ydf.2 dk dx) :=
by 
  unfold revDerivProj; ftrans

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revDerivProjUpdate_rule
  {Y Yi : Type} {YI : Yi → Type} [StructType Y Yi YI] [EnumType Yi]
  [SemiHilbert K Y] [∀ i, SemiHilbert K (YI i)] [SemiInnerProductSpaceStruct K Y Yi YI]
  (f : X → K) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivProjUpdate K Yi fun x => f x • g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivProjUpdate K Yi g x
      (ydf.1 • zdg.1, 
       fun i (dy : YI i) dx => 
         let dk := inner (structProj zdg.1 i) dy
         let dy' := conj ydf.1•dy
         let dx := zdg.2 i dy' dx
         ydf.2 dk dx) :=
by 
  unfold revDerivProjUpdate
  ftrans; simp[revDerivUpdate,add_assoc,smul_pull]
  simp only [smul_pull,revDerivProj,revDeriv]



-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revDeriv_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : fpropParam (∀ x, g x ≠ 0))
  : (revDeriv K fun x => f x / g x)
    =
    fun x => 
      let ydf := revDeriv K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 / zdg.1, 
       fun dx' => (1 / (conj zdg.1)^2) • (zdg.2 (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 dx'))) :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv; simp; ftrans; ftrans
  simp[revDerivUpdate,smul_push,neg_pull,revDeriv,smul_add,smul_sub, ← sub_eq_add_neg]

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revDerivUpdate_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : fpropParam (∀ x, g x ≠ 0))
  : (revDerivUpdate K fun x => f x / g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 / zdg.1, 
       fun dx' dx => 
         let c := (1 / (conj zdg.1)^2)
         let a := -(c * conj ydf.1)
         let b := c * conj zdg.1
         ((zdg.2 (a • dx') (ydf.2 (b • dx') dx)))) :=
by 
  funext
  simp[revDerivUpdate]; ftrans
  simp[revDerivUpdate,smul_push,neg_pull,revDeriv,smul_add,smul_sub,add_assoc,mul_assoc]

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revDerivProj_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : fpropParam (∀ x, g x ≠ 0))
  : (revDerivProj K Unit fun x => f x / g x)
    =
    fun x => 
      let ydf := revDeriv K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 / zdg.1, 
       fun _ dx' => (1 / (conj zdg.1)^2) • (zdg.2 (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 dx'))) :=
by 
  unfold revDerivProj
  ftrans; simp[oneHot, structMake]

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revDerivProjUpdate_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : fpropParam (∀ x, g x ≠ 0))
  : (revDerivProjUpdate K Unit fun x => f x / g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 / zdg.1, 
       fun _ dx' dx => 
         let c := (1 / (conj zdg.1)^2)
         let a := -(c * conj ydf.1)
         let b := c * conj zdg.1
         ((zdg.2 (a • dx') (ydf.2 (b • dx') dx)))) :=
by 
  unfold revDerivProjUpdate
  ftrans; simp[revDerivUpdate,revDeriv,add_assoc,neg_pull,mul_assoc,smul_push]


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HPow.hPow.arg_a0.revDeriv_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f) 
  : revDeriv K (fun x => f x ^ n)
    =
    fun x => 
      let ydf := revDeriv K f x
      let y' := (n : K) * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n, 
       fun dx' => ydf.2 (y' * dx')) :=
by 
  have ⟨_,_⟩ := hf
  funext x
  unfold revDeriv; simp; funext dx; ftrans; ftrans; simp[smul_push,smul_smul]; ring_nf

@[ftrans]
def HPow.hPow.arg_a0.revDerivUpdate_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f) 
  : revDerivUpdate K (fun x => f x ^ n)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let y' := n * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n, 
       fun dy dx => ydf.2 (y' * dy) dx) :=
by 
  unfold revDerivUpdate
  funext x; ftrans; simp[mul_assoc,mul_comm,add_assoc]

@[ftrans]
def HPow.hPow.arg_a0.revDerivProj_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f)
  : revDerivProj K Unit (fun x => f x ^ n)
    =
    fun x => 
      let ydf := revDeriv K f x
      let y' := (n : K) * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n, fun _ dx' => ydf.2 (y' * dx')) :=
by 
  unfold revDerivProj; ftrans; simp[oneHot,structMake]

@[ftrans]
def HPow.hPow.arg_a0.revDerivProjUpdate_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f) 
  : revDerivProjUpdate K Unit (fun x => f x ^ n)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let y' := n * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n, 
       fun _ dy dx => ydf.2 (y' * dy) dx) :=
by 
  unfold revDerivProjUpdate; ftrans; simp[oneHot,structMake,revDerivUpdate]


-- EnumType.sum ----------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem SciLean.EnumType.sum.arg_f.revDeriv_rule {ι : Type} [EnumType ι]
  (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDeriv K (fun x => ∑ i, f x i)
    =
    fun x => 
      let ydf := fun i => revDerivUpdate K (f · i) x
      (∑ i, (ydf i).1, 
       fun dy => Function.repeatIdx (fun i dx => (ydf i).2 dy dx) 0) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  funext
  sorry_proof


@[ftrans]
theorem SciLean.EnumType.sum.arg_f.revDerivUpdate_rule {ι : Type} [EnumType ι]
  (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDerivUpdate K (fun x => ∑ i, f x i)
    =
    fun x => 
      let ydf := fun i => revDerivUpdate K (f · i) x
      (∑ i, (ydf i).1, 
       fun dy dx => Function.repeatIdx (fun i dx => (ydf i).2 dy dx) dx) :=
by
  simp[revDerivUpdate]
  ftrans
  sorry_proof


@[ftrans]
theorem SciLean.EnumType.sum.arg_f.revDerivProj_rule {ι : Type} [EnumType ι]
  (f : X → ι → Y') (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDerivProj K Yi (fun x => ∑ i, f x i)
    =
    fun x => 
      let ydf := fun i => revDerivProjUpdate K Yi (f · i) x
      (∑ i, (ydf i).1, 
       fun j dy => Function.repeatIdx (fun (i : ι) dx => (ydf i).2 j dy dx) 0) :=
by
  funext; simp[revDerivProj]; ftrans; sorry_proof


@[ftrans]
theorem SciLean.EnumType.sum.arg_f.revDerivProjUpdate_rule {ι : Type} [EnumType ι]
  (f : X → ι → Y') (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDerivProjUpdate K Yi (fun x => ∑ i, f x i)
    =
    fun x => 
      let ydf := fun i => revDerivProjUpdate K Yi (f · i) x
      (∑ i, (ydf i).1, 
       fun j dy dx => Function.repeatIdx (fun (i : ι) dx => (ydf i).2 j dy dx) dx) :=
by
  funext; simp[revDerivProjUpdate]; ftrans; sorry_proof


-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem ite.arg_te.revDeriv_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y)
  : revDeriv K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDeriv K t y) (revDeriv K e y) := 
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[ftrans]
theorem ite.arg_te.revDerivUpdate_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y)
  : revDerivUpdate K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDerivUpdate K t y) (revDerivUpdate K e y) := 
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[ftrans]
theorem ite.arg_te.revDerivProj_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y')
  : revDerivProj K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDerivProj K Yi t y) (revDerivProj K Yi e y) := 
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[ftrans]
theorem ite.arg_te.revDerivProjUpdate_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y')
  : revDerivProjUpdate K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDerivProjUpdate K Yi t y) (revDerivProjUpdate K Yi e y) := 
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]


@[ftrans]
theorem dite.arg_te.revDeriv_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (e : ¬c → X → Y)
  : revDeriv K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDeriv K (t p) y) 
             (fun p => revDeriv K (e p) y) := 
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[ftrans]
theorem dite.arg_te.revDerivUpdate_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (e : ¬c → X → Y)
  : revDerivUpdate K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDerivUpdate K (t p) y) 
             (fun p => revDerivUpdate K (e p) y) := 
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[ftrans]
theorem dite.arg_te.revDerivProj_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y') (e : ¬c → X → Y')
  : revDerivProj K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDerivProj K Yi (t p) y) 
             (fun p => revDerivProj K Yi (e p) y) := 
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[ftrans]
theorem dite.arg_te.revDerivProjUpdate_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y') (e : ¬c → X → Y')
  : revDerivProjUpdate K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDerivProjUpdate K Yi (t p) y) 
             (fun p => revDerivProjUpdate K Yi (e p) y) := 
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]


--------------------------------------------------------------------------------

section InnerProductSpace

variable 
  {R : Type _} [RealScalar R]
  -- {K : Type _} [Scalar R K]
  {X : Type _} [SemiInnerProductSpace R X]
  {Y : Type _} [SemiHilbert R Y]

-- Inner -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate

@[ftrans]
theorem Inner.inner.arg_a0a1.revDeriv_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDeriv R fun x => ⟪f x, g x⟫[R])
    =
    fun x => 
      let y₁df := revDeriv R f x
      let y₂dg := revDerivUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr => 
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1))):=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  funext; simp[revDeriv,revDerivUpdate]
  ftrans only; simp
  ftrans; simp[smul_pull]

@[ftrans]
theorem Inner.inner.arg_a0a1.revDerivUpdate_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDerivUpdate R fun x => ⟪f x, g x⟫[R])
    =
    fun x => 
      let y₁df := revDerivUpdate R f x
      let y₂dg := revDerivUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr dx => 
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1) dx) ) := 

by 
  unfold revDerivUpdate
  ftrans; simp[revDerivUpdate,add_assoc]

@[ftrans]
theorem Inner.inner.arg_a0a1.revDerivProj_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDerivProj R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x => 
      let y₁df := revDeriv R f x
      let y₂dg := revDerivUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr => 
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1))) :=
by 
  funext
  simp[revDerivProj]
  ftrans; simp[oneHot, structMake]

@[ftrans]
theorem Inner.inner.arg_a0a1.revDerivProjUpdate_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDerivProjUpdate R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x => 
      let y₁df := revDerivUpdate R f x
      let y₂dg := revDerivUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr dx => 
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1) dx)) := 
by 
  funext
  simp[revDerivProjUpdate]
  ftrans; simp[revDerivUpdate,add_assoc]



-- norm2 -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem SciLean.Norm2.norm2.arg_a0.revDeriv_rule
  (f : X → Y) (hf : HasAdjDiff R f) 
  : (revDeriv R fun x => ‖f x‖₂²[R])
    =
    fun x => 
      let ydf := revDeriv R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun dr => 
         ((2:R) * dr) • ydf.2 ydf.1):=
by 
  have ⟨_,_⟩ := hf
  funext x; simp[revDeriv]
  ftrans only
  simp
  ftrans
  simp[smul_smul]

@[ftrans]
theorem SciLean.Norm2.norm2.arg_a0.revDerivUpdate_rule
  (f : X → Y) (hf : HasAdjDiff R f) 
  : (revDerivUpdate R fun x => ‖f x‖₂²[R])
    =
    fun x => 
      let ydf := revDerivUpdate R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun dr dx => 
          ydf.2 (((2:R)*dr)•ydf.1) dx) :=
by 
  have ⟨_,_⟩ := hf
  funext x; simp[revDerivUpdate]
  ftrans only; simp[revDeriv,smul_pull]


@[ftrans]
theorem SciLean.Norm2.norm2.arg_a0.revDerivProj_rule
  (f : X → Y) (hf : HasAdjDiff R f) 
  : (revDerivProj R Unit fun x => ‖f x‖₂²[R])
    =
    fun x => 
      let ydf := revDeriv R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr => 
         ((2:R) * dr) • ydf.2 ydf.1):=
by 
  have ⟨_,_⟩ := hf
  funext x; simp[revDerivProj]
  ftrans; simp[oneHot,structMake]

@[ftrans]
theorem SciLean.Norm2.norm2.arg_a0.revDerivProjUpdate_rule
  (f : X → Y) (hf : HasAdjDiff R f) 
  : (revDerivProjUpdate R Unit fun x => ‖f x‖₂²[R])
    =
    fun x => 
      let ydf := revDerivUpdate R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr dx => 
          ydf.2 (((2:R)*dr)•ydf.1) dx) :=
by 
  have ⟨_,_⟩ := hf
  funext x; simp[revDerivProjUpdate]
  ftrans only; simp[revDeriv,revDerivUpdate,smul_pull]


-- norm₂ -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem SciLean.norm₂.arg_x.revDeriv_rule_at
  (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDeriv R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDeriv R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun dr => 
       (ynorm⁻¹ * dr) • ydf.2 ydf.1):=
by 
  have ⟨_,_⟩ := hf
  simp[revDeriv]
  ftrans only
  simp
  ftrans
  funext dr; simp[smul_smul]

@[ftrans]
theorem SciLean.norm₂.arg_x.revDerivUpdate_rule_at
  (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDerivUpdate R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDerivUpdate R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun dr dx => 
       ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
by 
  have ⟨_,_⟩ := hf
  simp[revDerivUpdate]
  ftrans only
  simp
  ftrans
  funext dr; simp[revDeriv,smul_pull]

@[ftrans]
theorem SciLean.norm₂.arg_x.revDerivProj_rule_at
  (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDerivProj R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDeriv R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr => 
       (ynorm⁻¹ * dr) • ydf.2 ydf.1):=
by 
  have ⟨_,_⟩ := hf
  simp[revDerivProj]
  ftrans only; simp[oneHot, structMake]

@[ftrans]
theorem SciLean.norm₂.arg_x.revDerivProjUpdate_rule_at
  (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDerivProjUpdate R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDerivUpdate R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr dx => 
       ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
by 
  have ⟨_,_⟩ := hf
  simp[revDerivProjUpdate]
  ftrans only; simp[revDeriv,revDerivUpdate,smul_pull]


@[ftrans]
theorem SciLean.norm₂.arg_x.revDeriv_rule
  (f : X → Y) (hf : HasAdjDiff R f) (hx : fpropParam <| ∀ x, f x≠0)
  : (revDeriv R (fun x => ‖f x‖₂[R]))
    =
    fun x => 
      let ydf := revDeriv R f x
      let ynorm := ‖ydf.1‖₂[R]
      (ynorm,
       fun dr => 
         (ynorm⁻¹ * dr) • ydf.2 ydf.1):=
by 
  have ⟨_,_⟩ := hf
  simp[revDeriv]
  ftrans only
  sorry_proof

@[ftrans]
theorem SciLean.norm₂.arg_x.revDerivUpdate_rule
  (f : X → Y) (hf : HasAdjDiff R f) (hx : fpropParam <| ∀ x, f x≠0)
  : (revDerivUpdate R (fun x => ‖f x‖₂[R]))
    =
    fun x => 
      let ydf := revDerivUpdate R f x
      let ynorm := ‖ydf.1‖₂[R]
      (ynorm,
       fun dr dx => 
         ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
by 
  have ⟨_,_⟩ := hf
  simp[revDerivUpdate]
  ftrans only
  sorry_proof
  -- simp
  -- ftrans
  -- funext dr; simp[revDeriv,smul_pull]

@[ftrans]
theorem SciLean.norm₂.arg_x.revDerivProj_rule
  (f : X → Y) (hf : HasAdjDiff R f) (hx : fpropParam <| ∀ x, f x≠0)
  : (revDerivProj R Unit (fun x => ‖f x‖₂[R]))
    =
    fun x =>
      let ydf := revDeriv R f x
      let ynorm := ‖ydf.1‖₂[R]
      (ynorm,
       fun _ dr => 
         (ynorm⁻¹ * dr) • ydf.2 ydf.1):=
by 
  have ⟨_,_⟩ := hf
  simp[revDerivProj]
  ftrans only; 
  sorry_proof -- simp[oneHot, structMake]

@[ftrans]
theorem SciLean.norm₂.arg_x.revDerivProjUpdate_rule
  (f : X → Y) (hf : HasAdjDiff R f) (hx : fpropParam <| ∀ x, f x≠0)
  : (revDerivProjUpdate R Unit (fun x => ‖f x‖₂[R]))
    =
    fun x => 
       let ydf := revDerivUpdate R f x
       let ynorm := ‖ydf.1‖₂[R]
       (ynorm,
        fun _ dr dx => 
          ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx) :=
by 
  have ⟨_,_⟩ := hf
  simp[revDerivProjUpdate]
  ftrans only; simp[revDeriv,revDerivUpdate,smul_pull]
  sorry_proof

end InnerProductSpace
