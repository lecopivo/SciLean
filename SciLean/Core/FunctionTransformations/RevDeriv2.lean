import SciLean.Core.FunctionPropositions.HasAdjDiff
import SciLean.Core.FunctionTransformations.SemiAdjoint

import SciLean.Data.StructType.Algebra

set_option linter.unusedVariables false

namespace SciLean

variable
  (K I : Type) [IsROrC K]
  {W : Type} [SemiInnerProductSpace K W]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {ι : Type} [EnumType ι]
  -- {κ : Type} [EnumType κ]
  {E : Type} {EI : I → Type}
  [StructType E I EI] [EnumType.{0,0,0} I]
  [SemiInnerProductSpace K E] [∀ i, SemiInnerProductSpace K (EI i)]
  {XI : I → Type} [StructType X I XI] [∀ i, SemiInnerProductSpace K (XI i)]
  {YI : I → Type} [StructType Y I YI] [∀ i, SemiInnerProductSpace K (YI i)]
  {ZI : I → Type} [StructType Z I ZI] [∀ i, SemiInnerProductSpace K (ZI i)]
  {WI : I → Type} [StructType W I WI] [∀ i, SemiInnerProductSpace K (WI i)]

  -- [SemiInnerProductSpaceStruct K E I EI]
  -- {F J : Type} {FJ : J → Type}
  -- [StructType F J FJ] [EnumType J]
  -- [SemiInnerProductSpace K F] [∀ j, SemiInnerProductSpace K (FJ j)]
  -- [SemiInnerProductSpaceStruct K F J FJ]


noncomputable
def revDeriv
  (f : W → X → Y) (w : W) (x : X) : Y×(Y→W→(W×X)) :=
  (f w x,
   fun dy =>
     let (dw,dx) := semiAdjoint K (cderiv K (fun (w,x) => f w x) (w,x)) dy
     fun dw' => (dw'+dw,dx))

noncomputable
def revDerivProj
  (f : W → X→ Y) (w : W) (x : X) (i : I) : YI i×(YI i→W→(W×X)) :=
  let ydf := revDeriv K f w x
  (structProj ydf.1 i,
   fun dyi => ydf.2 (oneHot i dyi))


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDeriv ------------------------------------------
--------------------------------------------------------------------------------

namespace revDeriv

theorem id1_rule
  : revDeriv K (fun (w : W) (x : X) => w)
    =
    fun w x =>
      (w, fun dw dw' => (dw' + dw, 0)) :=
by
  unfold revDeriv
  funext x y; fun_trans

theorem id2_rule
  : revDeriv K (fun (w : W) (x : X) => x)
    =
    fun w x =>
      (x, fun dx dw' => (dw', dx)) :=
by
  unfold revDeriv
  funext x y; fun_trans

theorem const_rule (y : Y)
  : revDeriv K (fun (_ : W) (_ : X) => y)
    =
    fun w x => (y, fun _ dw' => (dw',0)) :=
by
  unfold revDeriv
  funext x y; simp; fun_trans
  sorry_proof


theorem let_rule
  (f : W → X → Y → Z) (g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x,y) => f w x y)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv K (fun (w : W) (x : X) => let y := g w x; f w x y)
    =
    fun w x =>
      let ydg := revDeriv K (fun (wx : W×X) (_ : Unit) => g wx.1 wx.2) (w,x) ()
      let zdf := revDeriv K (fun w (xy : X×Y) => f w xy.1 xy.2) w (x,ydg.1)
      (zdf.1,
       fun dz dx =>
         let dxyz := zdf.2 dz dx
         let dxy := ydg.2 dxyz.2.2 (dxyz.1,dxyz.2.1)
         dxy.1) :=
by
  simp at hf hg
  unfold revDeriv
  funext x y; simp (config:={zeta:=false});
  conv => lhs; fun_trans
  simp; funext dy dw'
  sorry_proof


theorem pi_rule
  (f :  X → Y → (i : I) → EI i) (hf : ∀ i, HasAdjDiff K (fun (x,y) => f x y i))
  : (revDeriv K fun (x : X) (y : Y) (i : I) => f x y i)
    =
    fun x y =>
      let xdf := revDerivProj K I (fun (x,y) (_:Unit) => f x y) (x,y) ()
      (fun i => (xdf i).1,
       fun df dx' =>
         Function.repeatIdx (fun (i : I) dxy => ((xdf i).2 (df i) dxy).1) (dx',0)) :=
by
  simp at hf
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  unfold revDerivProj revDeriv
  funext x y; fun_trans; fun_trans; simp
  funext dw dx;
  sorry_proof -- needs some relation between sum and repeatIdx
variable (I)

end revDeriv


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDerivProj --------------------------------------
--------------------------------------------------------------------------------

namespace revDerivProj

variable (W X)
theorem id1_rule
  : revDerivProj K I (fun (w : W) (x : X) => w)
    =
    fun w x i =>
      (structProj w i, fun dwi dw' => (structModify i (fun wi => wi + dwi) dw', 0)) :=
by
  unfold revDerivProj
  simp[revDeriv.id1_rule K]


theorem id2_rule
  : revDerivProj K I (fun (w : W) (x : X) => x)
    =
    fun w x i =>
      (structProj x i, fun dxi dw' => (dw',oneHot i dxi)) :=
by
  unfold revDerivProj
  simp (config:={zeta:=false}) [revDeriv.id2_rule K]


theorem const_rule (y : Y)
  : revDerivProj K I (fun (_ : W) (_ : X) => y)
    =
    fun w x i => (structProj y i, fun _ dw' => (dw',0)) :=
by
  unfold revDerivProj
  simp (config:={zeta:=false}) [revDeriv.const_rule K _ _ y]
variable {W X}


theorem let_rule
  (f : W → X → Y → Z) (g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x,y) => f w x y)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDerivProj K I (fun (w : W) (x : X) => let y := g w x; f w x y)
    =
    fun w x i =>
      let ydg := revDeriv K (fun (wx : W×X) (_ : Unit) => g wx.1 wx.2) (w,x) ()
      let zdf := revDerivProj K I (fun w (xy : X×Y) => f w xy.1 xy.2) w (x,ydg.1) i
      (zdf.1,
       fun dz dw =>
         let dwxy := zdf.2 dz dw
         let dxy := ydg.2 dwxy.2.2 (dwxy.1,dwxy.2.1)
         dxy.1) :=
by
  unfold revDerivProj
  simp (config:={zeta:=false}) [revDeriv.let_rule _ f g hf hg]


-- variable {I}
-- theorem pi_rule
--   (f :  X → Y → (i : I) → EI i) (hf : ∀ i, HasAdjDiff K (fun (x,y) => f x y i))
--   : (revDerivProj K fun (x : X) (y : Y) (i : I) => f x y i)
--     =
--     fun x y =>
--       let xdf := revDerivProjProj K I (fun (x,y) (_:Unit) => f x y) (x,y) ()
--       (fun i => (xdf i).1,
--        fun df dx' =>
--          Function.repeatIdx (fun (i : I) dxy => ((xdf i).2 (df i) dxy).1) (dx',0)) :=
-- by
--   simp at hf
--   have _ := fun i => (hf i).1
--   have _ := fun i => (hf i).2
--   unfold revDerivProjProj revDerivProj
--   funext x y; fun_trans; fun_trans; simp
--   funext dw dx;
--   sorry_proof -- needs some relation between sum and repeatIdx
-- variable (I)

end revDerivProj


--------------------------------------------------------------------------------
-- Register `revCDeriv` as function transformation -----------------------------
--------------------------------------------------------------------------------
namespace revDeriv

open Fun_trans2

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


open Lean Meta Fun_trans2 in
def fun_transExt : Fun_trans2Ext where
  fun_trans2Name := ``revDeriv

  getFun? e :=
    if e.isAppOf ``revDeriv then

      if let .some f := e.getArg? 8 then
        some f
      else
        none
    else
      none

  replaceFun e f :=
    if e.isAppOf ``revDeriv then
      e.setArg 8 f
    else
      e

  id1Rule e W X := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``id1_rule #[K, W, X], origin := .decl ``id1_rule, rfl := false} ]
      discharger e

  id2Rule e W X := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``id2_rule #[K, W, X], origin := .decl ``id2_rule, rfl := false} ]
      discharger e

  constRule e W X y := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[K, W, X, y], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[K, f, g], origin := .decl ``let_rule, rfl := false} ]
      discharger e

  piRule e f := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[K, f], origin := .decl ``pi_rule, rfl := false} ]
      discharger e

  discharger := discharger

-- register revDeriv
open Lean in
#eval show CoreM Unit from do
  modifyEnv (λ env => Fun_trans2.fun_trans2Ext.addEntry env (``revDeriv, fun_transExt))


end revDeriv


--------------------------------------------------------------------------------
-- Register `revCDeriv` as function transformation -----------------------------
--------------------------------------------------------------------------------
namespace revDerivProj

open Fun_trans2

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


open Lean Meta Fun_trans2 in
def fun_transExt : Fun_trans2Ext where
  fun_trans2Name := ``revDerivProj

  getFun? e :=
    if e.isAppOf ``revDerivProj then

      if let .some f := e.getArg? 13 then
        some f
      else
        none
    else
      none

  replaceFun e f :=
    if e.isAppOf ``revDerivProj then
      e.setArg 13 f
    else
      e

  id1Rule e W X := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``id1_rule #[K, I, W, X], origin := .decl ``id1_rule, rfl := false} ]
      discharger e

  id2Rule e W X := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``id2_rule #[K, I, W, X], origin := .decl ``id2_rule, rfl := false} ]
      discharger e

  constRule e W X y := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[K, I, W, X, y], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some I := e.getArg? 1 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[K, I, f, g], origin := .decl ``let_rule, rfl := false} ]
      discharger e

  piRule e f := return none
    -- let .some K := e.getArg? 0 | return none
    -- tryTheorems
    --   #[ { proof := ← mkAppM ``pi_rule #[K, I, f], origin := .decl ``pi_rule, rfl := false} ]
    --   discharger e

  discharger := discharger

-- register revDerivProj
open Lean in
#eval show CoreM Unit from do
  modifyEnv (λ env => Fun_trans2.fun_trans2Ext.addEntry env (``revDerivProj, fun_transExt))


end revDerivProj



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
  -- {X' Xi : Type} {XI : Xi → Type} [StructType X' Xi XI] [EnumType Xi]
  -- {Y' Yi : Type} {YI : Yi → Type} [StructType Y' Yi YI] [EnumType Yi]
  -- {Z' Zi : Type} {ZI : Zi → Type} [StructType Z' Zi ZI] [EnumType Zi]
  -- [SemiInnerProductSpace K X'] [∀ i, SemiInnerProductSpace K (XI i)] [SemiInnerProductSpaceStruct K X' Xi XI]
  -- [SemiInnerProductSpace K Y'] [∀ i, SemiInnerProductSpace K (YI i)] [SemiInnerProductSpaceStruct K Y' Yi YI]
  -- [SemiInnerProductSpace K Z'] [∀ i, SemiInnerProductSpace K (ZI i)] [SemiInnerProductSpaceStruct K Z' Zi ZI]
  {W : Type} [SemiInnerProductSpace K W]
  -- {ι : Type} [EnumType ι]


--------------------------------------------------------------------------------



-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans2]
theorem Prod.mk.arg_fstsnd.revDeriv_rule
  (g : W → X → Y) (f : W → X → Z)
  (hg : HasAdjDiff K (fun (w,x) => g w x)) (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDeriv K (fun w x => (g w x, f w x))
    =
    fun w x =>
      let ydg := revDeriv K g w x
      let zdf := revDeriv K (fun (w,x) (_:Unit) => f w x) (w,x) ()
      ((ydg.1,zdf.1),
       fun dyz dw =>
         let dwx := ydg.2 dyz.1 dw
         (zdf.2 dyz.2 dwx).1) :=
by
  simp at hf hg
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv; simp; fun_trans; fun_trans; simp
  funext w x; simp
  funext (dy,dz) dw
  ext
  . simp[add_assoc]; sorry_proof
  . simp; sorry_proof


@[fun_trans2]
theorem Prod.mk.arg_fstsnd.revDerivProj_rule {ι κ : Type} [EnumType ι] [EnumType κ]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)]
  {ZI : κ → Type} [StructType Z κ ZI] [∀ i, SemiInnerProductSpace K (ZI i)]
  (g : W → X → Y) (f : W → X → Z)
  (hg : HasAdjDiff K (fun (w,x) => g w x)) (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDerivProj K (ι⊕κ) (fun w x => (g w x, f w x))
    =
    fun w x i =>
      match i with
      | .inl j =>
        let ydg := revDerivProj K ι g w x j
        (ydg.1, fun dy dw => ydg.2 dy dw)
      | .inr j =>
        let zdf := revDerivProj K κ f w x j
        (zdf.1, fun dz dw => zdf.2 dz dw) :=
by
  simp at hf hg
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivProj
  simp[Prod.mk.arg_fstsnd.revDeriv_rule _ _ hg hf]
  funext w x i
  cases i
  case inl =>
    simp[revDeriv, oneHot, structMake]; funext dyi dw;
    ext <;> (simp; congr; funext i; congr; funext h; subst h; rfl)
  case inr =>
    simp[revDeriv, oneHot, structMake]; funext dyi dw; fun_trans; fun_trans
    sorry_proof


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans2]
theorem Prod.fst.arg_self.revDeriv_rule
  (f : W → X → Y×Z)
  (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDeriv K (fun w x => (f w x).1)
    =
    fun w x =>
      let zdf := revDerivProj K (Unit⊕Unit) f w x (.inl ())
      zdf :=
by
  have ⟨_,_⟩ := hf
  unfold revDerivProj revDeriv
  fun_trans; fun_trans; simp

@[fun_trans2]
theorem Prod.fst.arg_self.revDerivProj_rule {ι} [EnumType ι]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)]
  (f : W → X → Y×Z)
  (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDerivProj K ι (fun x y => (f x y).1)
    =
    fun w x i =>
      let zdf := revDerivProj K (ι⊕Unit) f w x (.inl i)
      zdf :=
by
  have ⟨_,_⟩ := hf
  unfold revDerivProj revDeriv
  fun_trans; fun_trans; simp


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans2]
theorem Prod.snd.arg_self.revDeriv_rule
  (f : W → X → Y×Z)
  (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDeriv K (fun x y => (f x y).2)
    =
    fun w x =>
      let zdf := revDerivProj K (Unit⊕Unit) f w x (.inr ())
      zdf :=
by
  have ⟨_,_⟩ := hf
  unfold revDerivProj revDeriv
  fun_trans; fun_trans; simp

@[fun_trans2]
theorem Prod.snd.arg_self.revDerivProj_rule {ι} [EnumType ι]
  {ZI : ι → Type} [StructType Z ι ZI] [∀ i, SemiInnerProductSpace K (ZI i)]
  (f : W → X → Y×Z)
  (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDerivProj K ι (fun w x => (f w x).2)
    =
    fun w x i =>
      let zdf := revDerivProj K (Unit⊕ι) f w x (.inr i)
      zdf :=
by
  have ⟨_,_⟩ := hf
  unfold revDerivProj revDeriv
  fun_trans; fun_trans; simp




example
  (f : W → X → X)
  (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDeriv K (fun w x =>
      let y := f w x
      let z := f w y
      z)
    =
    sorry :=
by
  set_option trace.Meta.Tactic.fun_trans.step true in
  set_option trace.Meta.Tactic.simp.rewrite true in
  set_option trace.Meta.Tactic.simp.discharge true in
  set_option trace.Meta.Tactic.simp.unify true in
  set_option pp.funBinderTypes true in
  fun_trans2


example
  (f : W → X → X)
  (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDeriv K (fun (w:W×W) x =>
      let y := f w.1 x
      let z := f w.2 y
      z)
    =
    sorry :=
by
  set_option trace.Meta.Tactic.fun_trans.step true in
  set_option trace.Meta.Tactic.simp.rewrite true in
  set_option trace.Meta.Tactic.simp.discharge true in
  set_option trace.Meta.Tactic.simp.unify true in
  set_option pp.funBinderTypes true in
  fun_trans2



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans2]
theorem HAdd.hAdd.arg_a0a1.revDeriv_rule
  (f g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv K (fun w x => f w x + g w x)
    =
    fun w x =>
      let adf := revDeriv K f w x
      let bdg := revDeriv K (fun wx (_ : Unit) => g wx.1 wx.2) (w,x) ()
      (adf.1 + bdg.1,
       fun dy dw =>
         let dwx := adf.2 dy dw
         let dwx := bdg.2 dy dwx
         dwx.1) :=
by
  simp at hf hg
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv
  fun_trans; fun_trans; simp[add_assoc]
  funext w x; simp; funext dy dw
  ext
  . simp[add_assoc,add_comm]; sorry_proof
  . simp[add_assoc,add_comm]; sorry_proof


@[fun_trans2]
theorem HAdd.hAdd.arg_a0a1.revDerivProj_rule {ι} [EnumType ι]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)]
  (f g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDerivProj K ι (fun w x => f w x + g w x)
    =
    fun w x i =>
      let adf := revDerivProj K ι f w x i
      let bdg := revDerivProj K ι (fun xy (_ : Unit) => g xy.1 xy.2) (w,x) () i
      (adf.1 + bdg.1,
       fun dy dw =>
         let dwx := adf.2 dy dw
         let dwx := bdg.2 dy dwx
         dwx.1) :=
by
  simp at hf hg
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivProj
  simp only [HAdd.hAdd.arg_a0a1.revDeriv_rule _ _ hf hg]
  funext w x i; simp[revDeriv]


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans2]
theorem HSub.hSub.arg_a0a1.revDeriv_rule
  (f g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv K (fun w x => f w x - g w x)
    =
    fun w x =>
      let adf := revDeriv K f w x
      let bdg := revDeriv K (fun wx (_ : Unit) => g wx.1 wx.2) (w,x) ()
      (adf.1 - bdg.1,
       fun dy dw =>
         let dwx := adf.2 dy dw
         let dwx := bdg.2 (-dy) dwx
         dwx.1) :=
by
  simp at hf hg
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv
  fun_trans; fun_trans;
  funext w x; simp; funext dy dw
  ext
  . simp[add_assoc,neg_pull]; sorry_proof
  . simp[add_assoc,neg_pull]; sorry_proof


@[fun_trans2]
theorem HSub.hSub.arg_a0a1.revDerivProj_rule {ι} [EnumType ι]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)]
  (f g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDerivProj K ι (fun w x => f w x - g w x)
    =
    fun w x i =>
      let adf := revDerivProj K ι f w x i
      let bdg := revDerivProj K ι (fun xy (_ : Unit) => g xy.1 xy.2) (w,x) () i
      (adf.1 - bdg.1,
       fun dy dw =>
         let dwx := adf.2 dy dw
         let dwx := bdg.2 (-dy) dwx
         dwx.1) :=
by
  simp at hf hg
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivProj
  simp only [HSub.hSub.arg_a0a1.revDeriv_rule _ _ hf hg]
  funext w x i; simp[revDeriv,neg_pull]


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans2]
theorem Neg.neg.arg_a0.revDeriv_rule
  (f : W → X → Y)
  : (revDeriv K fun w x => - f w x)
    =
    fun w x =>
      let ydf := revDeriv K f w x
      (-ydf.1,
       fun dy dw =>
         let dwx := ydf.2 (-dy) dw
         dwx) :=
by
  unfold revDeriv; simp; fun_trans; fun_trans; simp[neg_pull]


@[fun_trans2]
theorem Neg.neg.arg_a0.revDerivProj_rule {ι} [EnumType ι]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)]
  (f : W → X → Y)
  : (revDerivProj K ι fun w x => - f w x)
    =
    fun w x i =>
      let ydf := revDerivProj K ι f w x i
      (-ydf.1,
       fun dy dw =>
         let dwx := ydf.2 (-dy) dw
         dwx) :=
by
  unfold revDerivProj revDeriv; simp; fun_trans; fun_trans; simp[neg_pull]



-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate

@[fun_trans2]
theorem HMul.hMul.arg_a0a1.revDeriv_rule
  (f g : W → X → K)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv K (fun w x => f w x * g w x)
    =
    fun w x =>
      let adf := revDeriv K f w x
      let bdg := revDeriv K (fun wx (_ : Unit) => g wx.1 wx.2) (w,x) ()
      (adf.1 * bdg.1,
       fun dz dw =>
         let dwx := adf.2 (conj bdg.1 * dz) dw
         let dwx := bdg.2 (conj adf.1 * dz) dwx
         dwx.1) :=
by
  simp at hf hg
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv
  fun_trans; fun_trans; simp[mul_assoc]
  funext w w; simp; funext dx dw
  simp[mul_assoc,mul_comm,smul_push,add_assoc]
  ext
  . simp[smul_push]; sorry_proof
  . simp[smul_push]; sorry_proof

@[fun_trans2]
theorem HMul.hMul.arg_a0a1.revDerivProj_rule
  (f g : W → X → K)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDerivProj K Unit (fun w x => f w x * g w x)
    =
    fun w x _ =>
      let adf := revDeriv K f w x
      let bdg := revDeriv K (fun wx (_ : Unit) => g wx.1 wx.2) (w,x) ()
      (adf.1 * bdg.1,
       fun dz dw =>
         let dwx := adf.2 (conj bdg.1 * dz) dw
         let dwx := bdg.2 (conj adf.1 * dz) dwx
         dwx.1) :=
by
  unfold revDerivProj
  simp only [HMul.hMul.arg_a0a1.revDeriv_rule _ _ hf hg]
  funext w x i; simp[revDeriv, oneHot]



-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans2]
theorem HSMul.hSMul.arg_a0a1.revDeriv_rule
  {Y : Type} [SemiHilbert K Y]
  (f : W → X → K) (g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : (revDeriv K fun w x => f w x • g w x)
    =
    fun w x =>
      let ydf := revDeriv K f w x
      let zdg := revDeriv K (fun wx (_:Unit) => g wx.1 wx.2) (w,x) ()
      (ydf.1 • zdg.1,
       fun dy dw =>
         let dk := inner zdg.1 dy
         let dwx := ydf.2 dk dw
         let dy := (conj ydf.1) • dy
         let dwx := zdg.2 dy dwx
         dwx.1) :=
by
  simp at hf hg
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv; simp; fun_trans; fun_trans
  funext w x; simp
  funext dy dw'
  ext
  . simp[smul_pull,add_comm,add_assoc]; sorry_proof
  . simp[smul_pull,add_comm]; sorry_proof


@[fun_trans2]
theorem HSMul.hSMul.arg_a0a1.revDerivProj_rule {ι} [EnumType ι]
  {Y : Type} [SemiHilbert K Y]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)] [SemiInnerProductSpaceStruct K Y ι YI]
  (f : W → X → K) (g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : (revDerivProj K ι fun w x => f w x • g w x)
    =
    fun w x i =>
      let ydf := revDeriv K f w x
      let zdg := revDerivProj K ι (fun wx (_:Unit) => g wx.1 wx.2) (w,x) () i
      (ydf.1 • zdg.1,
       fun dy dw =>
         let dk := inner zdg.1 dy
         let dwx := ydf.2 dk dw
         let dy := (conj ydf.1) • dy
         let dwx := zdg.2 dy dwx
         dwx.1) :=
by
  simp at hf hg
  unfold revDerivProj
  simp only [HSMul.hSMul.arg_a0a1.revDeriv_rule _ _ hf hg]
  funext w x i; simp
  funext dyi dw; simp[structMake,revDeriv,structProj,add_assoc]
  sorry_proof


#exit

-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
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
  unfold revDeriv; simp; fun_trans; fun_trans
  simp[revDerivUpdate,smul_push,neg_pull,revDeriv,smul_add,smul_sub, ← sub_eq_add_neg]

@[fun_trans]
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
  simp[revDerivUpdate]; fun_trans
  simp[revDerivUpdate,smul_push,neg_pull,revDeriv,smul_add,smul_sub,add_assoc,mul_assoc]

@[fun_trans]
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
  fun_trans; simp[oneHot, structMake]

@[fun_trans]
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
  fun_trans; simp[revDerivUpdate,revDeriv,add_assoc,neg_pull,mul_assoc,smul_push]


-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
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
  unfold revDeriv; simp; funext dx; fun_trans; fun_trans; simp[smul_push,smul_smul]; ring_nf

@[fun_trans]
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
  funext x; fun_trans; simp[mul_assoc,mul_comm,add_assoc]

@[fun_trans]
def HPow.hPow.arg_a0.revDerivProj_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f)
  : revDerivProj K Unit (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revDeriv K f x
      let y' := (n : K) * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n, fun _ dx' => ydf.2 (y' * dx')) :=
by
  unfold revDerivProj; fun_trans; simp[oneHot,structMake]

@[fun_trans]
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
  unfold revDerivProjUpdate; fun_trans; simp[oneHot,structMake,revDerivUpdate]


-- EnumType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
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


@[fun_trans]
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
  fun_trans
  sorry_proof


@[fun_trans]
theorem SciLean.EnumType.sum.arg_f.revDerivProj_rule {ι : Type} [EnumType ι]
  (f : X → ι → Y') (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDerivProj K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := fun i => revDerivProjUpdate K Yi (f · i) x
      (∑ i, (ydf i).1,
       fun j dy => Function.repeatIdx (fun (i : ι) dx => (ydf i).2 j dy dx) 0) :=
by
  funext; simp[revDerivProj]; fun_trans; sorry_proof


@[fun_trans]
theorem SciLean.EnumType.sum.arg_f.revDerivProjUpdate_rule {ι : Type} [EnumType ι]
  (f : X → ι → Y') (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDerivProjUpdate K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := fun i => revDerivProjUpdate K Yi (f · i) x
      (∑ i, (ydf i).1,
       fun j dy dx => Function.repeatIdx (fun (i : ι) dx => (ydf i).2 j dy dx) dx) :=
by
  funext; simp[revDerivProjUpdate]; fun_trans; sorry_proof


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
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

@[fun_trans]
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

@[fun_trans]
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

@[fun_trans]
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


@[fun_trans]
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

@[fun_trans]
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

@[fun_trans]
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

@[fun_trans]
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

@[fun_trans]
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
  fun_trans only; simp
  fun_trans; simp[smul_pull]

@[fun_trans]
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
  fun_trans; simp[revDerivUpdate,add_assoc]

@[fun_trans]
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
  fun_trans; simp[oneHot, structMake]

@[fun_trans]
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
  fun_trans; simp[revDerivUpdate,add_assoc]



-- norm2 -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
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
  fun_trans only
  simp
  fun_trans
  simp[smul_smul]

@[fun_trans]
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
  fun_trans only; simp[revDeriv,smul_pull]


@[fun_trans]
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
  fun_trans; simp[oneHot,structMake]

@[fun_trans]
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
  fun_trans only; simp[revDeriv,revDerivUpdate,smul_pull]


-- norm₂ -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
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
  fun_trans only
  simp
  fun_trans
  funext dr; simp[smul_smul]

@[fun_trans]
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
  fun_trans only
  simp
  fun_trans
  funext dr; simp[revDeriv,smul_pull]

@[fun_trans]
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
  fun_trans only; simp[oneHot, structMake]

@[fun_trans]
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
  fun_trans only; simp[revDeriv,revDerivUpdate,smul_pull]

end InnerProductSpace
