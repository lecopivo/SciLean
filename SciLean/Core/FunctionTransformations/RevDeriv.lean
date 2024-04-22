import SciLean.Core.FunctionPropositions.HasAdjDiff
import SciLean.Core.FunctionTransformations.SemiAdjoint
import SciLean.Core.FunctionSpaces.SmoothLinearMap

import SciLean.Data.StructType.Algebra

set_option linter.unusedVariables false

open LeanColls

namespace SciLean

variable
  (K I : Type _) [RCLike K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {κ : Type _} [IndexType κ] [LawfulIndexType κ] [DecidableEq κ]
  {E : Type _} {EI : I → Type _}
  [StructType E I EI] [IndexType I] [LawfulIndexType I] [DecidableEq I]
  [SemiInnerProductSpace K E] [∀ i, SemiInnerProductSpace K (EI i)]
  [SemiInnerProductSpaceStruct K E I EI]
  {F J : Type _} {FJ : J → Type _}
  [StructType F J FJ] [IndexType J] [LawfulIndexType J] [DecidableEq J]
  [SemiInnerProductSpace K F] [∀ j, SemiInnerProductSpace K (FJ j)]
  [SemiInnerProductSpaceStruct K F J FJ]


@[fun_trans]
noncomputable
def revDeriv
  (f : X → Y) (x : X) : Y×(Y→X) :=
  (f x, semiAdjoint K (cderiv K f x))

@[fun_trans]
noncomputable
def revDerivUpdate
  (f : X → Y) (x : X) : Y×(Y→X→X) :=
  let ydf := revDeriv K f x
  (ydf.1, fun dy dx => dx + ydf.2 dy)

@[fun_trans]
noncomputable
def revDerivProj [DecidableEq I]
  (f : X → E) (x : X) : E×((i : I)→EI i→X) :=
  let ydf' := revDeriv K f x
  (ydf'.1, fun i de =>
    ydf'.2 (oneHot i de))

@[fun_trans]
noncomputable
def revDerivProjUpdate [DecidableEq I]
  (f : X → E) (x : X) : E×((i : I)→EI i→X→X) :=
  let ydf' := revDerivProj K I f x
  (ydf'.1, fun i de dx => dx + ydf'.2 i de)


noncomputable
abbrev revDeriv' (f : X → Y) (x : X) : Y×(Y ⊸[K] X) :=
  let ydf := revDeriv K f x
  (ydf.1, ⟨fun dy => ydf.2 dy, by simp (config:={zetaDelta:=true}) [revDeriv]; fun_prop⟩)


noncomputable
abbrev gradient (f : X → Y) (x : X) : (Y → X):= (revDeriv K f x).2

noncomputable
abbrev scalarGradient (f : X → K) (x : X) : X := (revDeriv K f x).2 1


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

@[fun_trans]
theorem id_rule :
    revDeriv K (fun x : X => x) = fun x => (x, fun dx => dx) := by
  unfold revDeriv
  fun_trans

@[fun_trans]
theorem const_rule (y : Y) :
    revDeriv K (fun _ : X => y) = fun x => (y, fun _ => 0) := by
  unfold revDeriv
  fun_trans

@[fun_trans]
theorem comp_rule
    (f : Y → Z) (g : X → Y)
    (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    revDeriv K (fun x : X => f (g x))
    =
    fun x =>
      let ydg := revDeriv K g x
      let zdf := revDeriv K f ydg.1
      (zdf.1,
       fun dz =>
         let dy := zdf.2 dz
         ydg.2 dy)  := by
  unfold revDeriv
  fun_trans


example
    (f : X → Y → Z) (g : X → Y)
    -- (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g) :
    (hf : HasAdjDiff K ↿f) (hg : HasAdjDiff K g) :
    HasSemiAdjoint K fun dx => SciLean.cderiv K (fun xy => f xy.1 xy.2) (x, g x) dx := by fun_prop

example (f : X → Y → Z) (hf : HasAdjDiff K ↿f) :
   HasAdjDiff K (fun xy : X×Y => f xy.1 xy.2) := by fun_prop

@[fun_trans]
theorem let_rule
    (f : X → Y → Z) (g : X → Y)
    (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g) :
    -- todo: for some reason `fun_prop` does not see (hf : HasAdjDiff K ↿f)
    -- (hf : HasAdjDiff K ↿f) (hg : HasAdjDiff K g) :
    revDeriv K (fun x : X => let y := g x; f x y)
    =
    fun x =>
      let ydg := revDerivUpdate K g x
      let zdf := revDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz =>
         let dxdy := zdf.2 dz
         let dx := ydg.2 dxdy.2 dxdy.1
         dx)  := by
  unfold revDerivUpdate revDeriv
  fun_trans

@[fun_trans]
theorem apply_rule (i : I) :
    revDeriv K (fun (x : (i:I) → EI i) => x i)
    =
    fun x =>
      (x i, fun dxi => oneHot i dxi) := by
  unfold revDeriv
  fun_trans; simp[oneHot]

@[fun_trans]
theorem pi_rule
    (f :  X → (i : I) → EI i) (hf : ∀ i, HasAdjDiff K (f · i)) :
    (revDeriv K fun (x : X) (i : I) => f x i)
    =
    fun x =>
      let xdf := fun i => revDerivUpdate K (f · i) x
      (fun i => (xdf i).1,
       fun dy =>
         Fold.fold (IndexType.univ I) (fun dx i => (xdf i).2 (dy i) dx) 0) := by
  unfold revDeriv
  fun_trans;
  funext x; simp
  rw[cderiv.pi_rule (hf:=by fun_prop)]; fun_trans
  simp[revDerivUpdate,revDeriv,IndexType.sum]

end revDeriv


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDerivUpdate ------------------------------------
--------------------------------------------------------------------------------

namespace revDerivUpdate

@[fun_trans]
theorem id_rule :
    revDerivUpdate K (fun x : X => x) = fun x => (x, fun dx' dx => dx + dx') := by
  unfold revDerivUpdate
  fun_trans

@[fun_trans]
theorem const_rule (y : Y) :
    revDerivUpdate K (fun _ : X => y) = fun x => (y, fun _ dx => dx) := by
  unfold revDerivUpdate
  fun_trans

@[fun_trans]
theorem comp_rule
    (f : Y → Z) (g : X → Y)
    (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    revDerivUpdate K (fun x : X => f (g x))
    =
    fun x =>
      let ydg := revDerivUpdate K g x
      let zdf := revDeriv K f ydg.1
      (zdf.1,
       fun dz dx =>
         let dy := zdf.2 dz
         ydg.2 dy dx)  := by
  unfold revDerivUpdate
  fun_trans

@[fun_trans]
theorem let_rule
    (f : X → Y → Z) (g : X → Y)
    (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g) :
    revDerivUpdate K (fun x : X => let y := g x; f x y)
    =
    fun x =>
      let ydg := revDerivUpdate K g x
      let zdf := revDerivUpdate K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz dx =>
         let dxdy := zdf.2 dz (dx, 0)
         let dx := ydg.2 dxdy.2 dxdy.1
         dx)  := by
  unfold revDerivUpdate
  fun_trans [revDerivUpdate,add_assoc]

@[fun_trans]
theorem apply_rule (i : I) :
    revDerivUpdate K (fun (x : (i:I) → EI i) => x i)
    =
    fun x =>
      (x i, fun dxi dx => structModify i (fun dxi' => dxi' + dxi) dx) := by
  unfold revDerivUpdate
  fun_trans

@[fun_trans]
theorem pi_rule
    (f :  X → (i : I) → EI i) (hf : ∀ i, HasAdjDiff K (f · i)) :
    (revDerivUpdate K fun (x : X) (i : I) => f x i)
    =
    fun x =>
      let xdf := fun i => revDerivUpdate K (f · i) x
      (fun i => (xdf i).1,
       fun dy dx =>
         Fold.fold (IndexType.univ I) (fun dx i => (xdf i).2 (dy i) dx) dx) := by
  unfold revDerivUpdate
  funext x
  rw[revDeriv.pi_rule (hf:=by fun_prop)]
  simp
  sorry_proof


end revDerivUpdate


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDerivProj ------------------------------------
--------------------------------------------------------------------------------

namespace revDerivProj

@[fun_trans]
theorem id_rule :
    revDerivProj K I (fun x : E => x)
    =
    fun x =>
      (x,
       fun i de =>
         oneHot i de) := by
  unfold revDerivProj; fun_trans

@[fun_trans]
theorem const_rule (x : E)
  : revDerivProj K I (fun _ : Y => x)
    =
    fun _ =>
      (x,
       fun i (de : EI i) => 0) := by
  unfold revDerivProj; fun_trans

@[fun_trans]
theorem apply_rule [DecidableEq I] (i : ι) :
    revDerivProj K I (fun (f : ι → E) => f i)
    =
    fun f : ι → E =>
      (f i, fun j dxj => oneHot (X:=ι→E) (I:=ι×I) (i,j) dxj) :=
by
  unfold revDerivProj;
  fun_trans; simp[oneHot]
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

@[fun_trans]
theorem comp_rule
    (f : Y → E) (g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    revDerivProj K I (fun x => f (g x))
    =
    fun x =>
      let ydg' := revDeriv K g x
      let zdf' := revDerivProj K I f ydg'.1
      (zdf'.1,
       fun i de =>
         ydg'.2 (zdf'.2 i de)) := by
  unfold revDerivProj; fun_trans

@[fun_trans]
theorem let_rule
    (f : X → Y → E) (g : X → Y)
    (hf : HasAdjDiff K (fun (x,y) => f x y)) (hg : HasAdjDiff K g) :
    revDerivProj K I (fun x => let y := g x; f x y)
    =
    fun x =>
      let ydg' := revDerivUpdate K g x
      let zdf' := revDerivProj K I (fun (x,y) => f x y) (x,ydg'.1)
      (zdf'.1,
       fun i dei =>
         let dxy := zdf'.2 i dei
         ydg'.2 dxy.2 dxy.1) := by
  unfold revDerivProj; fun_trans

@[fun_trans]
theorem pi_rule
    (f :  X → ι → Y) (hf : ∀ i, HasAdjDiff K (f · i)) :
    (revDerivProj K Unit fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let ydf := fun i => revDerivUpdate K (f · i) x
      (fun i => (ydf i).1,
       fun _ df =>
         Fold.fold (IndexType.univ ι) (fun dx i => (ydf i).2 (df i) dx) (0 : X)) := by
  unfold revDerivProj
  fun_trans
  funext x; simp; funext i de
  rw[revDeriv.pi_rule (hf:=by fun_prop)]; simp[oneHot]

end revDerivProj


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDerivProjUpdate --------------------------------
--------------------------------------------------------------------------------

namespace revDerivProjUpdate

@[fun_trans]
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

@[fun_trans]
theorem const_rule (x : E)
  : revDerivProjUpdate K I (fun _ : Y => x)
    =
    fun _ =>
      (x,
       fun i de dx => dx) :=
by
  unfold revDerivProjUpdate; simp[revDerivProj.const_rule]

@[fun_trans]
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

@[fun_trans]
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

@[fun_trans]
theorem apply_rule [DecidableEq I] (i : ι)
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
  unfold revDerivProjUpdate
  fun_trans
  funext j dxj f i'
  apply structExt (I:=I)
  intro j'
  if h :i'=i then
    subst h; simp
  else
    have h' : i≠i' := by intro h''; simp[h''] at h
    simp[h,h',Function.update]

@[fun_trans]
theorem pi_rule
    (f :  X → ι → Y) (hf : ∀ i, HasAdjDiff K (f · i)) :
    (revDerivProjUpdate K Unit fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let ydf := fun i => revDerivUpdate K (f · i) x
      (fun i => (ydf i).1,
       fun _ df dx =>
         Fold.fold (IndexType.univ ι) (fun dx i => (ydf i).2 (df i) dx) dx) :=
by
  unfold revDerivProjUpdate
  fun_trans
  unfold revDerivProj
  funext x; simp; funext i de dx
  rw[revDeriv.pi_rule (hf:=by fun_prop)]; simp[oneHot,revDerivUpdate]
  sorry_proof


end revDerivProjUpdate


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

end SciLean
open SciLean

variable
  {K : Type} [RCLike K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {X' Xi : Type} {XI : Xi → Type} [StructType X' Xi XI] [IndexType Xi] [LawfulIndexType Xi] [DecidableEq Xi]
  {Y' Yi : Type} {YI : Yi → Type} [StructType Y' Yi YI] [IndexType Yi] [LawfulIndexType Yi] [DecidableEq Yi]
  {Z' Zi : Type} {ZI : Zi → Type} [StructType Z' Zi ZI] [IndexType Zi] [LawfulIndexType Zi] [DecidableEq Zi]
  [SemiInnerProductSpace K X'] [∀ i, SemiInnerProductSpace K (XI i)] [SemiInnerProductSpaceStruct K X' Xi XI]
  [SemiInnerProductSpace K Y'] [∀ i, SemiInnerProductSpace K (YI i)] [SemiInnerProductSpaceStruct K Y' Yi YI]
  [SemiInnerProductSpace K Z'] [∀ i, SemiInnerProductSpace K (ZI i)] [SemiInnerProductSpaceStruct K Z' Zi ZI]
  {W : Type} [SemiInnerProductSpace K W]
  {ι : Type} [IndexType ι] [LawfulIndexType ι]



-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.mk.arg_fstsnd.revDeriv_rule
    (g : X → Y) (f : X → Z) (hg : HasAdjDiff K g) (hf : HasAdjDiff K f) :
    revDeriv K (fun x => (g x, f x))
    =
    fun x =>
      let ydg := revDeriv K g x
      let zdf := revDerivUpdate K f x
      ((ydg.1,zdf.1),
       fun dyz =>
         let dx := ydg.2 dyz.1
         zdf.2 dyz.2 dx) := by
  unfold revDerivUpdate; unfold revDeriv; simp; fun_trans

@[fun_trans]
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
  unfold revDerivUpdate; fun_trans; simp[add_assoc, revDerivUpdate]

@[fun_trans]
theorem Prod.mk.arg_fstsnd.revDerivProj_rule
    (g : X → Y') (f : X → Z')
    (hg : HasAdjDiff K g) (hf : HasAdjDiff K f) :
    revDerivProj K (Yi⊕Zi) (fun x => (g x, f x))
    =
    fun x =>
      let ydg := revDerivProj K Yi g x
      let zdf := revDerivProj K Zi f x
      ((ydg.1,zdf.1),
       fun i dyz =>
         match i with
         | .inl j => ydg.2 j dyz
         | .inr j => zdf.2 j dyz) := by
  unfold revDerivProj
  funext x; fun_trans; simp[revDerivUpdate]
  funext i dyz
  induction i <;>
    { simp[oneHot,structMake]
      apply congr_arg
      congr; funext i; congr; funext h
      subst h; rfl
    }

@[fun_trans]
theorem Prod.mk.arg_fstsnd.revDerivProjUpdate_rule
    (g : X → Y') (f : X → Z')
    (hg : HasAdjDiff K g) (hf : HasAdjDiff K f) :
    revDerivProjUpdate K (Yi⊕Zi) (fun x => (g x, f x))
    =
    fun x =>
      let ydg := revDerivProjUpdate K Yi g x
      let zdf := revDerivProjUpdate K Zi f x
      ((ydg.1,zdf.1),
       fun i dyz dx =>
         match i with
         | .inl j => ydg.2 j dyz dx
         | .inr j => zdf.2 j dyz dx) := by
  unfold revDerivProjUpdate
  funext x; fun_trans
  funext i de dx
  induction i <;> simp


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.fst.arg_self.revDeriv_rule
    (f : X → Y×Z) (hf : HasAdjDiff K f) :
    revDeriv K (fun x => (f x).1)
    =
    fun x =>
      let yzdf := revDerivProj K (Unit⊕Unit) f x
      (yzdf.1.1, fun dy => yzdf.2 (.inl ()) dy) := by
  unfold revDerivProj; unfold revDeriv
  fun_trans

@[fun_trans]
theorem Prod.fst.arg_self.revDerivUpdate_rule
    (f : X → Y×Z) (hf : HasAdjDiff K f) :
    revDerivUpdate K (fun x => (f x).1)
    =
    fun x =>
      let yzdf := revDerivProjUpdate K (Unit⊕Unit) f x
      (yzdf.1.1, fun dy dx => yzdf.2 (.inl ()) dy dx) := by
  unfold revDerivProjUpdate; unfold revDerivUpdate;
  fun_trans

@[fun_trans]
theorem Prod.fst.arg_self.revDerivProj_rule
    (f : W → X'×Y) (hf : HasAdjDiff K f) :
    revDerivProj K Xi (fun x => (f x).1)
    =
    fun w =>
      let xydf := revDerivProj K (Xi⊕Unit) f w
      (xydf.1.1,
       fun i dxy => xydf.2 (.inl i) dxy) := by
  unfold revDerivProj
  funext x; fun_trans[revDerivProj]

@[fun_trans]
theorem Prod.fst.arg_self.revDerivProjUpdate_rule
    (f : W → X'×Y) (hf : HasAdjDiff K f) :
    revDerivProjUpdate K Xi (fun x => (f x).1)
    =
    fun w =>
      let xydf := revDerivProjUpdate K (Xi⊕Unit) f w
      (xydf.1.1,
       fun i dxy dw => xydf.2 (.inl i) dxy dw) := by
  unfold revDerivProjUpdate
  funext x; fun_trans


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.snd.arg_self.revDeriv_rule
    (f : X → Y×Z) (hf : HasAdjDiff K f) :
    revDeriv K (fun x => (f x).2)
    =
    fun x =>
      let yzdf := revDerivProj K (Unit⊕Unit) f x
      (yzdf.1.2, fun dy => yzdf.2 (.inr ()) dy) := by
  unfold revDerivProj; unfold revDeriv
  fun_trans

@[fun_trans]
theorem Prod.snd.arg_self.revDerivUpdate_rule
    (f : X → Y×Z) (hf : HasAdjDiff K f) :
    revDerivUpdate K (fun x => (f x).2)
    =
    fun x =>
      let yzdf := revDerivProjUpdate K (Unit⊕Unit) f x
      (yzdf.1.2, fun dy dx => yzdf.2 (.inr ()) dy dx) := by
  unfold revDerivProjUpdate; unfold revDerivUpdate
  fun_trans

@[fun_trans]
theorem Prod.snd.arg_self.revDerivProj_rule
    (f : W → X×Y') (hf : HasAdjDiff K f) :
    revDerivProj K Yi (fun x => (f x).2)
    =
    fun w =>
      let xydf := revDerivProj K (Unit⊕Yi) f w
      (xydf.1.2,
       fun i dxy => xydf.2 (.inr i) dxy) := by
  unfold revDerivProj
  funext x; fun_trans[revDerivProj]

@[fun_trans]
theorem Prod.snd.arg_self.revDerivProjUpdate_rule
    (f : W → X×Y') (hf : HasAdjDiff K f) :
    revDerivProjUpdate K Yi (fun x => (f x).2)
    =
    fun w =>
      let xydf := revDerivProjUpdate K (Unit⊕Yi) f w
      (xydf.1.2,
       fun i dxy dw => xydf.2 (.inr i) dxy dw) := by
  unfold revDerivProjUpdate
  funext x; fun_trans


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revDeriv_rule
    (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDeriv K fun x => f x + g x)
    =
    fun x =>
      let ydf := revDeriv K f x
      let ydg := revDerivUpdate K g x
      (ydf.1 + ydg.1,
       fun dy =>
         let dx := ydf.2 dy
         ydg.2 dy dx) := by
  unfold revDerivUpdate; unfold revDeriv; simp; fun_trans

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revDerivUpdate_rule
    (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivUpdate K fun x => f x + g x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let ydg := revDerivUpdate K g x
      (ydf.1 + ydg.1,
       fun dy dx =>
         let dx := ydf.2 dy dx
         ydg.2 dy dx) := by
  unfold revDerivUpdate
  fun_trans; funext x; simp[add_assoc,revDerivUpdate]

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revDerivProj_rule
    (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivProj K Yi fun x => f x + g x)
    =
    fun x =>
      let ydf := revDerivProj K Yi f x
      let ydg := revDerivProjUpdate K Yi g x
      (ydf.1 + ydg.1,
       fun i dy =>
         let dx := ydf.2 i dy
         (ydg.2 i dy dx)) := by
  unfold revDerivProjUpdate; unfold revDerivProj
  fun_trans; simp[revDerivUpdate]

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revDerivProjUpdate_rule
    (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivProjUpdate K Yi fun x => f x + g x)
    =
    fun x =>
      let ydf := revDerivProjUpdate K Yi f x
      let ydg := revDerivProjUpdate K Yi g x
      (ydf.1 + ydg.1,
       fun i dy dx =>
         let dx := ydf.2 i dy dx
         ydg.2 i dy dx) := by
  unfold revDerivProjUpdate
  fun_trans; simp[revDerivProjUpdate, add_assoc]


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSub.hSub.arg_a0a1.revDeriv_rule
    (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDeriv K fun x => f x - g x)
    =
    fun x =>
      let ydf := revDeriv K f x
      let ydg := revDerivUpdate K g x
      (ydf.1 - ydg.1,
       fun dy =>
         let dx := ydf.2 dy
         let dy' := -dy
         ydg.2 dy' dx) := by
  unfold revDerivUpdate; unfold revDeriv;
  fun_trans
  funext x; simp; funext dy; simp only [neg_pull, ← sub_eq_add_neg]

@[fun_trans]
theorem HSub.hSub.arg_a0a1.revDerivUpdate_rule
    (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivUpdate K fun x => f x - g x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let ydg := revDerivUpdate K g x
      (ydf.1 - ydg.1,
       fun dy dx =>
         let dx := ydf.2 dy dx
         let dy' := -dy
         ydg.2 dy' dx) := by
  unfold revDerivUpdate
  fun_trans; funext x; simp[add_assoc,revDerivUpdate]

@[fun_trans]
theorem HSub.hSub.arg_a0a1.revDerivProj_rule
    (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivProj K Yi fun x => f x - g x)
    =
    fun x =>
      let ydf := revDerivProj K Yi f x
      let ydg := revDerivProjUpdate K Yi g x
      (ydf.1 - ydg.1,
       fun i dy =>
         let dx := ydf.2 i dy
         let dy' := -dy
         (ydg.2 i dy' dx)) := by
  unfold revDerivProjUpdate; unfold revDerivProj
  fun_trans; simp[revDerivUpdate, neg_pull,revDeriv]


@[fun_trans]
theorem HSub.hSub.arg_a0a1.revDerivProjUpdate_rule
    (f g : X → Y') (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivProjUpdate K Yi fun x => f x - g x)
    =
    fun x =>
      let ydf := revDerivProjUpdate K Yi f x
      let ydg := revDerivProjUpdate K Yi g x
      (ydf.1 - ydg.1,
       fun i dy dx =>
         let dx := ydf.2 i dy dx
         let dy' := -dy
         ydg.2 i dy' dx) := by
  unfold revDerivProjUpdate
  fun_trans; simp[revDerivProjUpdate, neg_pull, revDerivProj, revDeriv,add_assoc]


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.revDeriv_rule
    (f : X → Y) (x : X) :
    (revDeriv K fun x => - f x) x
    =
    let ydf := revDeriv K f x
    (-ydf.1,
     fun dy =>
       let dx := ydf.2 dy
       (-dx)) := by
  unfold revDeriv; simp; fun_trans

@[fun_trans]
theorem Neg.neg.arg_a0.revDerivUpdate_rule
    (f : X → Y) :
    (revDerivUpdate K fun x => - f x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      (-ydf.1,
       fun dy dx =>
         let dy' := -dy
         ydf.2 dy' dx) := by
  unfold revDerivUpdate; funext x; fun_trans; simp[neg_pull,revDeriv]

@[fun_trans]
theorem Neg.neg.arg_a0.revDerivProj_rule
    (f : X → Y') :
    (revDerivProj K Yi fun x => - f x)
    =
    fun x =>
      let ydf := revDerivProj K Yi f x
      (-ydf.1,
       fun i dy =>
         let dy' := -dy
         ydf.2 i dy') := by
  unfold revDerivProj; fun_trans; simp[neg_push,revDeriv]

@[fun_trans]
theorem Neg.neg.arg_a0.revDerivProjUpdate_rule
    (f : X → Y') :
    (revDerivProjUpdate K Yi fun x => - f x)
    =
    fun x =>
      let ydf := revDerivProjUpdate K Yi f x
      (-ydf.1,
       fun i dy dx =>
         let dy' := -dy
         ydf.2 i dy' dx) := by
  unfold revDerivProjUpdate; fun_trans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------
open ComplexConjugate

@[fun_trans]
theorem HMul.hMul.arg_a0a1.revDeriv_rule
    (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDeriv K fun x => f x * g x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let zdg := revDeriv K g x
      (ydf.1 * zdg.1,
       fun dx' =>
         let dx₁ := (conj zdg.1 * dx')
         let dx₂ := (conj ydf.1 * dx')
         let dx := zdg.2 dx₂
         ydf.2 dx₁ dx) := by
  unfold revDerivUpdate; unfold revDeriv; simp; fun_trans
  simp [smul_push]

@[fun_trans]
theorem HMul.hMul.arg_a0a1.revDerivUpdate_rule
    (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivUpdate K fun x => f x * g x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 * zdg.1,
       fun dx' dx =>
         let dx₁ := (conj zdg.1 * dx')
         let dx₂ := (conj ydf.1 * dx')
         let dx := zdg.2 dx₂ dx
         ydf.2 dx₁ dx) := by
  unfold revDerivUpdate; simp; fun_trans
  simp [smul_push,add_assoc,revDerivUpdate]

@[fun_trans]
theorem HMul.hMul.arg_a0a1.revDerivProj_rule
    (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivProj K Unit fun x => f x * g x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let zdg := revDeriv K g x
      (ydf.1 * zdg.1,
       fun _ dy =>
         let dy₁ := (conj zdg.1)*dy
         let dy₂ := (conj ydf.1)*dy
         let dx := zdg.2 dy₂
         ydf.2 dy₁ dx) := by
  unfold revDerivProj
  fun_trans; simp[oneHot, structMake]

@[fun_trans]
theorem HMul.hMul.arg_a0a1.revDerivProjUpdate_rule
    (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivProjUpdate K Unit fun x => f x * g x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 * zdg.1,
       fun _ dy dx =>
         let dy₁ := (conj zdg.1)*dy
         let dy₂ := (conj ydf.1)*dy
         let dx := zdg.2 dy₂ dx
         ydf.2 dy₁ dx) := by
  unfold revDerivProjUpdate
  fun_trans; simp[revDerivUpdate,add_assoc]


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

section SMulOnSemiHilbert

variable
  {Y Yi : Type} {YI : Yi → Type} [StructType Y Yi YI] [IndexType Yi] [LawfulIndexType Yi] [DecidableEq Yi]
  [SemiHilbert K Y] [∀ i, SemiHilbert K (YI i)] [SemiInnerProductSpaceStruct K Y Yi YI]

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revDeriv_rule
    (f : X → K) (g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDeriv K fun x => f x • g x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let zdg := revDeriv K g x
      (ydf.1 • zdg.1,
       fun dy' =>
         let dk := inner zdg.1 dy'
         let dx := zdg.2 dy'
         let dx := conj ydf.1 • dx
         ydf.2 dk dx) := by
  unfold revDerivUpdate; unfold revDeriv
  fun_trans

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revDerivUpdate_rule
    (f : X → K) (g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivUpdate K fun x => f x • g x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 • zdg.1,
       fun dy dx =>
         let dk := inner zdg.1 dy
         let dy' := conj ydf.1 • dy
         let dx := zdg.2 dy' dx
         ydf.2 dk dx) := by
  unfold revDerivUpdate;
  funext x; fun_trans; simp[mul_assoc,add_assoc,revDerivUpdate,revDeriv,smul_push]

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revDerivProj_rule
    (f : X → K) (g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivProj K Yi fun x => f x • g x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let zdg := revDerivProj K Yi g x
      (ydf.1 • zdg.1,
       fun i (dy : YI i) =>
         let dk := inner (structProj zdg.1 i) dy
         let dx := zdg.2 i dy
         let dx := conj ydf.1•dx
         ydf.2 dk dx) := by
  unfold revDerivProj; fun_trans

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revDerivProjUpdate_rule
    (f : X → K) (g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) :
    (revDerivProjUpdate K Yi fun x => f x • g x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let zdg := revDerivProjUpdate K Yi g x
      (ydf.1 • zdg.1,
       fun i (dy : YI i) dx =>
         let dk := inner (structProj zdg.1 i) dy
         let dy' := conj ydf.1•dy
         let dx := zdg.2 i dy' dx
         ydf.2 dk dx) := by
  unfold revDerivProjUpdate
  fun_trans; simp[revDerivUpdate,add_assoc,smul_pull]
  simp only [smul_pull,revDerivProj,revDeriv]

end SMulOnSemiHilbert


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revDeriv_rule
    (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : fpropParam (∀ x, g x ≠ 0)) :
    (revDeriv K fun x => f x / g x)
    =
    fun x =>
      let ydf := revDeriv K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 / zdg.1,
       fun dx' => (1 / (conj zdg.1)^2) • (zdg.2 (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 dx'))) := by
  unfold revDeriv; simp
  fun_trans (disch:=assumption)
  simp[revDerivUpdate,smul_push,neg_pull,revDeriv,smul_add,smul_sub, ← sub_eq_add_neg]

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revDerivUpdate_rule
    (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0) :
    (revDerivUpdate K fun x => f x / g x)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 / zdg.1,
       fun dx' dx =>
         let c := (1 / (conj zdg.1)^2)
         let a := -(c * conj ydf.1)
         let b := c * conj zdg.1
         ((zdg.2 (a • dx') (ydf.2 (b • dx') dx)))) := by
  funext
  simp[revDerivUpdate]
  fun_trans (disch:=assumption)
  simp[revDerivUpdate,smul_push,neg_pull,revDeriv,smul_add,smul_sub,add_assoc,mul_assoc]


@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revDerivProj_rule
    (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0) :
    (revDerivProj K Unit fun x => f x / g x)
    =
    fun x =>
      let ydf := revDeriv K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 / zdg.1,
       fun _ dx' => (1 / (conj zdg.1)^2) • (zdg.2 (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 dx'))) :=
by
  unfold revDerivProj
  fun_trans (disch:=assumption); simp[oneHot, structMake]

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revDerivProjUpdate_rule
    (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0) :
    (revDerivProjUpdate K Unit fun x => f x / g x)
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
  fun_trans (disch:=assumption)
  simp[revDerivUpdate,revDeriv,add_assoc,neg_pull,mul_assoc,smul_push]


-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
def HPow.hPow.arg_a0.revDeriv_rule
    (f : X → K) (n : Nat) (hf : HasAdjDiff K f) :
    revDeriv K (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revDeriv K f x
      let y' := (n : K) * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n,
       fun dx' => ydf.2 (y' * dx')) :=
by
  funext x
  unfold revDeriv; simp; funext dx; fun_trans; simp[smul_push,smul_smul]; ring_nf

@[fun_trans]
def HPow.hPow.arg_a0.revDerivUpdate_rule
    (f : X → K) (n : Nat) (hf : HasAdjDiff K f) :
    revDerivUpdate K (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let y' := n * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n,
       fun dy dx => ydf.2 (y' * dy) dx) := by
  unfold revDerivUpdate
  funext x; fun_trans

@[fun_trans]
def HPow.hPow.arg_a0.revDerivProj_rule
    (f : X → K) (n : Nat) (hf : HasAdjDiff K f) :
    revDerivProj K Unit (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revDeriv K f x
      let y' := (n : K) * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n, fun _ dx' => ydf.2 (y' * dx')) := by
  unfold revDerivProj; fun_trans; simp[oneHot,structMake]

@[fun_trans]
def HPow.hPow.arg_a0.revDerivProjUpdate_rule
    (f : X → K) (n : Nat) (hf : HasAdjDiff K f) :
    revDerivProjUpdate K Unit (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      let y' := n * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n,
       fun _ dy dx => ydf.2 (y' * dy) dx) := by
  unfold revDerivProjUpdate; fun_trans; simp[oneHot,structMake,revDerivUpdate]


-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

section IndexTypeSum

variable {ι : Type} [IndexType ι] [LawfulIndexType ι]

@[fun_trans]
theorem IndexType.sum.arg_f.revDeriv_rule
  (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDeriv K (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := revDeriv K f x
      (∑ i, ydf.1 i,
       fun dy =>
         ydf.2 (fun _ => dy)) :=
by
  unfold revDeriv
  fun_trans;
  funext x; simp; funext dy;
  conv => rhs; rw[cderiv.pi_rule (hf := by fun_prop)];
  fun_trans


@[fun_trans]
theorem IndexType.sum.arg_f.revDerivUpdate_rule
    (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i)) :
    revDerivUpdate K (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := revDerivUpdate K f x
      (∑ i, ydf.1 i,
       fun dy dx =>
         ydf.2 (fun _ => dy) dx) := by
  unfold revDerivUpdate
  fun_trans

@[fun_trans]
theorem IndexType.sum.arg_f.revDerivProj_rule [DecidableEq ι]
    (f : X → ι → Y') (hf : ∀ i, HasAdjDiff K (fun x => f x i)) :
    revDerivProj K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      -- this is not optimal
      -- we should have but right now there is no appropriate StrucLike instance
      -- let ydf := revDerivProj K Yi f x
      let ydf := revDerivProjUpdate K (ι×Yi) f x
      (∑ i, ydf.1 i,
       fun j dy =>
         Fold.fold (IndexType.univ ι) (fun dx i => ydf.2 (i,j) dy dx) 0) := by
  unfold revDerivProj
  fun_trans
  sorry_proof


@[fun_trans]
theorem IndexType.sum.arg_f.revDerivProjUpdate_rule [DecidableEq ι]
    (f : X → ι → Y') (hf : ∀ i, HasAdjDiff K (fun x => f x i)) :
    revDerivProjUpdate K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := revDerivProjUpdate K (ι×Yi) f x
      (∑ i, ydf.1 i,
       fun j dy dx =>
         Fold.fold (IndexType.univ ι) (fun dx i => ydf.2 (i,j) dy dx) dx) := by
  sorry_proof


end IndexTypeSum


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem ite.arg_te.revDeriv_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y) :
    revDeriv K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDeriv K t y) (revDeriv K e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem ite.arg_te.revDerivUpdate_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y) :
    revDerivUpdate K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDerivUpdate K t y) (revDerivUpdate K e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem ite.arg_te.revDerivProj_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y') :
    revDerivProj K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDerivProj K Yi t y) (revDerivProj K Yi e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem ite.arg_te.revDerivProjUpdate_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y') :
    revDerivProjUpdate K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDerivProjUpdate K Yi t y) (revDerivProjUpdate K Yi e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]


@[fun_trans]
theorem dite.arg_te.revDeriv_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y) (e : ¬c → X → Y) :
    revDeriv K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDeriv K (t p) y)
             (fun p => revDeriv K (e p) y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem dite.arg_te.revDerivUpdate_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y) (e : ¬c → X → Y) :
    revDerivUpdate K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDerivUpdate K (t p) y)
             (fun p => revDerivUpdate K (e p) y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem dite.arg_te.revDerivProj_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y') (e : ¬c → X → Y') :
    revDerivProj K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDerivProj K Yi (t p) y)
             (fun p => revDerivProj K Yi (e p) y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem dite.arg_te.revDerivProjUpdate_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y') (e : ¬c → X → Y') :
    revDerivProjUpdate K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDerivProjUpdate K Yi (t p) y)
             (fun p => revDerivProjUpdate K Yi (e p) y) := by
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
    (f : X → Y) (g : X → Y) (hf : HasAdjDiff R f) (hg : HasAdjDiff R g) :
    (revDeriv R fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revDeriv R f x
      let y₂dg := revDerivUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1))) := by
  funext; simp[revDeriv,revDerivUpdate]
  fun_trans[smul_pull]

@[fun_trans]
theorem Inner.inner.arg_a0a1.revDerivUpdate_rule
    (f : X → Y) (g : X → Y) (hf : HasAdjDiff R f) (hg : HasAdjDiff R g) :
    (revDerivUpdate R fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revDerivUpdate R f x
      let y₂dg := revDerivUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr dx =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1) dx) ) := by
  unfold revDerivUpdate
  fun_trans; simp[revDerivUpdate,add_assoc]

@[fun_trans]
theorem Inner.inner.arg_a0a1.revDerivProj_rule
    (f : X → Y) (g : X → Y) (hf : HasAdjDiff R f) (hg : HasAdjDiff R g) :
    (revDerivProj R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revDeriv R f x
      let y₂dg := revDerivUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1))) := by
  funext
  simp[revDerivProj]
  fun_trans; simp[oneHot, structMake]

@[fun_trans]
theorem Inner.inner.arg_a0a1.revDerivProjUpdate_rule
    (f : X → Y) (g : X → Y) (hf : HasAdjDiff R f) (hg : HasAdjDiff R g) :
    (revDerivProjUpdate R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revDerivUpdate R f x
      let y₂dg := revDerivUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr dx =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1) dx)) := by
  funext
  simp[revDerivProjUpdate]
  fun_trans; simp[revDerivUpdate,add_assoc]


-- norm2 -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revDeriv_rule
    (f : X → Y) (hf : HasAdjDiff R f) :
    (revDeriv R fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revDeriv R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun dr =>
         ((2:R) * dr) • ydf.2 ydf.1) := by
  funext x; simp[revDeriv]
  fun_trans[smul_smul]

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revDerivUpdate_rule
    (f : X → Y) (hf : HasAdjDiff R f) :
    (revDerivUpdate R fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revDerivUpdate R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun dr dx =>
          ydf.2 (((2:R)*dr)•ydf.1) dx) := by
  funext x; simp[revDerivUpdate]
  fun_trans; simp[revDeriv,smul_pull]

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revDerivProj_rule
    (f : X → Y) (hf : HasAdjDiff R f) :
    (revDerivProj R Unit fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revDeriv R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr =>
         ((2:R) * dr) • ydf.2 ydf.1) := by
  funext x; simp[revDerivProj]
  fun_trans; simp[oneHot,structMake]

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revDerivProjUpdate_rule
    (f : X → Y) (hf : HasAdjDiff R f) :
    (revDerivProjUpdate R Unit fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revDerivUpdate R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr dx =>
          ydf.2 (((2:R)*dr)•ydf.1) dx) := by
  funext x; simp[revDerivProjUpdate]
  fun_trans only; simp[revDeriv,revDerivUpdate,smul_pull]


-- norm₂ -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDeriv_rule_at
    (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0) :
    (revDeriv R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDeriv R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun dr =>
       (ynorm⁻¹ * dr) • ydf.2 ydf.1) := by
  simp[revDeriv]
  fun_trans (disch:=assumption) only
  simp[smul_smul]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDerivUpdate_rule_at
    (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0) :
    (revDerivUpdate R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDerivUpdate R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun dr dx =>
       ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx) := by
  simp[revDerivUpdate]
  fun_trans (disch:=assumption) only
  simp[revDeriv,smul_pull]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDerivProj_rule_at
    (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0) :
    (revDerivProj R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDeriv R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr =>
       (ynorm⁻¹ * dr) • ydf.2 ydf.1):= by
  simp[revDerivProj]
  fun_trans (disch:=assumption) only; simp[oneHot, structMake]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDerivProjUpdate_rule_at
    (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0) :
    (revDerivProjUpdate R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDerivUpdate R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr dx =>
       ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
by
  have ⟨_,_⟩ := hf
  simp[revDerivProjUpdate]
  fun_trans (disch:=assumption) only
  simp[revDeriv,revDerivUpdate,smul_pull]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDeriv_rule
    (f : X → Y) (hf : HasAdjDiff R f) (hx : ∀ x, f x≠0) :
    (revDeriv R (fun x => ‖f x‖₂[R]))
    =
    fun x =>
      let ydf := revDeriv R f x
      let ynorm := ‖ydf.1‖₂[R]
      (ynorm,
       fun dr =>
         (ynorm⁻¹ * dr) • ydf.2 ydf.1):=
by
  unfold revDeriv
  funext x; simp
  fun_trans (disch:=assumption)
  simp[smul_smul]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDerivUpdate_rule
    (f : X → Y) (hf : HasAdjDiff R f) (hx : ∀ x, f x≠0) :
    (revDerivUpdate R (fun x => ‖f x‖₂[R]))
    =
    fun x =>
      let ydf := revDerivUpdate R f x
      let ynorm := ‖ydf.1‖₂[R]
      (ynorm,
       fun dr dx =>
         ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
by
  unfold revDerivUpdate
  funext x; simp
  fun_trans (disch:=assumption) only
  simp[revDeriv,smul_pull]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDerivProj_rule
    (f : X → Y) (hf : HasAdjDiff R f) (hx : ∀ x, f x≠0) :
    (revDerivProj R Unit (fun x => ‖f x‖₂[R]))
    =
    fun x =>
      let ydf := revDeriv R f x
      let ynorm := ‖ydf.1‖₂[R]
      (ynorm,
       fun _ dr =>
         (ynorm⁻¹ * dr) • ydf.2 ydf.1) := by
  unfold revDerivProj
  funext x; simp
  fun_trans (disch:=assumption) only
  simp[oneHot, structMake]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDerivProjUpdate_rule
    (f : X → Y) (hf : HasAdjDiff R f) (hx : ∀ x, f x≠0) :
    (revDerivProjUpdate R Unit (fun x => ‖f x‖₂[R]))
    =
    fun x =>
       let ydf := revDerivUpdate R f x
       let ynorm := ‖ydf.1‖₂[R]
       (ynorm,
        fun _ dr dx =>
          ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx) := by
  unfold revDerivProjUpdate
  funext x; simp
  fun_trans (disch:=assumption) only
  simp[revDeriv,revDerivUpdate,smul_pull]

end InnerProductSpace
