import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.AdjointSpace.Adjoint
import SciLean.Analysis.FunctionSpaces.SmoothLinearMap

import SciLean.Data.StructType.Algebra

import SciLean.Tactic.Autodiff

set_option linter.unusedVariables false

namespace SciLean

variable
  (K I : Type _) [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [AdjointSpace K Z]
  {W : Type _} [NormedAddCommGroup W] [AdjointSpace K W]
  {ι : Type _} [IndexType ι] [DecidableEq ι]
  {κ : Type _} [IndexType κ] [DecidableEq κ]
  {E : Type _} {EI : I → Type _}
  [StructType E I EI] [IndexType I] [DecidableEq I]
  [NormedAddCommGroup E] [AdjointSpace K E] [∀ i, NormedAddCommGroup (EI i)] [∀ i, AdjointSpace K (EI i)]
  [VecStruct K E I EI] -- todo: define AdjointSpaceStruct
  {F J : Type _} {FJ : J → Type _}
  [StructType F J FJ] [IndexType J] [DecidableEq J]
  [NormedAddCommGroup F] [AdjointSpace K F] [∀ j, NormedAddCommGroup (FJ j)] [∀ j, AdjointSpace K (FJ j)]
  [VecStruct K F J FJ] -- todo: define AdjointSpaceStruct


@[fun_trans]
noncomputable
def revFDerivOpt
  (f : X → Y) (x : X) : Y×(Y→X) :=
  (f x, adjoint K (fderiv K f x))

@[fun_trans]
noncomputable
def revFDerivOptUpdate
  (f : X → Y) (x : X) : Y×(Y→X→X) :=
  let ydf := revFDerivOpt K f x
  (ydf.1, fun dy dx => dx + ydf.2 dy)

@[fun_trans]
noncomputable
def revFDerivOptProj [DecidableEq I]
  (f : X → E) (x : X) : E×((i : I)→EI i→X) :=
  let ydf' := revFDerivOpt K f x
  (ydf'.1, fun i de =>
    ydf'.2 (oneHot i de))

@[fun_trans]
noncomputable
def revFDerivOptProjUpdate [DecidableEq I]
  (f : X → E) (x : X) : E×((i : I)→EI i→X→X) :=
  let ydf' := revFDerivOptProj K I f x
  (ydf'.1, fun i de dx => dx + ydf'.2 i de)


-- noncomputable
-- abbrev gradient (f : X → Y) (x : X) : (Y → X):= (revFDerivOpt K f x).2

-- noncomputable
-- abbrev scalarGradient (f : X → K) (x : X) : X := (revFDerivOpt K f x).2 1


--------------------------------------------------------------------------------
-- simplification rules for individual components ------------------------------
--------------------------------------------------------------------------------

@[simp, simp_core]
theorem revFDerivOpt_fst (f : X → Y) (x : X)
  : (revFDerivOpt K f x).1 = f x :=
by
  rfl

@[simp, simp_core]
theorem revFDerivOpt_snd_zero (f : X → Y) (x : X)
  : (revFDerivOpt K f x).2 0 = 0 :=
by
  simp[revFDerivOpt]

@[simp, simp_core]
theorem revFDerivOptUpdate_fst (f : X → Y) (x : X)
  : (revFDerivOptUpdate K f x).1 = f x :=
by
  rfl

@[simp, simp_core]
theorem revFDerivOptUpdate_snd_zero (f : X → Y) (x dx : X)
  : (revFDerivOptUpdate K f x).2 0 dx = dx :=
by
  simp[revFDerivOptUpdate]

@[simp, simp_core]
theorem revFDerivOptUpdate_snd_zero' (f : X → Y) (x : X) (dy : Y)
  : (revFDerivOptUpdate K f x).2 dy 0 = (revFDerivOpt K f x).2 dy :=
by
  simp[revFDerivOptUpdate]


@[simp, simp_core]
theorem revFDerivOptProj_fst (f : X → E) (x : X)
  : (revFDerivOptProj K (I:=I) f x).1 = f x :=
by
  rfl

@[simp, simp_core]
theorem revFDerivOptProj_snd_zero (f : X → E) (x : X) (i : I)
  : (revFDerivOptProj K I f x).2 i 0 = 0 :=
by
  simp[revFDerivOptProj]

@[simp, simp_core]
theorem revFDerivOptProjUpdate_fst (f : X → E) (x : X)
  : (revFDerivOptProjUpdate K I f x).1 = f x :=
by
  rfl

@[simp, simp_core]
theorem revFDerivOptProjUpdate_snd_zero (f : X → E) (x dx : X) (i : I)
  : (revFDerivOptProjUpdate K I f x).2 i 0 dx = dx :=
by
  simp[revFDerivOptProjUpdate]

@[simp, simp_core]
theorem revFDerivOptProjUpdate_snd_zero' (f : X → Y) (x : X) (dy : Y)
  : (revFDerivOptUpdate K f x).2 dy 0 = (revFDerivOpt K f x).2 dy :=
by
  simp[revFDerivOptUpdate]


--------------------------------------------------------------------------------
-- Lambda calculus rules for revFDerivOpt ------------------------------------------
--------------------------------------------------------------------------------

namespace revFDerivOpt

@[fun_trans]
theorem id_rule :
    revFDerivOpt K (fun x : X => x) = fun x => (x, fun dx => dx) := by
  unfold revFDerivOpt
  fun_trans

@[fun_trans]
theorem const_rule (y : Y) :
    revFDerivOpt K (fun _ : X => y) = fun x => (y, fun _ => 0) := by
  unfold revFDerivOpt
  fun_trans

@[fun_trans]
theorem comp_rule
    (f : Y → Z) (g : X → Y)
    (hf : Differentiable K f) (hg : Differentiable K g) :
    revFDerivOpt K (fun x : X => f (g x))
    =
    fun x =>
      let ydg := revFDerivOpt K g x
      let zdf := revFDerivOpt K f ydg.1
      (zdf.1,
       fun dz =>
         let dy := zdf.2 dz
         ydg.2 dy)  := by
  unfold revFDerivOpt
  fun_trans

@[fun_trans]
theorem let_rule
    (f : X → Y → Z) (g : X → Y)
    (hf : Differentiable K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : Differentiable K g) :
    revFDerivOpt K (fun x : X => let y := g x; f x y)
    =
    fun x =>
      let ydg := revFDerivOptUpdate K g x
      let zdf := revFDerivOpt K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz =>
         let dxdy := zdf.2 dz
         let dx := ydg.2 dxdy.2 dxdy.1
         dx)  := by
  unfold revFDerivOptUpdate revFDerivOpt
  fun_trans

@[fun_trans]
theorem apply_rule (i : I) :
    revFDerivOpt K (fun (x : (i:I) → EI i) => x i)
    =
    fun x =>
      (x i, fun dxi => oneHot i dxi) := by
  unfold revFDerivOpt
  fun_trans; simp[oneHot]

@[fun_trans]
theorem pi_rule
    (f :  X → (i : I) → EI i) (hf : ∀ i, Differentiable K (f · i)) :
    (revFDerivOpt K fun (x : X) (i : I) => f x i)
    =
    fun x =>
      let xdf := fun i => revFDerivOptUpdate K (f · i) x
      (fun i => (xdf i).1,
       fun dy =>
         IndexType.foldl (fun dx i => (xdf i).2 (dy i) dx) 0) := by
  unfold revFDerivOpt
  fun_trans;
  funext x; simp
  rw[fderiv.pi_rule (hf:=by fun_prop)]; fun_trans
  simp[revFDerivOptUpdate,revFDerivOpt,IndexType.sum]
  sorry_proof

end revFDerivOpt


--------------------------------------------------------------------------------
-- Lambda calculus rules for revFDerivOptUpdate ------------------------------------
--------------------------------------------------------------------------------

namespace revFDerivOptUpdate

@[fun_trans]
theorem id_rule :
    revFDerivOptUpdate K (fun x : X => x) = fun x => (x, fun dx' dx => dx + dx') := by
  unfold revFDerivOptUpdate
  fun_trans

@[fun_trans]
theorem const_rule (y : Y) :
    revFDerivOptUpdate K (fun _ : X => y) = fun x => (y, fun _ dx => dx) := by
  unfold revFDerivOptUpdate
  fun_trans

@[fun_trans]
theorem comp_rule
    (f : Y → Z) (g : X → Y)
    (hf : Differentiable K f) (hg : Differentiable K g) :
    revFDerivOptUpdate K (fun x : X => f (g x))
    =
    fun x =>
      let ydg := revFDerivOptUpdate K g x
      let zdf := revFDerivOpt K f ydg.1
      (zdf.1,
       fun dz dx =>
         let dy := zdf.2 dz
         ydg.2 dy dx)  := by
  unfold revFDerivOptUpdate
  fun_trans

@[fun_trans]
theorem let_rule
    (f : X → Y → Z) (g : X → Y)
    (hf : Differentiable K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : Differentiable K g) :
    revFDerivOptUpdate K (fun x : X => let y := g x; f x y)
    =
    fun x =>
      let ydg := revFDerivOptUpdate K g x
      let zdf := revFDerivOptUpdate K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz dx =>
         let dxdy := zdf.2 dz (dx, 0)
         let dx := ydg.2 dxdy.2 dxdy.1
         dx)  := by
  unfold revFDerivOptUpdate
  fun_trans [revFDerivOptUpdate,revFDerivOpt,add_assoc]


@[fun_trans]
theorem apply_rule (i : I) :
    revFDerivOptUpdate K (fun (x : (i:I) → EI i) => x i)
    =
    fun x =>
      (x i, fun dxi dx => structModify i (fun dxi' => dxi' + dxi) dx) := by
  funext x
  unfold revFDerivOptUpdate
  fun_trans [oneHot,Function.modify]
  funext dy dx i;
  unfold Function.modify Function.update
  simp
  aesop

@[fun_trans]
theorem pi_rule
    (f :  X → (i : I) → EI i) (hf : ∀ i, Differentiable K (f · i)) :
    (revFDerivOptUpdate K fun (x : X) (i : I) => f x i)
    =
    fun x =>
      let xdf := fun i => revFDerivOptUpdate K (f · i) x
      (fun i => (xdf i).1,
       fun dy dx =>
         IndexType.foldl (fun dx i => (xdf i).2 (dy i) dx) dx) := by
  unfold revFDerivOptUpdate
  funext x
  rw[revFDerivOpt.pi_rule (hf:=by fun_prop)]
  simp
  simp[revFDerivOptUpdate,revFDerivOpt]
  sorry_proof


end revFDerivOptUpdate


--------------------------------------------------------------------------------
-- Lambda calculus rules for revFDerivOptProj ------------------------------------
--------------------------------------------------------------------------------

namespace revFDerivOptProj

@[fun_trans]
theorem id_rule :
    revFDerivOptProj K I (fun x : E => x)
    =
    fun x =>
      (x,
       fun i de =>
         oneHot i de) := by
  unfold revFDerivOptProj; fun_trans

@[fun_trans]
theorem const_rule (x : E)
  : revFDerivOptProj K I (fun _ : Y => x)
    =
    fun _ =>
      (x,
       fun i (de : EI i) => 0) := by
  unfold revFDerivOptProj; fun_trans

@[fun_trans]
theorem apply_rule [DecidableEq I] (i : ι) :
    revFDerivOptProj K I (fun (f : ι → E) => f i)
    =
    fun f : ι → E =>
      (f i, fun j dxj => oneHot (X:=ι→E) (I:=ι×I) (i,j) dxj) :=
by
  unfold revFDerivOptProj;
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
    (f : Y → E) (g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    revFDerivOptProj K I (fun x => f (g x))
    =
    fun x =>
      let ydg' := revFDerivOpt K g x
      let zdf' := revFDerivOptProj K I f ydg'.1
      (zdf'.1,
       fun i de =>
         ydg'.2 (zdf'.2 i de)) := by
  unfold revFDerivOptProj; fun_trans

@[fun_trans]
theorem let_rule
    (f : X → Y → E) (g : X → Y)
    (hf : Differentiable K (fun (x,y) => f x y)) (hg : Differentiable K g) :
    revFDerivOptProj K I (fun x => let y := g x; f x y)
    =
    fun x =>
      let ydg' := revFDerivOptUpdate K g x
      let zdf' := revFDerivOptProj K I (fun (x,y) => f x y) (x,ydg'.1)
      (zdf'.1,
       fun i dei =>
         let dxy := zdf'.2 i dei
         ydg'.2 dxy.2 dxy.1) := by
  unfold revFDerivOptProj revFDerivOptUpdate revFDerivOpt; fun_trans

@[fun_trans]
theorem pi_rule
    (f :  X → ι → Y) (hf : ∀ i, Differentiable K (f · i)) :
    (revFDerivOptProj K Unit fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let ydf := fun i => revFDerivOptUpdate K (f · i) x
      (fun i => (ydf i).1,
       fun _ df =>
         IndexType.foldl (fun dx i => (ydf i).2 (df i) dx) (0 : X)) := by
  unfold revFDerivOptProj
  fun_trans
  funext x; simp; funext i de
  rw[revFDerivOpt.pi_rule (hf:=by fun_prop)]; simp[oneHot]

end revFDerivOptProj


--------------------------------------------------------------------------------
-- Lambda calculus rules for revFDerivOptProjUpdate --------------------------------
--------------------------------------------------------------------------------

namespace revFDerivOptProjUpdate

@[fun_trans]
theorem id_rule
  : revFDerivOptProjUpdate K I (fun x : E => x)
    =
    fun x =>
      (x,
       fun i de dx =>
         structModify i (fun ei => ei + de) dx) :=
by
  funext x
  simp[revFDerivOptProjUpdate, revFDerivOptProj.id_rule]
  sorry_proof


@[fun_trans]
theorem const_rule (x : E)
  : revFDerivOptProjUpdate K I (fun _ : Y => x)
    =
    fun _ =>
      (x,
       fun i de dx => dx) :=
by
  unfold revFDerivOptProjUpdate; simp[revFDerivOptProj.const_rule]

@[fun_trans]
theorem comp_rule
  (f : Y → E) (g : X → Y)
  (hf : Differentiable K f) (hg : Differentiable K g)
  : revFDerivOptProjUpdate K I (fun x => f (g x))
    =
    fun x =>
      let ydg' := revFDerivOptUpdate K g x
      let zdf' := revFDerivOptProj K I f ydg'.1
      (zdf'.1,
       fun i de dx =>
         ydg'.2 (zdf'.2 i de) dx) :=
by
  funext x
  simp[revFDerivOptProjUpdate,revFDerivOptProj.comp_rule _ _ _ _ hf hg]
  rfl

@[fun_trans]
theorem let_rule
  (f : X → Y → E) (g : X → Y)
  (hf : Differentiable K (fun (x,y) => f x y)) (hg : Differentiable K g)
  : revFDerivOptProjUpdate K I (fun x => let y := g x; f x y)
    =
    fun x =>
      let ydg' := revFDerivOptUpdate K g x
      let zdf' := revFDerivOptProjUpdate K I (fun (x,y) => f x y) (x,ydg'.1)
      (zdf'.1,
       fun i dei dx =>
         let dxy := zdf'.2 i dei (dx,0)
         ydg'.2 dxy.2 dxy.1) :=
by
  unfold revFDerivOptProjUpdate
  simp [revFDerivOptProj.let_rule _ _ _ _ hf hg,add_assoc,add_comm,revFDerivOptUpdate]

@[fun_trans]
theorem apply_rule [DecidableEq I] (i : ι)
  : revFDerivOptProjUpdate K I (fun (f : ι → E) => f i)
    =
    fun f =>
      (f i, fun j dxj df i' =>
        if i=i' then
          structModify j (fun xj => xj + dxj) (df i')
        else
          df i') :=
by
  funext x;
  unfold revFDerivOptProjUpdate
  fun_trans
  funext j dxj f i'
  apply structExt (I:=I)
  intro j'
  if h :i'=i then
    subst h; simp; sorry_proof
  else
    have h' : i≠i' := by intro h''; simp[h''] at h
    simp[h,h']
    sorry_proof

@[fun_trans]
theorem pi_rule
    (f :  X → ι → Y) (hf : ∀ i, Differentiable K (f · i)) :
    (revFDerivOptProjUpdate K Unit fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let ydf := fun i => revFDerivOptUpdate K (f · i) x
      (fun i => (ydf i).1,
       fun _ df dx =>
         IndexType.foldl (fun dx i => (ydf i).2 (df i) dx) dx) :=
by
  unfold revFDerivOptProjUpdate
  fun_trans
  unfold revFDerivOptProj
  funext x; simp; funext i de dx
  rw[revFDerivOpt.pi_rule (hf:=by fun_prop)]; simp[oneHot,revFDerivOptUpdate]
  sorry_proof


end revFDerivOptProjUpdate


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

end SciLean
open SciLean

variable
  {K : Type} [RCLike K]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z]
  {X' Xi : Type} {XI : Xi → Type} [StructType X' Xi XI] [IndexType Xi] [DecidableEq Xi]
  {Y' Yi : Type} {YI : Yi → Type} [StructType Y' Yi YI] [IndexType Yi] [DecidableEq Yi]
  {Z' Zi : Type} {ZI : Zi → Type} [StructType Z' Zi ZI] [IndexType Zi] [DecidableEq Zi]
  [NormedAddCommGroup X'] [AdjointSpace K X'] [∀ i, NormedAddCommGroup (XI i)] [∀ i, AdjointSpace K (XI i)] [VecStruct K X' Xi XI]
  [NormedAddCommGroup Y'] [AdjointSpace K Y'] [∀ i, NormedAddCommGroup (YI i)] [∀ i, AdjointSpace K (YI i)] [VecStruct K Y' Yi YI]
  [NormedAddCommGroup Z'] [AdjointSpace K Z'] [∀ i, NormedAddCommGroup (ZI i)] [∀ i, AdjointSpace K (ZI i)] [VecStruct K Z' Zi ZI]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace K W]
  {ι : Type} [IndexType ι]



-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.mk.arg_fstsnd.revFDerivOpt_rule
    (g : X → Y) (f : X → Z) (hg : Differentiable K g) (hf : Differentiable K f) :
    revFDerivOpt K (fun x => (g x, f x))
    =
    fun x =>
      let ydg := revFDerivOpt K g x
      let zdf := revFDerivOptUpdate K f x
      ((ydg.1,zdf.1),
       fun dyz =>
         let dx := ydg.2 dyz.1
         zdf.2 dyz.2 dx) := by
  unfold revFDerivOptUpdate; unfold revFDerivOpt; simp; fun_trans

@[fun_trans]
theorem Prod.mk.arg_fstsnd.revFDerivOptUpdate_rule
  (g : X → Y) (f : X → Z)
  (hg : Differentiable K g) (hf : Differentiable K f)
  : revFDerivOptUpdate K (fun x => (g x, f x))
    =
    fun x =>
      let ydg := revFDerivOptUpdate K g x
      let zdf := revFDerivOptUpdate K f x
      ((ydg.1,zdf.1),
       fun dyz dx =>
         let dx := ydg.2 dyz.1 dx
         zdf.2 dyz.2 dx) :=
by
  unfold revFDerivOptUpdate; fun_trans; simp[add_assoc, revFDerivOptUpdate]

@[fun_trans]
theorem Prod.mk.arg_fstsnd.revFDerivOptProj_rule
    (g : X → Y') (f : X → Z')
    (hg : Differentiable K g) (hf : Differentiable K f) :
    revFDerivOptProj K (Yi⊕Zi) (fun x => (g x, f x))
    =
    fun x =>
      let ydg := revFDerivOptProj K Yi g x
      let zdf := revFDerivOptProj K Zi f x
      ((ydg.1,zdf.1),
       fun i dyz =>
         match i with
         | .inl j => ydg.2 j dyz
         | .inr j => zdf.2 j dyz) := by
  unfold revFDerivOptProj
  funext x; fun_trans; simp[revFDerivOptUpdate]
  funext i dyz
  induction i <;>
    { simp[oneHot,structMake]
      apply congr_arg
      congr; funext i; congr; funext h
      subst h; rfl
    }

@[fun_trans]
theorem Prod.mk.arg_fstsnd.revFDerivOptProjUpdate_rule
    (g : X → Y') (f : X → Z')
    (hg : Differentiable K g) (hf : Differentiable K f) :
    revFDerivOptProjUpdate K (Yi⊕Zi) (fun x => (g x, f x))
    =
    fun x =>
      let ydg := revFDerivOptProjUpdate K Yi g x
      let zdf := revFDerivOptProjUpdate K Zi f x
      ((ydg.1,zdf.1),
       fun i dyz dx =>
         match i with
         | .inl j => ydg.2 j dyz dx
         | .inr j => zdf.2 j dyz dx) := by
  unfold revFDerivOptProjUpdate
  funext x; fun_trans
  funext i de dx
  induction i <;> simp


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.fst.arg_self.revFDerivOpt_rule
    (f : X → Y×Z) (hf : Differentiable K f) :
    revFDerivOpt K (fun x => (f x).1)
    =
    fun x =>
      let yzdf := revFDerivOptProj K (Unit⊕Unit) f x
      (yzdf.1.1, fun dy => yzdf.2 (.inl ()) dy) := by
  unfold revFDerivOptProj; unfold revFDerivOpt
  fun_trans [oneHot]

@[fun_trans]
theorem Prod.fst.arg_self.revFDerivOptUpdate_rule
    (f : X → Y×Z) (hf : Differentiable K f) :
    revFDerivOptUpdate K (fun x => (f x).1)
    =
    fun x =>
      let yzdf := revFDerivOptProjUpdate K (Unit⊕Unit) f x
      (yzdf.1.1, fun dy dx => yzdf.2 (.inl ()) dy dx) := by
  unfold revFDerivOptProjUpdate; unfold revFDerivOptUpdate;
  fun_trans

@[fun_trans]
theorem Prod.fst.arg_self.revFDerivOptProj_rule
    (f : W → X'×Y) (hf : Differentiable K f) :
    revFDerivOptProj K Xi (fun x => (f x).1)
    =
    fun w =>
      let xydf := revFDerivOptProj K (Xi⊕Unit) f w
      (xydf.1.1,
       fun i dxy => xydf.2 (.inl i) dxy) := by
  unfold revFDerivOptProj
  funext x; fun_trans[revFDerivOptProj, oneHot, structMake]
  funext i de
  simp [revFDerivOpt]
  congr
  funext i
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only


@[fun_trans]
theorem Prod.fst.arg_self.revFDerivOptProjUpdate_rule
    (f : W → X'×Y) (hf : Differentiable K f) :
    revFDerivOptProjUpdate K Xi (fun x => (f x).1)
    =
    fun w =>
      let xydf := revFDerivOptProjUpdate K (Xi⊕Unit) f w
      (xydf.1.1,
       fun i dxy dw => xydf.2 (.inl i) dxy dw) := by
  unfold revFDerivOptProjUpdate
  funext x; fun_trans


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.snd.arg_self.revFDerivOpt_rule
    (f : X → Y×Z) (hf : Differentiable K f) :
    revFDerivOpt K (fun x => (f x).2)
    =
    fun x =>
      let yzdf := revFDerivOptProj K (Unit⊕Unit) f x
      (yzdf.1.2, fun dy => yzdf.2 (.inr ()) dy) := by
  unfold revFDerivOptProj; unfold revFDerivOpt
  fun_trans [oneHot]

@[fun_trans]
theorem Prod.snd.arg_self.revFDerivOptUpdate_rule
    (f : X → Y×Z) (hf : Differentiable K f) :
    revFDerivOptUpdate K (fun x => (f x).2)
    =
    fun x =>
      let yzdf := revFDerivOptProjUpdate K (Unit⊕Unit) f x
      (yzdf.1.2, fun dy dx => yzdf.2 (.inr ()) dy dx) := by
  unfold revFDerivOptProjUpdate; unfold revFDerivOptUpdate
  fun_trans

@[fun_trans]
theorem Prod.snd.arg_self.revFDerivOptProj_rule
    (f : W → X×Y') (hf : Differentiable K f) :
    revFDerivOptProj K Yi (fun x => (f x).2)
    =
    fun w =>
      let xydf := revFDerivOptProj K (Unit⊕Yi) f w
      (xydf.1.2,
       fun i dxy => xydf.2 (.inr i) dxy) := by
  unfold revFDerivOptProj
  funext x; fun_trans[revFDerivOptProj,oneHot]
  funext i de
  simp [revFDerivOpt]
  congr
  funext i
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only


@[fun_trans]
theorem Prod.snd.arg_self.revFDerivOptProjUpdate_rule
    (f : W → X×Y') (hf : Differentiable K f) :
    revFDerivOptProjUpdate K Yi (fun x => (f x).2)
    =
    fun w =>
      let xydf := revFDerivOptProjUpdate K (Unit⊕Yi) f w
      (xydf.1.2,
       fun i dxy dw => xydf.2 (.inr i) dxy dw) := by
  unfold revFDerivOptProjUpdate
  funext x; fun_trans


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revFDerivOpt_rule' :
    (revFDerivOpt K fun x : X×X => x.1+x.2)
    =
    fun x =>
      (x.1 + x.2,
       fun dy => (dy,dy)) := by
  unfold revFDerivOpt; simp; fun_trans

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revFDerivOpt_rule
    (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOpt K fun x => f x + g x)
    =
    fun x =>
      let ydf := revFDerivOpt K f x
      let ydg := revFDerivOptUpdate K g x
      (ydf.1 + ydg.1,
       fun dy =>
         let dx := ydf.2 dy
         ydg.2 dy dx) := by
  conv =>
    lhs
    fun_trans (config:={zeta:=false}) only [simp_core]
  -- unfold revFDerivOptUpdate; unfold revFDerivOpt; simp; fun_trans

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revFDerivOptUpdate_rule
    (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptUpdate K fun x => f x + g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let ydg := revFDerivOptUpdate K g x
      (ydf.1 + ydg.1,
       fun dy dx =>
         let dx := ydf.2 dy dx
         ydg.2 dy dx) := by
  unfold revFDerivOptUpdate
  fun_trans; funext x; simp[add_assoc,revFDerivOptUpdate]

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revFDerivOptProj_rule
    (f g : X → Y') (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptProj K Yi fun x => f x + g x)
    =
    fun x =>
      let ydf := revFDerivOptProj K Yi f x
      let ydg := revFDerivOptProjUpdate K Yi g x
      (ydf.1 + ydg.1,
       fun i dy =>
         let dx := ydf.2 i dy
         (ydg.2 i dy dx)) := by
  unfold revFDerivOptProjUpdate; unfold revFDerivOptProj
  fun_trans; simp[revFDerivOptUpdate]

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revFDerivOptProjUpdate_rule
    (f g : X → Y') (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptProjUpdate K Yi fun x => f x + g x)
    =
    fun x =>
      let ydf := revFDerivOptProjUpdate K Yi f x
      let ydg := revFDerivOptProjUpdate K Yi g x
      (ydf.1 + ydg.1,
       fun i dy dx =>
         let dx := ydf.2 i dy dx
         ydg.2 i dy dx) := by
  unfold revFDerivOptProjUpdate
  fun_trans; simp[revFDerivOptProjUpdate, add_assoc]


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSub.hSub.arg_a0a1.revFDerivOpt_rule
    (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOpt K fun x => f x - g x)
    =
    fun x =>
      let ydf := revFDerivOpt K f x
      let ydg := revFDerivOptUpdate K g x
      (ydf.1 - ydg.1,
       fun dy =>
         let dx := ydf.2 dy
         let dy' := -dy
         ydg.2 dy' dx) := by
  unfold revFDerivOptUpdate; unfold revFDerivOpt;
  fun_trans
  funext x; simp; funext dy; simp only [neg_pull, ← sub_eq_add_neg]

@[fun_trans]
theorem HSub.hSub.arg_a0a1.revFDerivOptUpdate_rule
    (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptUpdate K fun x => f x - g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let ydg := revFDerivOptUpdate K g x
      (ydf.1 - ydg.1,
       fun dy dx =>
         let dx := ydf.2 dy dx
         let dy' := -dy
         ydg.2 dy' dx) := by
  unfold revFDerivOptUpdate
  fun_trans; funext x; simp[add_assoc,revFDerivOptUpdate]

@[fun_trans]
theorem HSub.hSub.arg_a0a1.revFDerivOptProj_rule
    (f g : X → Y') (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptProj K Yi fun x => f x - g x)
    =
    fun x =>
      let ydf := revFDerivOptProj K Yi f x
      let ydg := revFDerivOptProjUpdate K Yi g x
      (ydf.1 - ydg.1,
       fun i dy =>
         let dx := ydf.2 i dy
         let dy' := -dy
         (ydg.2 i dy' dx)) := by
  unfold revFDerivOptProjUpdate; unfold revFDerivOptProj
  fun_trans; simp[revFDerivOptUpdate, revFDerivOpt]


@[fun_trans]
theorem HSub.hSub.arg_a0a1.revFDerivOptProjUpdate_rule
    (f g : X → Y') (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptProjUpdate K Yi fun x => f x - g x)
    =
    fun x =>
      let ydf := revFDerivOptProjUpdate K Yi f x
      let ydg := revFDerivOptProjUpdate K Yi g x
      (ydf.1 - ydg.1,
       fun i dy dx =>
         let dx := ydf.2 i dy dx
         let dy' := -dy
         ydg.2 i dy' dx) := by
  unfold revFDerivOptProjUpdate
  fun_trans; simp[revFDerivOptProjUpdate, revFDerivOptProj, revFDerivOpt,add_assoc]


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.revFDerivOpt_rule
    (f : X → Y) (x : X) :
    (revFDerivOpt K fun x => - f x) x
    =
    let ydf := revFDerivOpt K f x
    (-ydf.1,
     fun dy =>
       let dx := ydf.2 dy
       (-dx)) := by
  unfold revFDerivOpt; simp; fun_trans [Neg.neg]

@[fun_trans]
theorem Neg.neg.arg_a0.revFDerivOptUpdate_rule
    (f : X → Y) :
    (revFDerivOptUpdate K fun x => - f x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      (-ydf.1,
       fun dy dx =>
         let dy' := -dy
         ydf.2 dy' dx) := by
  unfold revFDerivOptUpdate; funext x; fun_trans; simp[neg_pull,revFDerivOpt]

@[fun_trans]
theorem Neg.neg.arg_a0.revFDerivOptProj_rule
    (f : X → Y') :
    (revFDerivOptProj K Yi fun x => - f x)
    =
    fun x =>
      let ydf := revFDerivOptProj K Yi f x
      (-ydf.1,
       fun i dy =>
         let dy' := -dy
         ydf.2 i dy') := by
  unfold revFDerivOptProj; fun_trans; simp[neg_push,revFDerivOpt]

@[fun_trans]
theorem Neg.neg.arg_a0.revFDerivOptProjUpdate_rule
    (f : X → Y') :
    (revFDerivOptProjUpdate K Yi fun x => - f x)
    =
    fun x =>
      let ydf := revFDerivOptProjUpdate K Yi f x
      (-ydf.1,
       fun i dy dx =>
         let dy' := -dy
         ydf.2 i dy' dx) := by
  unfold revFDerivOptProjUpdate; fun_trans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------
open ComplexConjugate

@[fun_trans]
theorem HMul.hMul.arg_a0a1.revFDerivOpt_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOpt K fun x => f x * g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let zdg := revFDerivOpt K g x
      (ydf.1 * zdg.1,
       fun dx' =>
         let dx₁ := (conj zdg.1 * dx')
         let dx₂ := (conj ydf.1 * dx')
         let dx := zdg.2 dx₂
         ydf.2 dx₁ dx) := by
  unfold revFDerivOptUpdate; unfold revFDerivOpt; simp; fun_trans
  simp [smul_push]

@[fun_trans]
theorem HMul.hMul.arg_a0a1.revFDerivOptUpdate_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptUpdate K fun x => f x * g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let zdg := revFDerivOptUpdate K g x
      (ydf.1 * zdg.1,
       fun dx' dx =>
         let dx₁ := (conj zdg.1 * dx')
         let dx₂ := (conj ydf.1 * dx')
         let dx := zdg.2 dx₂ dx
         ydf.2 dx₁ dx) := by
  unfold revFDerivOptUpdate; simp; fun_trans
  simp [smul_push,add_assoc,revFDerivOptUpdate]

@[fun_trans]
theorem HMul.hMul.arg_a0a1.revFDerivOptProj_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptProj K Unit fun x => f x * g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let zdg := revFDerivOpt K g x
      (ydf.1 * zdg.1,
       fun _ dy =>
         let dy₁ := (conj zdg.1)*dy
         let dy₂ := (conj ydf.1)*dy
         let dx := zdg.2 dy₂
         ydf.2 dy₁ dx) := by
  unfold revFDerivOptProj
  fun_trans; simp[oneHot, structMake]

@[fun_trans]
theorem HMul.hMul.arg_a0a1.revFDerivOptProjUpdate_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptProjUpdate K Unit fun x => f x * g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let zdg := revFDerivOptUpdate K g x
      (ydf.1 * zdg.1,
       fun _ dy dx =>
         let dy₁ := (conj zdg.1)*dy
         let dy₂ := (conj ydf.1)*dy
         let dx := zdg.2 dy₂ dx
         ydf.2 dy₁ dx) := by
  unfold revFDerivOptProjUpdate
  fun_trans; simp[revFDerivOptUpdate,add_assoc]


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

section SMulOnSemiHilbert

variable
  {Y Yi : Type} {YI : Yi → Type} [StructType Y Yi YI] [IndexType Yi] [DecidableEq Yi]
  [NormedAddCommGroup Y] [AdjointSpace K Y] [∀ i, NormedAddCommGroup (YI i)] [∀ i, AdjointSpace K (YI i)] [VecStruct K Y Yi YI]

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revFDerivOpt_rule
    (f : X → K) (g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOpt K fun x => f x • g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let zdg := revFDerivOpt K g x
      (ydf.1 • zdg.1,
       fun dy' =>
         let dk := inner zdg.1 dy'
         let dx := zdg.2 dy'
         let dx := conj ydf.1 • dx
         ydf.2 dk dx) := by
  unfold revFDerivOptUpdate; unfold revFDerivOpt
  fun_trans [smul_push]

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revFDerivOptUpdate_rule
    (f : X → K) (g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptUpdate K fun x => f x • g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let zdg := revFDerivOptUpdate K g x
      (ydf.1 • zdg.1,
       fun dy dx =>
         let dk := inner zdg.1 dy
         let dy' := conj ydf.1 • dy
         let dx := zdg.2 dy' dx
         ydf.2 dk dx) := by
  unfold revFDerivOptUpdate;
  funext x; fun_trans; simp[mul_assoc,add_assoc,revFDerivOptUpdate,revFDerivOpt,smul_push]

@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revFDerivOptProj_rule
    (f : X → K) (g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptProj K Yi fun x => f x • g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let zdg := revFDerivOptProj K Yi g x
      (ydf.1 • zdg.1,
       fun i (dy : YI i) =>
         let dk := inner (structProj zdg.1 i) dy
         let dx := zdg.2 i dy
         let dx := conj ydf.1•dx
         ydf.2 dk dx) := by
  unfold revFDerivOptProj; fun_trans
  funext x; simp; funext i de; simp [revFDerivOptUpdate,revFDerivOpt]
  sorry_proof


@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revFDerivOptProjUpdate_rule
    (f : X → K) (g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivOptProjUpdate K Yi fun x => f x • g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let zdg := revFDerivOptProjUpdate K Yi g x
      (ydf.1 • zdg.1,
       fun i (dy : YI i) dx =>
         let dk := inner (structProj zdg.1 i) dy
         let dy' := conj ydf.1•dy
         let dx := zdg.2 i dy' dx
         ydf.2 dk dx) := by
  unfold revFDerivOptProjUpdate
  fun_trans; simp[revFDerivOptUpdate,add_assoc,smul_pull]
  simp only [smul_pull,revFDerivOptProj,revFDerivOpt]

end SMulOnSemiHilbert


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revFDerivOpt_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) (hx : ∀ x, g x ≠ 0) :
    (revFDerivOpt K fun x => f x / g x)
    =
    fun x =>
      let ydf := revFDerivOpt K f x
      let zdg := revFDerivOptUpdate K g x
      (ydf.1 / zdg.1,
       fun dx' => (1 / (conj zdg.1)^2) • (zdg.2 (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 dx'))) := by
  unfold revFDerivOpt; simp
  fun_trans (disch:=apply hx)
  simp[revFDerivOptUpdate,smul_push,neg_pull,revFDerivOpt,smul_add,smul_sub, ← sub_eq_add_neg]

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revFDerivOptUpdate_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) (hx : ∀ x, g x ≠ 0) :
    (revFDerivOptUpdate K fun x => f x / g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let zdg := revFDerivOptUpdate K g x
      (ydf.1 / zdg.1,
       fun dx' dx =>
         let c := (1 / (conj zdg.1)^2)
         let a := -(c * conj ydf.1)
         let b := c * conj zdg.1
         ((zdg.2 (a • dx') (ydf.2 (b • dx') dx)))) := by
  funext
  simp[revFDerivOptUpdate]
  fun_trans (disch:=assumption)
  simp[revFDerivOptUpdate,smul_push,neg_pull,revFDerivOpt,smul_add,smul_sub,add_assoc,mul_assoc]


@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revFDerivOptProj_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) (hx : ∀ x, g x ≠ 0) :
    (revFDerivOptProj K Unit fun x => f x / g x)
    =
    fun x =>
      let ydf := revFDerivOpt K f x
      let zdg := revFDerivOptUpdate K g x
      (ydf.1 / zdg.1,
       fun _ dx' => (1 / (conj zdg.1)^2) • (zdg.2 (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 dx'))) :=
by
  unfold revFDerivOptProj
  fun_trans (disch:=assumption); simp[oneHot, structMake]

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revFDerivOptProjUpdate_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) (hx : ∀ x, g x ≠ 0) :
    (revFDerivOptProjUpdate K Unit fun x => f x / g x)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let zdg := revFDerivOptUpdate K g x
      (ydf.1 / zdg.1,
       fun _ dx' dx =>
         let c := (1 / (conj zdg.1)^2)
         let a := -(c * conj ydf.1)
         let b := c * conj zdg.1
         ((zdg.2 (a • dx') (ydf.2 (b • dx') dx)))) :=
by
  unfold revFDerivOptProjUpdate
  fun_trans (disch:=assumption)
  simp[revFDerivOptUpdate,revFDerivOpt,add_assoc,neg_pull,mul_assoc,smul_push]


-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
def HPow.hPow.arg_a0.revFDerivOpt_rule
    (f : X → K) (n : Nat) (hf : Differentiable K f) :
    revFDerivOpt K (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revFDerivOpt K f x
      let y' := (n : K) * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n,
       fun dx' => ydf.2 (y' * dx')) :=
by
  funext x
  unfold revFDerivOpt; simp; funext dx; fun_trans; simp[smul_push,smul_smul]; ring_nf

@[fun_trans]
def HPow.hPow.arg_a0.revFDerivOptUpdate_rule
    (f : X → K) (n : Nat) (hf : Differentiable K f) :
    revFDerivOptUpdate K (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let y' := n * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n,
       fun dy dx => ydf.2 (y' * dy) dx) := by
  unfold revFDerivOptUpdate
  funext x; fun_trans

@[fun_trans]
def HPow.hPow.arg_a0.revFDerivOptProj_rule
    (f : X → K) (n : Nat) (hf : Differentiable K f) :
    revFDerivOptProj K Unit (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revFDerivOpt K f x
      let y' := (n : K) * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n, fun _ dx' => ydf.2 (y' * dx')) := by
  unfold revFDerivOptProj; fun_trans; simp[oneHot,structMake]

@[fun_trans]
def HPow.hPow.arg_a0.revFDerivOptProjUpdate_rule
    (f : X → K) (n : Nat) (hf : Differentiable K f) :
    revFDerivOptProjUpdate K Unit (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      let y' := n * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n,
       fun _ dy dx => ydf.2 (y' * dy) dx) := by
  unfold revFDerivOptProjUpdate; fun_trans; simp[oneHot,structMake,revFDerivOptUpdate]


-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

section IndexTypeSum

variable {ι : Type} [IndexType ι]

@[fun_trans]
theorem IndexType.sum.arg_f.revFDerivOpt_rule
  (f : X → ι → Y) (hf : ∀ i, Differentiable K (fun x => f x i))
  : revFDerivOpt K (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := revFDerivOpt K f x
      (∑ i, ydf.1 i,
       fun dy =>
         ydf.2 (fun _ => dy)) :=
by
  unfold revFDerivOpt
  fun_trans;
  funext x; simp; funext dy;
  conv => rhs; rw[fderiv.pi_rule (hf := by fun_prop)];
  fun_trans


@[fun_trans]
theorem IndexType.sum.arg_f.revFDerivOptUpdate_rule
    (f : X → ι → Y) (hf : ∀ i, Differentiable K (fun x => f x i)) :
    revFDerivOptUpdate K (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := revFDerivOptUpdate K f x
      (∑ i, ydf.1 i,
       fun dy dx =>
         ydf.2 (fun _ => dy) dx) := by
  unfold revFDerivOptUpdate
  fun_trans

@[fun_trans]
theorem IndexType.sum.arg_f.revFDerivOptProj_rule [DecidableEq ι]
    (f : X → ι → Y') (hf : ∀ i, Differentiable K (fun x => f x i)) :
    revFDerivOptProj K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      -- this is not optimal
      -- we should have but right now there is no appropriate StrucLike instance
      -- let ydf := revFDerivOptProj K Yi f x
      let ydf := revFDerivOptProjUpdate K (ι×Yi) f x
      (∑ i, ydf.1 i,
       fun j dy =>
         IndexType.foldl (fun dx i => ydf.2 (i,j) dy dx) 0) := by
  unfold revFDerivOptProj
  fun_trans
  sorry_proof


@[fun_trans]
theorem IndexType.sum.arg_f.revFDerivOptProjUpdate_rule [DecidableEq ι]
    (f : X → ι → Y') (hf : ∀ i, Differentiable K (fun x => f x i)) :
    revFDerivOptProjUpdate K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := revFDerivOptProjUpdate K (ι×Yi) f x
      (∑ i, ydf.1 i,
       fun j dy dx =>
         IndexType.foldl (fun dx i => ydf.2 (i,j) dy dx) dx) := by
  sorry_proof


end IndexTypeSum


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem ite.arg_te.revFDerivOpt_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y) :
    revFDerivOpt K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revFDerivOpt K t y) (revFDerivOpt K e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem ite.arg_te.revFDerivOptUpdate_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y) :
    revFDerivOptUpdate K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revFDerivOptUpdate K t y) (revFDerivOptUpdate K e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem ite.arg_te.revFDerivOptProj_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y') :
    revFDerivOptProj K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revFDerivOptProj K Yi t y) (revFDerivOptProj K Yi e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem ite.arg_te.revFDerivOptProjUpdate_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y') :
    revFDerivOptProjUpdate K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revFDerivOptProjUpdate K Yi t y) (revFDerivOptProjUpdate K Yi e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]


@[fun_trans]
theorem dite.arg_te.revFDerivOpt_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y) (e : ¬c → X → Y) :
    revFDerivOpt K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revFDerivOpt K (t p) y)
             (fun p => revFDerivOpt K (e p) y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem dite.arg_te.revFDerivOptUpdate_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y) (e : ¬c → X → Y) :
    revFDerivOptUpdate K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revFDerivOptUpdate K (t p) y)
             (fun p => revFDerivOptUpdate K (e p) y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem dite.arg_te.revFDerivOptProj_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y') (e : ¬c → X → Y') :
    revFDerivOptProj K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revFDerivOptProj K Yi (t p) y)
             (fun p => revFDerivOptProj K Yi (e p) y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem dite.arg_te.revFDerivOptProjUpdate_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y') (e : ¬c → X → Y') :
    revFDerivOptProjUpdate K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revFDerivOptProjUpdate K Yi (t p) y)
             (fun p => revFDerivOptProjUpdate K Yi (e p) y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]


--------------------------------------------------------------------------------

section InnerProductSpace

variable
  {R : Type _} [RealScalar R]
  -- {K : Type _} [Scalar R K]
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace R Y]

-- Inner -----------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate

@[fun_trans]
theorem Inner.inner.arg_a0a1.revFDerivOpt_rule
    (f : X → Y) (g : X → Y) (hf : Differentiable R f) (hg : Differentiable R g) :
    (revFDerivOpt R fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revFDerivOpt R f x
      let y₂dg := revFDerivOptUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1))) := by
  funext; simp[revFDerivOpt,revFDerivOptUpdate]
  fun_trans[smul_pull]
  sorry_proof

@[fun_trans]
theorem Inner.inner.arg_a0a1.revFDerivOptUpdate_rule
    (f : X → Y) (g : X → Y) (hf : Differentiable R f) (hg : Differentiable R g) :
    (revFDerivOptUpdate R fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revFDerivOptUpdate R f x
      let y₂dg := revFDerivOptUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr dx =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1) dx) ) := by
  unfold revFDerivOptUpdate
  fun_trans; simp[revFDerivOptUpdate,add_assoc]

@[fun_trans]
theorem Inner.inner.arg_a0a1.revFDerivOptProj_rule
    (f : X → Y) (g : X → Y) (hf : Differentiable R f) (hg : Differentiable R g) :
    (revFDerivOptProj R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revFDerivOpt R f x
      let y₂dg := revFDerivOptUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1))) := by
  funext
  simp[revFDerivOptProj]
  fun_trans; simp[oneHot, structMake]

@[fun_trans]
theorem Inner.inner.arg_a0a1.revFDerivOptProjUpdate_rule
    (f : X → Y) (g : X → Y) (hf : Differentiable R f) (hg : Differentiable R g) :
    (revFDerivOptProjUpdate R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revFDerivOptUpdate R f x
      let y₂dg := revFDerivOptUpdate R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr dx =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1) dx)) := by
  funext
  simp[revFDerivOptProjUpdate]
  fun_trans; simp[revFDerivOptUpdate,add_assoc]


-- norm2 -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revFDerivOpt_rule
    (f : X → Y) (hf : Differentiable R f) :
    (revFDerivOpt R fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revFDerivOpt R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun dr =>
         ((2:R) * dr) • ydf.2 ydf.1) := by
  funext x; simp[revFDerivOpt]
  -- fun_trans[smul_smul]
  sorry_proof

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revFDerivOptUpdate_rule
    (f : X → Y) (hf : Differentiable R f) :
    (revFDerivOptUpdate R fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revFDerivOptUpdate R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun dr dx =>
          ydf.2 (((2:R)*dr)•ydf.1) dx) := by
  funext x; simp[revFDerivOptUpdate]
  fun_trans; simp[revFDerivOpt,smul_pull]

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revFDerivOptProj_rule
    (f : X → Y) (hf : Differentiable R f) :
    (revFDerivOptProj R Unit fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revFDerivOpt R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr =>
         ((2:R) * dr) • ydf.2 ydf.1) := by
  funext x; simp[revFDerivOptProj]
  fun_trans; simp[oneHot,structMake]

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revFDerivOptProjUpdate_rule
    (f : X → Y) (hf : Differentiable R f) :
    (revFDerivOptProjUpdate R Unit fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revFDerivOptUpdate R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr dx =>
          ydf.2 (((2:R)*dr)•ydf.1) dx) := by
  funext x; simp[revFDerivOptProjUpdate]
  fun_trans only; simp[revFDerivOpt,revFDerivOptUpdate,smul_pull]


-- norm₂ -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivOpt_rule_at
    (f : X → Y) (x : X) (hf : DifferentiableAt R f x) (hx : f x≠0) :
    (revFDerivOpt R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revFDerivOpt R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun dr =>
       (ynorm⁻¹ * dr) • ydf.2 ydf.1) := by
  simp[revFDerivOpt]
  sorry_proof
  -- fun_trans (disch:=assumption) only
  -- simp[smul_smul]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivOptUpdate_rule_at
    (f : X → Y) (x : X) (hf : DifferentiableAt R f x) (hx : f x≠0) :
    (revFDerivOptUpdate R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revFDerivOptUpdate R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun dr dx =>
       ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx) := by
  simp[revFDerivOptUpdate]
  fun_trans (disch:=assumption) only
  simp[revFDerivOpt,smul_pull]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivOptProj_rule_at
    (f : X → Y) (x : X) (hf : DifferentiableAt R f x) (hx : f x≠0) :
    (revFDerivOptProj R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revFDerivOpt R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr =>
       (ynorm⁻¹ * dr) • ydf.2 ydf.1):= by
  simp[revFDerivOptProj]
  fun_trans (disch:=assumption) only; simp[oneHot, structMake]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivOptProjUpdate_rule_at
    (f : X → Y) (x : X) (hf : DifferentiableAt R f x) (hx : f x≠0) :
    (revFDerivOptProjUpdate R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revFDerivOptUpdate R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr dx =>
       ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
by
  have ⟨_,_⟩ := hf
  simp[revFDerivOptProjUpdate]
  fun_trans (disch:=assumption) only
  simp[revFDerivOpt,revFDerivOptUpdate,smul_pull]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivOpt_rule
    (f : X → Y) (hf : Differentiable R f) (hx : ∀ x, f x≠0) :
    (revFDerivOpt R (fun x => ‖f x‖₂[R]))
    =
    fun x =>
      let ydf := revFDerivOpt R f x
      let ynorm := ‖ydf.1‖₂[R]
      (ynorm,
       fun dr =>
         (ynorm⁻¹ * dr) • ydf.2 ydf.1):=
by
  unfold revFDerivOpt
  funext x; simp
  -- fun_trans (disch:=assumption)
  -- simp[smul_smul]
  sorry_proof

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivOptUpdate_rule
    (f : X → Y) (hf : Differentiable R f) (hx : ∀ x, f x≠0) :
    (revFDerivOptUpdate R (fun x => ‖f x‖₂[R]))
    =
    fun x =>
      let ydf := revFDerivOptUpdate R f x
      let ynorm := ‖ydf.1‖₂[R]
      (ynorm,
       fun dr dx =>
         ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
by
  unfold revFDerivOptUpdate
  funext x; simp
  fun_trans (disch:=assumption) only
  simp[revFDerivOpt,smul_pull]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivOptProj_rule
    (f : X → Y) (hf : Differentiable R f) (hx : ∀ x, f x≠0) :
    (revFDerivOptProj R Unit (fun x => ‖f x‖₂[R]))
    =
    fun x =>
      let ydf := revFDerivOpt R f x
      let ynorm := ‖ydf.1‖₂[R]
      (ynorm,
       fun _ dr =>
         (ynorm⁻¹ * dr) • ydf.2 ydf.1) := by
  unfold revFDerivOptProj
  funext x; simp
  fun_trans (disch:=assumption) only
  simp[oneHot, structMake]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivOptProjUpdate_rule
    (f : X → Y) (hf : Differentiable R f) (hx : ∀ x, f x≠0) :
    (revFDerivOptProjUpdate R Unit (fun x => ‖f x‖₂[R]))
    =
    fun x =>
       let ydf := revFDerivOptUpdate R f x
       let ynorm := ‖ydf.1‖₂[R]
       (ynorm,
        fun _ dr dx =>
          ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx) := by
  unfold revFDerivOptProjUpdate
  funext x; simp
  fun_trans (disch:=assumption) only
  simp[revFDerivOpt,revFDerivOptUpdate,smul_pull]

end InnerProductSpace
