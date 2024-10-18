import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.AdjointSpace.Adjoint
import SciLean.Analysis.FunctionSpaces.SmoothLinearMap
import SciLean.Tactic.StructureDecomposition

import SciLean.Data.StructType.Algebra

import SciLean.Tactic.Autodiff

set_option linter.unusedVariables false

namespace SciLean

set_option deprecated.oldSectionVars true

variable
  (K I : Type) [RCLike K]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace K W] [CompleteSpace W]
  {ι : Type} [IndexType ι] [DecidableEq ι]
  {κ : Type} [IndexType κ] [DecidableEq κ]
  {E : Type} {EI : I → Type}
  [StructType E I EI] [IndexType I] [DecidableEq I]
  [NormedAddCommGroup E] [AdjointSpace K E] [CompleteSpace E] [∀ i, NormedAddCommGroup (EI i)] [∀ i, AdjointSpace K (EI i)] [∀ i, CompleteSpace (EI i)]
  [VecStruct K E I EI] -- todo: define AdjointSpaceStruct
  {F J : Type} {FJ : J → Type}
  [StructType F J FJ] [IndexType J] [DecidableEq J]
  [NormedAddCommGroup F] [AdjointSpace K F] [CompleteSpace F] [∀ j, NormedAddCommGroup (FJ j)] [∀ j, AdjointSpace K (FJ j)] [∀ j, CompleteSpace (FJ j)]
  [VecStruct K F J FJ] -- todo: define AdjointSpaceStruct



@[fun_trans]
noncomputable
def revFDerivProj [DecidableEq I]
  (f : X → E) (x : X) : E×((i : I)→EI i→X) :=
  (f x, fun i de =>
    adjoint K (fderiv K f x) (oneHot i de))

@[fun_trans]
noncomputable
def revFDerivProjUpdate [DecidableEq I]
  (f : X → E) (x : X) : E×((i : I)→EI i→X→X) :=
  let ydf' := revFDerivProj K I f x
  (ydf'.1, fun i de dx => dx + ydf'.2 i de)


--------------------------------------------------------------------------------
-- simplification rules for individual components ------------------------------
--------------------------------------------------------------------------------

@[simp, simp_core]
theorem revFDerivProj_fst (f : X → E) (x : X)
  : (revFDerivProj K (I:=I) f x).1 = f x :=
by
  rfl

@[simp, simp_core]
theorem revFDerivProj_snd_zero (f : X → E) (x : X) (i : I)
  : (revFDerivProj K I f x).2 i 0 = 0 :=
by
  simp[revFDerivProj]

@[simp, simp_core]
theorem revFDerivProjUpdate_fst (f : X → E) (x : X)
  : (revFDerivProjUpdate K I f x).1 = f x :=
by
  rfl

@[simp, simp_core]
theorem revFDerivProjUpdate_snd_zero (f : X → E) (x dx : X) (i : I)
  : (revFDerivProjUpdate K I f x).2 i 0 dx = dx :=
by
  simp[revFDerivProjUpdate]


theorem revFDeriv_eq_revFDerivProj (f : X → Y) :
  revFDeriv K f
  =
  fun x =>
    let ydf := revFDerivProj K Unit f x
    (ydf.1, fun dy => ydf.2 () dy) := by unfold revFDerivProj revFDeriv; simp


--------------------------------------------------------------------------------
-- Lambda calculus rules for revFDerivProj ------------------------------------
--------------------------------------------------------------------------------

namespace revFDerivProj

@[fun_trans]
theorem id_rule :
    revFDerivProj K I (fun x : E => x)
    =
    fun x =>
      (x,
       fun i de =>
         oneHot i de) := by
  unfold revFDerivProj; fun_trans

@[fun_trans]
theorem const_rule (x : E)
  : revFDerivProj K I (fun _ : Y => x)
    =
    fun _ =>
      (x,
       fun i (de : EI i) => 0) := by
  unfold revFDerivProj; fun_trans

@[fun_trans]
theorem apply_rule [DecidableEq I] (i : ι) :
    revFDerivProj K I (fun (f : ι → E) => f i)
    =
    fun f : ι → E =>
      (f i, fun j dxj => oneHot (X:=ι→E) (I:=ι×I) (i,j) dxj) :=
by
  unfold revFDerivProj;
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
    revFDerivProj K I (fun x => f (g x))
    =
    fun x =>
      let ydg' := revFDerivProj K Unit g x
      let zdf' := revFDerivProj K I f ydg'.1
      (zdf'.1,
       fun i de =>
         ydg'.2 () (zdf'.2 i de)) := by
  unfold revFDerivProj; fun_trans

@[fun_trans]
theorem let_rule
    (f : X → Y → E) (g : X → Y)
    (hf : Differentiable K (fun (x,y) => f x y)) (hg : Differentiable K g) :
    revFDerivProj K I (fun x => let y := g x; f x y)
    =
    fun x =>
      let ydg' := revFDerivProjUpdate K Unit g x
      let zdf' := revFDerivProj K I (fun (x,y) => f x y) (x,ydg'.1)
      (zdf'.1,
       fun i dei =>
         let dxy := zdf'.2 i dei
         ydg'.2 () dxy.2 dxy.1) := by
  unfold revFDerivProj revFDerivProjUpdate; fun_trans [oneHot,revFDerivProj]

@[fun_trans]
theorem pi_rule_unit
    (f :  X → ι → Y) (hf : ∀ i, Differentiable K (f · i)) :
    (revFDerivProj K Unit fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let ydf := fun i => revFDerivProjUpdate K Unit (f · i) x
      (fun i => (ydf i).1,
       fun _ df =>
         IndexType.foldl (fun dx i => (ydf i).2 () (df i) dx) (0 : X)) := by
  unfold revFDerivProj
  fun_trans
  funext x; simp; funext i de
  sorry_proof


@[fun_trans]
theorem pi_rule
    (f :  X → ι → E) (hf : ∀ i, Differentiable K (f · i)) :
    (revFDerivProj K (ι×I) fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      (fun i => f x i,
       fun (i,i') df =>
         let dx := (revFDerivProj K I (f · i) x).2 i' df
         dx) := by
  unfold revFDerivProj
  fun_trans
  funext x; simp; funext i de
  sorry_proof


section PiRuleNonDep


variable
  {E : Type} {EI : Type}
  [StructType E I (fun _ => EI)]
  [NormedAddCommGroup E] [AdjointSpace K E] [NormedAddCommGroup EI] [AdjointSpace K EI]
  [VecStruct K E I (fun _ => EI)]


-- The is some unification problem when applying the dependent version `pi_rule`
-- Zulip question: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unification.20failure.20in.20simp
@[fun_trans]
theorem pi_rule_nondep
    (f :  X → ι → E) (hf : ∀ i, Differentiable K (f · i)) :
    (revFDerivProj K (ι×I) fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      (fun i => f x i,
       fun (i,i') df =>
         let dx := (revFDerivProj K I (f · i) x).2 i' df
         dx) := by
  rw[pi_rule K I f hf]

end PiRuleNonDep



end revFDerivProj


--------------------------------------------------------------------------------
-- Lambda calculus rules for revFDerivProjUpdate --------------------------------
--------------------------------------------------------------------------------

namespace revFDerivProjUpdate

@[fun_trans]
theorem id_rule
  : revFDerivProjUpdate K I (fun x : E => x)
    =
    fun x =>
      (x,
       fun i de dx =>
         structModify i (fun ei => ei + de) dx) :=
by
  funext x
  simp[revFDerivProjUpdate, revFDerivProj.id_rule]
  sorry_proof


@[fun_trans]
theorem const_rule (x : E)
  : revFDerivProjUpdate K I (fun _ : Y => x)
    =
    fun _ =>
      (x,
       fun i de dx => dx) :=
by
  unfold revFDerivProjUpdate; simp[revFDerivProj.const_rule]

@[fun_trans]
theorem comp_rule
  (f : Y → E) (g : X → Y)
  (hf : Differentiable K f) (hg : Differentiable K g)
  : revFDerivProjUpdate K I (fun x => f (g x))
    =
    fun x =>
      let ydg' := revFDerivProjUpdate K Unit g x
      let zdf' := revFDerivProj K I f ydg'.1
      (zdf'.1,
       fun i de dx =>
         ydg'.2 () (zdf'.2 i de) dx) :=
by
  funext x
  simp[revFDerivProjUpdate,revFDerivProj.comp_rule _ _ _ _ hf hg]


@[fun_trans]
theorem let_rule
  (f : X → Y → E) (g : X → Y)
  (hf : Differentiable K (fun (x,y) => f x y)) (hg : Differentiable K g)
  : revFDerivProjUpdate K I (fun x => let y := g x; f x y)
    =
    fun x =>
      let ydg' := revFDerivProjUpdate K Unit g x
      let zdf' := revFDerivProjUpdate K I (fun (x,y) => f x y) (x,ydg'.1)
      (zdf'.1,
       fun i dei dx =>
         let dxy := zdf'.2 i dei (dx,0)
         ydg'.2 () dxy.2 dxy.1) :=
by
  unfold revFDerivProjUpdate
  simp [revFDerivProj.let_rule _ _ _ _ hf hg,add_assoc,add_comm,revFDerivProjUpdate]

@[fun_trans]
theorem apply_rule [DecidableEq I] (i : ι)
  : revFDerivProjUpdate K I (fun (f : ι → E) => f i)
    =
    fun f =>
      (f i, fun j dxj df i' =>
        if i=i' then
          structModify j (fun xj => xj + dxj) (df i')
        else
          df i') :=
by
  funext x;
  unfold revFDerivProjUpdate
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
theorem pi_rule_unit
    (f :  X → ι → Y) (hf : ∀ i, Differentiable K (f · i)) :
    (revFDerivProjUpdate K Unit fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let ydf := fun i => revFDerivProjUpdate K Unit (f · i) x
      (fun i => (ydf i).1,
       fun _ df dx =>
         IndexType.foldl (fun dx i => (ydf i).2 () (df i) dx) dx) :=
by
  unfold revFDerivProjUpdate
  fun_trans
  unfold revFDerivProj
  funext x; simp; funext i de dx
  simp[oneHot,revFDerivProjUpdate]
  sorry_proof


@[fun_trans]
theorem pi_rule
    (f :  X → ι → E) (hf : ∀ i, Differentiable K (f · i)) :
    (revFDerivProjUpdate K (ι×I) fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      (fun i => f x i,
       fun (i,i') df dx =>
         let dx := (revFDerivProjUpdate K I (f · i) x).2 i' df dx
         dx) := by
  unfold revFDerivProjUpdate
  fun_trans
  funext x; simp; funext i de
  sorry_proof

section PiRuleNonDep

variable
  {E : Type} {EI : Type}
  [StructType E I (fun _ => EI)]
  [NormedAddCommGroup E] [AdjointSpace K E] [NormedAddCommGroup EI] [AdjointSpace K EI]
  [VecStruct K E I (fun _ => EI)]

@[fun_trans]
theorem pi_rule_nondep
    (f :  X → ι → E) (hf : ∀ i, Differentiable K (f · i)) :
    (revFDerivProjUpdate K (ι×I) fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      (fun i => f x i,
       fun (i,i') df dx =>
         let dx := (revFDerivProjUpdate K I (f · i) x).2 i' df dx
         dx) := pi_rule K I f hf

end PiRuleNonDep


end revFDerivProjUpdate


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

end SciLean
open SciLean

set_option deprecated.oldSectionVars true

variable
  {K : Type} [RCLike K]
  {ι : Type} [IndexType ι] [DecidableEq ι]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z] [CompleteSpace Z]
  {X' Xi : Type} {XI : Xi → Type} [StructType X' Xi XI] [IndexType Xi] [DecidableEq Xi]
  {Y' Yi : Type} {YI : Yi → Type} [StructType Y' Yi YI] [IndexType Yi] [DecidableEq Yi]
  {Z' Zi : Type} {ZI : Zi → Type} [StructType Z' Zi ZI] [IndexType Zi] [DecidableEq Zi]
  [NormedAddCommGroup X'] [AdjointSpace K X'] [CompleteSpace X'] [∀ i, NormedAddCommGroup (XI i)] [∀ i, AdjointSpace K (XI i)] [∀ i, CompleteSpace (XI i)] [VecStruct K X' Xi XI]
  [NormedAddCommGroup Y'] [AdjointSpace K Y'] [CompleteSpace Y'] [∀ i, NormedAddCommGroup (YI i)] [∀ i, AdjointSpace K (YI i)] [∀ i, CompleteSpace (YI i)] [VecStruct K Y' Yi YI]
  [NormedAddCommGroup Z'] [AdjointSpace K Z'] [CompleteSpace Z'] [∀ i, NormedAddCommGroup (ZI i)] [∀ i, AdjointSpace K (ZI i)] [∀ i, CompleteSpace (ZI i)] [VecStruct K Z' Zi ZI]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace K W] [CompleteSpace W]




-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_trans]
theorem Prod.mk.arg_fstsnd.revFDerivProj_rule
    (g : X → Y') (f : X → Z')
    (hg : Differentiable K g) (hf : Differentiable K f) :
    revFDerivProj K (Yi⊕Zi) (fun x => (g x, f x))
    =
    fun x =>
      let ydg := revFDerivProj K Yi g x
      let zdf := revFDerivProj K Zi f x
      ((ydg.1,zdf.1),
       fun i dyz =>
         match i with
         | .inl j => ydg.2 j dyz
         | .inr j => zdf.2 j dyz) := by
  unfold revFDerivProj
  funext x; fun_trans
  funext i dyz
  induction i <;>
    { simp[oneHot,structMake]
      apply congr_arg
      congr; funext i; congr; funext h
      subst h; rfl
    }

@[fun_trans]
theorem Prod.mk.arg_fstsnd.revFDerivProjUpdate_rule
    (g : X → Y') (f : X → Z')
    (hg : Differentiable K g) (hf : Differentiable K f) :
    revFDerivProjUpdate K (Yi⊕Zi) (fun x => (g x, f x))
    =
    fun x =>
      let ydg := revFDerivProjUpdate K Yi g x
      let zdf := revFDerivProjUpdate K Zi f x
      ((ydg.1,zdf.1),
       fun i dyz dx =>
         match i with
         | .inl j => ydg.2 j dyz dx
         | .inr j => zdf.2 j dyz dx) := by
  unfold revFDerivProjUpdate
  funext x; fun_trans
  funext i de dx
  induction i <;> simp


@[fun_trans]
theorem Prod.mk.arg_fstsnd.revFDerivProj_rule_unit
    (g : X → Y') (f : X → Z')
    (hg : Differentiable K g) (hf : Differentiable K f) :
    revFDerivProj K Unit (fun x => (g x, f x))
    =
    fun x =>
      let ydg := revFDerivProj K Unit g x
      let zdf := revFDerivProjUpdate K Unit f x
      ((ydg.1,zdf.1),
       fun i dyz =>
         let dx := ydg.2 () dyz.1
         zdf.2 () dyz.2 dx) := by
  unfold revFDerivProj
  funext x; fun_trans [revFDerivProjUpdate,revFDerivProj,oneHot]


@[fun_trans]
theorem Prod.mk.arg_fstsnd.revFDerivProjUpdate_rule_unit
    (g : X → Y') (f : X → Z')
    (hg : Differentiable K g) (hf : Differentiable K f) :
    revFDerivProjUpdate K Unit (fun x => (g x, f x))
    =
    fun x =>
      let ydg := revFDerivProjUpdate K Unit g x
      let zdf := revFDerivProjUpdate K Unit f x
      ((ydg.1,zdf.1),
       fun i dyz dx =>
         let dx := ydg.2 () dyz.1 dx
         zdf.2 () dyz.2 dx) := by
  unfold revFDerivProjUpdate
  funext x; fun_trans; simp [revFDerivProjUpdate,revFDerivProj,oneHot,add_assoc]


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.fst.arg_self.revFDerivProj_rule
    (f : W → X'×Y) (hf : Differentiable K f) :
    revFDerivProj K Xi (fun x => (f x).1)
    =
    fun w =>
      let xydf := revFDerivProj K (Xi⊕Unit) f w
      (xydf.1.1,
       fun i dxy => xydf.2 (.inl i) dxy) := by
  unfold revFDerivProj
  funext x; fun_trans[revFDerivProj, oneHot, structMake]
  funext i de
  congr
  funext i
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only


@[fun_trans]
theorem Prod.fst.arg_self.revFDerivProjUpdate_rule
    (f : W → X'×Y) (hf : Differentiable K f) :
    revFDerivProjUpdate K Xi (fun x => (f x).1)
    =
    fun w =>
      let xydf := revFDerivProjUpdate K (Xi⊕Unit) f w
      (xydf.1.1,
       fun i dxy dw => xydf.2 (.inl i) dxy dw) := by
  unfold revFDerivProjUpdate
  funext x; fun_trans


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.snd.arg_self.revFDerivProj_rule
    (f : W → X×Y') (hf : Differentiable K f) :
    revFDerivProj K Yi (fun x => (f x).2)
    =
    fun w =>
      let xydf := revFDerivProj K (Unit⊕Yi) f w
      (xydf.1.2,
       fun i dxy => xydf.2 (.inr i) dxy) := by
  unfold revFDerivProj
  funext x; fun_trans[revFDerivProj,oneHot]
  funext i de
  congr
  funext i
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only


@[fun_trans]
theorem Prod.snd.arg_self.revFDerivProjUpdate_rule
    (f : W → X×Y') (hf : Differentiable K f) :
    revFDerivProjUpdate K Yi (fun x => (f x).2)
    =
    fun w =>
      let xydf := revFDerivProjUpdate K (Unit⊕Yi) f w
      (xydf.1.2,
       fun i dxy dw => xydf.2 (.inr i) dxy dw) := by
  unfold revFDerivProjUpdate
  funext x; fun_trans


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revFDerivProj_rule
    (f g : X → Y') (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivProj K Yi fun x => f x + g x)
    =
    fun x =>
      let ydf := revFDerivProj K Yi f x
      let ydg := revFDerivProjUpdate K Yi g x
      (ydf.1 + ydg.1,
       fun i dy =>
         let dx := ydf.2 i dy
         (ydg.2 i dy dx)) := by
  unfold revFDerivProjUpdate; unfold revFDerivProj
  fun_trans

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.revFDerivProjUpdate_rule
    (f g : X → Y') (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivProjUpdate K Yi fun x => f x + g x)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K Yi f x
      let ydg := revFDerivProjUpdate K Yi g x
      (ydf.1 + ydg.1,
       fun i dy dx =>
         let dx := ydf.2 i dy dx
         ydg.2 i dy dx) := by
  unfold revFDerivProjUpdate
  fun_trans; simp[revFDerivProjUpdate, add_assoc]


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSub.hSub.arg_a0a1.revFDerivProj_rule
    (f g : X → Y') (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivProj K Yi fun x => f x - g x)
    =
    fun x =>
      let ydf := revFDerivProj K Yi f x
      let ydg := revFDerivProjUpdate K Yi g x
      (ydf.1 - ydg.1,
       fun i dy =>
         let dx := ydf.2 i dy
         let dy' := -dy
         (ydg.2 i dy' dx)) := by
  unfold revFDerivProjUpdate; unfold revFDerivProj
  fun_trans
  sorry_proof


@[fun_trans]
theorem HSub.hSub.arg_a0a1.revFDerivProjUpdate_rule
    (f g : X → Y') (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivProjUpdate K Yi fun x => f x - g x)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K Yi f x
      let ydg := revFDerivProjUpdate K Yi g x
      (ydf.1 - ydg.1,
       fun i dy dx =>
         let dx := ydf.2 i dy dx
         let dy' := -dy
         ydg.2 i dy' dx) := by
  unfold revFDerivProjUpdate
  fun_trans; simp[revFDerivProjUpdate, revFDerivProj,add_assoc]


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.revFDerivProj_rule
    (f : X → Y') :
    (revFDerivProj K Yi fun x => - f x)
    =
    fun x =>
      let ydf := revFDerivProj K Yi f x
      (-ydf.1,
       fun i dy =>
         let dy' := -dy
         ydf.2 i dy') := by
  unfold revFDerivProj; fun_trans; simp[neg_push]

@[fun_trans]
theorem Neg.neg.arg_a0.revFDerivProjUpdate_rule
    (f : X → Y') :
    (revFDerivProjUpdate K Yi fun x => - f x)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K Yi f x
      (-ydf.1,
       fun i dy dx =>
         let dy' := -dy
         ydf.2 i dy' dx) := by
  unfold revFDerivProjUpdate; fun_trans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------
open ComplexConjugate

@[fun_trans]
theorem HMul.hMul.arg_a0a1.revFDerivProj_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivProj K Unit fun x => f x * g x)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K Unit f x
      let zdg := revFDerivProj K Unit g x
      (ydf.1 * zdg.1,
       fun _ dy =>
         let dy₁ := (conj zdg.1)*dy
         let dy₂ := (conj ydf.1)*dy
         let dx := zdg.2 () dy₂
         ydf.2 () dy₁ dx) := by
  unfold revFDerivProj
  fun_trans; simp[oneHot, structMake,revFDerivProjUpdate, revFDerivProj, smul_push]

@[fun_trans]
theorem HMul.hMul.arg_a0a1.revFDerivProjUpdate_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivProjUpdate K Unit fun x => f x * g x)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K Unit f x
      let zdg := revFDerivProjUpdate K Unit g x
      (ydf.1 * zdg.1,
       fun _ dy dx =>
         let dy₁ := (conj zdg.1)*dy
         let dy₂ := (conj ydf.1)*dy
         let dx := zdg.2 () dy₂ dx
         ydf.2 () dy₁ dx) := by
  unfold revFDerivProjUpdate
  fun_trans; simp[revFDerivProjUpdate,add_assoc]


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

section SMulOnSemiHilbert

variable
  {Y Yi : Type} {YI : Yi → Type} [StructType Y Yi YI] [IndexType Yi] [DecidableEq Yi]
  [NormedAddCommGroup Y] [AdjointSpace K Y] [∀ i, NormedAddCommGroup (YI i)] [∀ i, AdjointSpace K (YI i)] [VecStruct K Y Yi YI]


@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revFDerivProj_rule
    (f : X → K) (g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivProj K Yi fun x => f x • g x)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K Unit f x
      let zdg := revFDerivProj K Yi g x
      (ydf.1 • zdg.1,
       fun i (dy : YI i) =>
         let dk := inner (structProj zdg.1 i) dy
         let dy' := conj ydf.1•dy
         let dx := zdg.2 i dy'
         ydf.2 () dk dx) := by
  unfold revFDerivProjUpdate revFDerivProj
  fun_trans [smul_push]
  sorry_proof


@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.revFDerivProjUpdate_rule
    (f : X → K) (g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g) :
    (revFDerivProjUpdate K Yi fun x => f x • g x)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K Unit f x
      let zdg := revFDerivProjUpdate K Yi g x
      (ydf.1 • zdg.1,
       fun i (dy : YI i) dx =>
         let dk := inner (structProj zdg.1 i) dy
         let dy' := conj ydf.1•dy
         let dx := zdg.2 i dy' dx
         ydf.2 () dk dx) := by
  unfold revFDerivProjUpdate
  fun_trans; simp[revFDerivProjUpdate,add_assoc,smul_pull]

end SMulOnSemiHilbert


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revFDerivProj_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) (hx : ∀ x, g x ≠ 0) :
    (revFDerivProj K Unit fun x => f x / g x)
    =
    fun x =>
      let ydf := revFDerivProj K Unit f x
      let zdg := revFDerivProjUpdate K Unit g x
      (ydf.1 / zdg.1,
       fun _ dx' => (1 / (conj zdg.1)^2) • (zdg.2 () (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 () dx'))) :=
by
  unfold revFDerivProj
  fun_trans (disch:=apply hx); simp[oneHot, structMake,revFDerivProjUpdate,revFDerivProj,smul_push]
  sorry_proof

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revFDerivProjUpdate_rule
    (f g : X → K) (hf : Differentiable K f) (hg : Differentiable K g) (hx : ∀ x, g x ≠ 0) :
    (revFDerivProjUpdate K Unit fun x => f x / g x)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K Unit f x
      let zdg := revFDerivProjUpdate K Unit g x
      (ydf.1 / zdg.1,
       fun _ dx' dx =>
         let c := (1 / (conj zdg.1)^2)
         let a := -(c * conj ydf.1)
         let b := c * conj zdg.1
         ((zdg.2 () (a • dx') (ydf.2 () (b • dx') dx)))) :=
by
  unfold revFDerivProjUpdate
  fun_trans (disch:=assumption)
  simp[revFDerivProjUpdate,revFDerivProj,add_assoc,neg_pull,mul_assoc,smul_push]


@[fun_trans]
theorem HDiv.hDiv.arg_a0.revFDerivProj_rule
    (f : X → K) (y : K) (hf : Differentiable K f) :
    (revFDerivProj K Unit fun x => f x / y)
    =
    fun x =>
      let ydf := revFDerivProj K Unit f x
      (ydf.1 / y,
       fun _ dx' => (1 / (conj y)) • (ydf.2 () dx')) :=
by
  unfold revFDerivProj
  fun_trans (disch:=apply hx); simp[oneHot, structMake,revFDerivProjUpdate,revFDerivProj,smul_push]


@[fun_trans]
theorem HDiv.hDiv.arg_a0.revFDerivProjUpdate_rule
    (f : X → K) (y : K) (hf : Differentiable K f) :
    (revFDerivProjUpdate K Unit fun x => f x / y)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K Unit f x
      (ydf.1 / y,
       fun _ dx' dx =>
         let c := (1 / (conj y))
         ((ydf.2 () (c • dx') dx))) :=
by
  unfold revFDerivProjUpdate
  fun_trans (disch:=assumption)
  simp[revFDerivProjUpdate,revFDerivProj,add_assoc,neg_pull,mul_assoc,smul_push]


-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
def HPow.hPow.arg_a0.revFDerivProj_rule
    (f : X → K) (n : Nat) (hf : Differentiable K f) :
    revFDerivProj K Unit (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revFDerivProj K Unit f x
      let y' := (n : K) * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n, fun _ dx' => ydf.2 () (y' * dx')) := by
  unfold revFDerivProj; fun_trans; simp[oneHot,structMake,smul_push,mul_comm,mul_assoc]

@[fun_trans]
def HPow.hPow.arg_a0.revFDerivProjUpdate_rule
    (f : X → K) (n : Nat) (hf : Differentiable K f) :
    revFDerivProjUpdate K Unit (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K Unit f x
      let y' := n * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n,
       fun _ dy dx => ydf.2 () (y' * dy) dx) := by
  unfold revFDerivProjUpdate; fun_trans


-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

section IndexTypeSum


@[fun_trans]
theorem IndexType.sum.arg_f.revFDerivProj_rule
    (f : X → ι → Y') (hf : ∀ i, Differentiable K (fun x => f x i)) :
    revFDerivProj K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K (ι×Yi) f x
      (∑ i, ydf.1 i,
       fun j dy =>
         IndexType.foldl (fun dx i => ydf.2 (i,j) dy dx) 0) := by
  unfold revFDerivProj
  fun_trans
  sorry_proof


@[fun_trans]
theorem IndexType.sum.arg_f.revFDerivProjUpdate_rule
    (f : X → ι → Y') (hf : ∀ i, Differentiable K (fun x => f x i)) :
    revFDerivProjUpdate K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := revFDerivProjUpdate K (ι×Yi) f x
      (∑ i, ydf.1 i,
       fun j dy dx =>
         IndexType.foldl (fun dx i => ydf.2 (i,j) dy dx) dx) := by
  sorry_proof


end IndexTypeSum


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem ite.arg_te.revFDerivProj_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y') :
    revFDerivProj K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revFDerivProj K Yi t y) (revFDerivProj K Yi e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem ite.arg_te.revFDerivProjUpdate_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y') :
    revFDerivProjUpdate K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revFDerivProjUpdate K Yi t y) (revFDerivProjUpdate K Yi e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]


@[fun_trans]
theorem dite.arg_te.revFDerivProj_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y') (e : ¬c → X → Y') :
    revFDerivProj K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revFDerivProj K Yi (t p) y)
             (fun p => revFDerivProj K Yi (e p) y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem dite.arg_te.revFDerivProjUpdate_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y') (e : ¬c → X → Y') :
    revFDerivProjUpdate K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revFDerivProjUpdate K Yi (t p) y)
             (fun p => revFDerivProjUpdate K Yi (e p) y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]


--------------------------------------------------------------------------------

section InnerProductSpace

variable
  {R : Type} [RealScalar R]
  -- {K : Type _} [Scalar R K]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]

-- Inner -----------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate


@[fun_trans]
theorem Inner.inner.arg_a0a1.revFDerivProj_rule
    (f : X → Y) (g : X → Y) (hf : Differentiable R f) (hg : Differentiable R g) :
    (revFDerivProj R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revFDerivProj R Unit f x
      let y₂dg := revFDerivProjUpdate R Unit g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr =>
         y₂dg.2 () (dr • y₁df.1) (y₁df.2 () (dr • y₂dg.1))) := by
  funext
  simp[revFDerivProj]
  sorry_proof
  -- fun_trans; simp[oneHot, structMake]

@[fun_trans]
theorem Inner.inner.arg_a0a1.revFDerivProjUpdate_rule
    (f : X → Y) (g : X → Y) (hf : Differentiable R f) (hg : Differentiable R g) :
    (revFDerivProjUpdate R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revFDerivProjUpdate R Unit f x
      let y₂dg := revFDerivProjUpdate R Unit g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr dx =>
         y₂dg.2 () (dr • y₁df.1) (y₁df.2 () (dr • y₂dg.1) dx)) := by
  funext
  simp[revFDerivProjUpdate]
  fun_trans; simp[revFDerivProjUpdate,add_assoc]


-- norm2 -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revFDerivProj_rule
    (f : X → Y) (hf : Differentiable R f) :
    (revFDerivProj R Unit fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revFDerivProj R Unit f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr =>
         ((2:R) * dr) • ydf.2 () ydf.1) := by
  funext x; simp[revFDerivProj]
  sorry_proof
  -- fun_trans; simp[oneHot,structMake]

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revFDerivProjUpdate_rule
    (f : X → Y) (hf : Differentiable R f) :
    (revFDerivProjUpdate R Unit fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revFDerivProjUpdate R Unit f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr dx =>
          ydf.2 () (((2:R)*dr)•ydf.1) dx) := by
  funext x; simp[revFDerivProjUpdate]
  fun_trans only; simp[revFDerivProj,revFDerivProjUpdate,smul_pull]


-- norm₂ -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivProj_rule_at
    (f : X → Y) (x : X) (hf : DifferentiableAt R f x) (hx : f x≠0) :
    (revFDerivProj R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revFDerivProj R Unit f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr =>
       (ynorm⁻¹ * dr) • ydf.2 () ydf.1):= by
  simp[revFDerivProj]
  sorry_proof
  -- fun_trans (disch:=assumption) only; simp[oneHot, structMake]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivProjUpdate_rule_at
    (f : X → Y) (x : X) (hf : DifferentiableAt R f x) (hx : f x≠0) :
    (revFDerivProjUpdate R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revFDerivProjUpdate R Unit f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr dx =>
       ydf.2 () ((ynorm⁻¹ * dr)•ydf.1) dx):=
by
  have ⟨_,_⟩ := hf
  simp[revFDerivProjUpdate]
  fun_trans (disch:=assumption) only
  simp[revFDerivProj,revFDerivProjUpdate,smul_pull]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivProj_rule
    (f : X → Y) (hf : Differentiable R f) (hx : ∀ x, f x≠0) :
    (revFDerivProj R Unit (fun x => ‖f x‖₂[R]))
    =
    fun x =>
      let ydf := revFDerivProj R Unit f x
      let ynorm := ‖ydf.1‖₂[R]
      (ynorm,
       fun _ dr =>
         (ynorm⁻¹ * dr) • ydf.2 () ydf.1) := by
  unfold revFDerivProj
  funext x; simp
  sorry_proof
  -- fun_trans (disch:=assumption) only
  -- simp[oneHot, structMake]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revFDerivProjUpdate_rule
    (f : X → Y) (hf : Differentiable R f) (hx : ∀ x, f x≠0) :
    (revFDerivProjUpdate R Unit (fun x => ‖f x‖₂[R]))
    =
    fun x =>
       let ydf := revFDerivProjUpdate R Unit f x
       let ynorm := ‖ydf.1‖₂[R]
       (ynorm,
        fun _ dr dx =>
          ydf.2 () ((ynorm⁻¹ * dr)•ydf.1) dx) := by
  unfold revFDerivProjUpdate
  funext x; simp
  fun_trans (disch:=assumption) only
  simp[revFDerivProj,revFDerivProjUpdate,smul_pull]

end InnerProductSpace




variable
  {X₁ : Type} [NormedAddCommGroup X₁] [AdjointSpace K X₁] [CompleteSpace X₁]
  {X₂ : Type} [NormedAddCommGroup X₂] [AdjointSpace K X₂] [CompleteSpace X₂]

theorem revFDerivProj_decomposition (f : X → Y')
  (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) (hdec : Meta.IsDecomposition p₁ p₂ q)
  (hp₁ : IsContinuousLinearMap K p₁)
  (f' : X₁ → Y') (hf : f = f' ∘ p₁) :
  revFDerivProj K Yi f
  =
  fun x =>
    let ydf := revFDerivProj K Yi f' (p₁ x)
    (ydf.1, fun j dy => q (ydf.2 j dy) 0) := sorry


theorem revFDerivUpdate_decomposition (f : X → Y')
  (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X) (hdec : Meta.IsDecomposition p₁ p₂ q)
  (hp₁ : IsContinuousLinearMap K p₁)
  (f' : X₁ → Y') (hf : f = f' ∘ p₁) :
  revFDerivProjUpdate K Yi f
  =
  fun x =>
    let ydf := revFDerivProjUpdate K Yi f' (p₁ x)
    (ydf.1, fun j dy dx =>
       let dx₁ := p₁ dx
       let dx₂ := p₂ dx
       q (ydf.2 j dy dx₁) dx₂) := sorry
