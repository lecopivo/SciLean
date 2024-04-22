import SciLean.Core.FunctionPropositions.HasAdjDiff
import SciLean.Core.FunctionTransformations.SemiAdjoint
import SciLean.Core.FunctionTransformations.RevDeriv

import SciLean.Data.StructType.Algebra

set_option linter.unusedVariables false

open LeanColls
namespace SciLean

variable
  (K I : Type) [RCLike K]
  {W : Type} [SemiInnerProductSpace K W]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {ι : Type} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  -- {κ : Type} [EnumType κ]
  {E : Type} {EI : I → Type}
  [StructType E I EI] [IndexType.{0,0} I] [LawfulIndexType I] [DecidableEq I]
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
def revDeriv2
  (f : W → X → Y) (w : W) (x : X) : Y×(Y→W→(W×X)) :=
  (f w x,
   fun dy =>
     let (dw,dx) := semiAdjoint K (cderiv K (fun (w,x) => f w x) (w,x)) dy
     fun dw' => (dw'+dw,dx))

noncomputable
def revDeriv2Proj
  (f : W → X→ Y) (w : W) (x : X) (i : I) : YI i×(YI i→W→(W×X)) :=
  let ydf := revDeriv2 K f w x
  (structProj ydf.1 i,
   fun dyi => ydf.2 (oneHot i dyi))

structure HasRevDeriv2At (f : W → X → Y) (f' : Y×(Y→W→(W×X))) (w : W) (x : X) : Prop where
  hasAdjDiff : HasAdjDiffAt K (fun (w,x) => f w x) (w,x)
  revDeriv2  : revDeriv2 K f w x = f'

structure HasRevDeriv2At' (f : W → X → Y) (y : Y) (f' : (Y→W→(W×X))) (w : W) (x : X) : Prop where
  hasAdjDiff : HasAdjDiffAt K (fun (w,x) => f w x) (w,x)
  val : y = f w x
  deriv : f' = fun dy =>
    let (dw,dx) := semiAdjoint K (cderiv K (fun (w,x) => f w x) (w,x)) dy
    fun dw' => (dw'+dw, dx)

structure HasRevDerivProj2At (f : W → X → Y)  (f' : (i : I) → YI i×(YI i→W→(W×X))) (w : W) (x : X)  : Prop where
  hasAdjDiff : HasAdjDiffAt K (fun (w,x) => f w x) (w,x)
  revDeriv2  : ∀ i, revDeriv2Proj K I f w x i = f' i


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDeriv2 ------------------------------------------
--------------------------------------------------------------------------------

namespace revDeriv2

theorem id1_rule
  : revDeriv2 K (fun (w : W) (x : X) => w)
    =
    fun w x =>
      (w, fun dw dw' => (dw' + dw, 0)) :=
by
  unfold revDeriv2
  funext x y; fun_trans

theorem id1_rule_has :
  HasRevDeriv2At K
    (fun (w : W) (x : X) => w)
    (w, fun dy dw => (dw+dy, 0))
    w x := by
  constructor
  . fun_prop
  . fun_trans [revDeriv2]

theorem id2_rule
  : revDeriv2 K (fun (w : W) (x : X) => x)
    =
    fun w x =>
      (x, fun dx dw' => (dw', dx)) :=
by
  unfold revDeriv2
  funext x y; fun_trans

theorem id2_rule_has :
  HasRevDeriv2At K
    (fun (w : W) (x : X) => x)
    (x, fun dy dw => (dw, dy))
    w x := by
  constructor
  . fun_prop
  . fun_trans [revDeriv2]

theorem const_rule (y : Y)
  : revDeriv2 K (fun (_ : W) (_ : X) => y)
    =
    fun w x => (y, fun _ dw' => (dw',0)) :=
by
  unfold revDeriv2
  funext x y; simp; fun_trans

theorem const_rule_has (y : Y) :
  HasRevDeriv2At K
    (fun (w : W) (x : X) => y)
    (y, fun dy dw => (dw, 0))
    w x := by
  constructor
  . fun_prop
  . fun_trans [revDeriv2]

theorem let_rule
  (f : W → X → Y → Z) (g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x,y) => f w x y)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv2 K (fun (w : W) (x : X) => let y := g w x; f w x y)
    =
    fun w x =>
      let ydg := revDeriv2 K (fun (wx : W×X) (_ : Unit) => g wx.1 wx.2) (w,x) ()
      let zdf := revDeriv2 K (fun w (xy : X×Y) => f w xy.1 xy.2) w (x,ydg.1)
      (zdf.1,
       fun dz dx =>
         let dxyz := zdf.2 dz dx
         let dxy := ydg.2 dxyz.2.2 (dxyz.1,dxyz.2.1)
         dxy.1) :=
by
  simp at hf hg
  unfold revDeriv2
  funext x y; simp (config:={zeta:=false});
  conv => lhs; fun_trans
  simp; funext dy dw'
  sorry_proof



theorem let_rule_has (w : W) (x : X)
    (g : W → X → Y) (g' : Y×(Y → (W×X) → ((W×X)×Unit)))
    (hg : HasRevDeriv2At K (fun (w,x) (_:Unit) => g w x) g' (w,x) ())
    (f : W → X → Y → Z) (f' : Z×(Z → W → (W×(X×Y))))
    (hf : HasRevDeriv2At K (fun w (x,y) => f w x y) f' w (x, g w x))
    (r : Z×(Z→W→(W×X)))
    (hr : r = (f'.1,
               fun dz dw =>
                 let dwxy := f'.2 dz dw
                 let dxy := g'.2 dwxy.2.2 (dwxy.1, dwxy.2.1)
                 dxy.1)) :
    HasRevDeriv2At K
      (fun w x => f w x (g w x))
      r
      w x := by
  rw[hr]
  have : HasAdjDiffAt K (fun (w,x) => g w x) (w,x) := sorry_proof
  have : HasAdjDiffAt K (fun (w,x,y) => f w x y) (w,x,g w x) := sorry_proof
  constructor
  . fun_prop
  . sorry_proof
    -- unfold revDeriv2
    -- fun_trans
    -- =
    -- fun w x =>
    --   let ydg := revDeriv2 K (fun (wx : W×X) (_ : Unit) => g wx.1 wx.2) (w,x) ()
    --   let zdf := revDeriv2 K (fun w (xy : X×Y) => f w xy.1 xy.2) w (x,ydg.1)
    --   (zdf.1,
    --    fun dz dx =>
    --      let dxyz := zdf.2 dz dx
    --      let dxy := ydg.2 dxyz.2.2 (dxyz.1,dxyz.2.1)
    --      dxy.1) := sorry


example : SemiInnerProductSpace K ((i : I) → EI i) := by apply instSemiInnerProductSpaceForAll
theorem pi_rule
  (f :  X → Y → (i : I) → EI i) (hf : ∀ i, HasAdjDiff K (fun xy : X×Y => f xy.1 xy.2 i))
  : (revDeriv2 K fun (x : X) (y : Y) (i : I) => f x y i)
    =
    fun x y =>
      let xdf := revDeriv2Proj K I (fun (x,y) (_:Unit) => f x y) (x,y) ()
      (fun i => (xdf i).1,
       fun df dx' =>
         fold (IndexType.univ I) (fun dxy (i : I) => ((xdf i).2 (df i) dxy).1) (dx',0)) :=
by
  unfold revDeriv2Proj revDeriv2
  funext x y; simp; funext dw dx;
  conv =>
    lhs
    rw[cderiv.pi_rule (hf:=by fun_prop)]
    fun_trans

  sorry_proof -- needs some relation between sum and repeatIdx

end revDeriv2


--------------------------------------------------------------------------------
-- Lambda calculus rules for revDeriv2Proj --------------------------------------
--------------------------------------------------------------------------------

namespace revDeriv2Proj

theorem id1_rule
  : revDeriv2Proj K I (fun (w : W) (x : X) => w)
    =
    fun w x i =>
      (structProj w i, fun dwi dw' => (structModify i (fun wi => wi + dwi) dw', 0)) :=
by
  unfold revDeriv2Proj
  simp[revDeriv2.id1_rule K]

theorem id2_rule
  : revDeriv2Proj K I (fun (w : W) (x : X) => x)
    =
    fun w x i =>
      (structProj x i, fun dxi dw' => (dw',oneHot i dxi)) :=
by
  unfold revDeriv2Proj
  simp (config:={zeta:=false}) [revDeriv2.id2_rule K]

theorem const_rule (y : Y)
  : revDeriv2Proj K I (fun (_ : W) (_ : X) => y)
    =
    fun w x i => (structProj y i, fun _ dw' => (dw',0)) :=
by
  unfold revDeriv2Proj revDeriv2
  fun_trans[semiAdjoint.const_rule]


theorem let_rule
  (f : W → X → Y → Z) (g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x,y) => f w x y)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv2Proj K I (fun (w : W) (x : X) => let y := g w x; f w x y)
    =
    fun w x i =>
      let ydg := revDeriv2 K (fun (wx : W×X) (_ : Unit) => g wx.1 wx.2) (w,x) ()
      let zdf := revDeriv2Proj K I (fun w (xy : X×Y) => f w xy.1 xy.2) w (x,ydg.1) i
      (zdf.1,
       fun dz dw =>
         let dwxy := zdf.2 dz dw
         let dxy := ydg.2 dwxy.2.2 (dwxy.1,dwxy.2.1)
         dxy.1) :=
by
  unfold revDeriv2Proj revDeriv2
  conv =>
    lhs; fun_trans
  funext w x i; simp[structProj]; funext dz dw
  simp[add_assoc,oneHot]
  ext
  . simp; sorry_proof
  . simp; sorry_proof

-- variable {I}
-- theorem pi_rule
--   (f :  X → Y → (i : I) → EI i) (hf : ∀ i, HasAdjDiff K (fun (x,y) => f x y i))
--   : (revDeriv2Proj K fun (x : X) (y : Y) (i : I) => f x y i)
--     =
--     fun x y =>
--       let xdf := revDeriv2ProjProj K I (fun (x,y) (_:Unit) => f x y) (x,y) ()
--       (fun i => (xdf i).1,
--        fun df dx' =>
--          Function.repeatIdx (fun (i : I) dxy => ((xdf i).2 (df i) dxy).1) (dx',0)) :=
-- by
--   simp at hf
--   have _ := fun i => (hf i).1
--   have _ := fun i => (hf i).2
--   unfold revDeriv2ProjProj revDeriv2Proj
--   funext x y; fun_trans; fun_trans; simp
--   funext dw dx;
--   sorry_proof -- needs some relation between sum and repeatIdx
-- variable (I)

end revDeriv2Proj


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


theorem Prod.mk.arg_fstsnd.revDeriv2_rule
  (g : W → X → Y) (f : W → X → Z)
  (hg : HasAdjDiff K (fun (w,x) => g w x)) (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDeriv2 K (fun w x => (g w x, f w x))
    =
    fun w x =>
      let ydg := revDeriv2 K g w x
      let zdf := revDeriv2 K (fun (w,x) (_:Unit) => f w x) (w,x) ()
      ((ydg.1,zdf.1),
       fun dyz dw =>
         let dwx := ydg.2 dyz.1 dw
         (zdf.2 dyz.2 dwx).1) :=
by
  simp at hf hg
  unfold revDeriv2; simp
  conv => lhs; fun_trans
  funext w x; simp
  funext (dy,dz) dw
  ext
  . simp[add_assoc]; sorry_proof
  . simp; sorry_proof



theorem Prod.mk.arg_fstsnd.revDeriv2Proj_rule {ι κ : Type} [EnumType ι] [EnumType κ]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)]
  {ZI : κ → Type} [StructType Z κ ZI] [∀ i, SemiInnerProductSpace K (ZI i)]
  (g : W → X → Y) (f : W → X → Z)
  (hg : HasAdjDiff K (fun (w,x) => g w x)) (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDeriv2Proj K (ι⊕κ) (fun w x => (g w x, f w x))
    =
    fun w x i =>
      match i with
      | .inl j =>
        let ydg := revDeriv2Proj K ι g w x j
        (ydg.1, fun dy dw => ydg.2 dy dw)
      | .inr j =>
        let zdf := revDeriv2Proj K κ f w x j
        (zdf.1, fun dz dw => zdf.2 dz dw) :=
by
  simp at hf hg
  unfold revDeriv2Proj revDeriv2
  fun_trans
  funext w x i
  cases i
  case inl =>
    simp[revDeriv2, oneHot, structMake]; funext dyi dw;
    ext <;> (simp; congr; funext i; congr; funext h; subst h; rfl)
  case inr =>
    simp[revDeriv2, oneHot, structMake]; funext dyi dw; fun_trans;
    sorry_proof


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------


theorem Prod.fst.arg_self.revDeriv2_rule
  (f : W → X → Y×Z)
  (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDeriv2 K (fun w x => (f w x).1)
    =
    fun w x =>
      let zdf := revDeriv2Proj K (Unit⊕Unit) f w x (.inl ())
      zdf :=
by
  unfold revDeriv2Proj revDeriv2
  fun_trans


theorem Prod.fst.arg_self.revDeriv2Proj_rule {ι} [EnumType ι]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)]
  (f : W → X → Y×Z)
  (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDeriv2Proj K ι (fun x y => (f x y).1)
    =
    fun w x i =>
      let zdf := revDeriv2Proj K (ι⊕Unit) f w x (.inl i)
      zdf :=
by
  unfold revDeriv2Proj revDeriv2
  fun_trans


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------


theorem Prod.snd.arg_self.revDeriv2_rule
  (f : W → X → Y×Z)
  (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDeriv2 K (fun x y => (f x y).2)
    =
    fun w x =>
      let zdf := revDeriv2Proj K (Unit⊕Unit) f w x (.inr ())
      zdf :=
by
  unfold revDeriv2Proj revDeriv2
  fun_trans


theorem Prod.snd.arg_self.revDeriv2Proj_rule {ι} [EnumType ι]
  {ZI : ι → Type} [StructType Z ι ZI] [∀ i, SemiInnerProductSpace K (ZI i)]
  (f : W → X → Y×Z)
  (hf : HasAdjDiff K (fun (w,x) => f w x))
  : revDeriv2Proj K ι (fun w x => (f w x).2)
    =
    fun w x i =>
      let zdf := revDeriv2Proj K (Unit⊕ι) f w x (.inr i)
      zdf :=
by
  unfold revDeriv2Proj revDeriv2
  fun_trans


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------


theorem HAdd.hAdd.arg_a0a1.revDeriv2_rule
  (f g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv2 K (fun w x => f w x + g w x)
    =
    fun w x =>
      let adf := revDeriv2 K f w x
      let bdg := revDeriv2 K (fun wx (_ : Unit) => g wx.1 wx.2) (w,x) ()
      (adf.1 + bdg.1,
       fun dy dw =>
         let dwx := adf.2 dy dw
         let dwx := bdg.2 dy dwx
         dwx.1) :=
by
  simp at hf hg
  unfold revDeriv2
  fun_trans
  funext w x; simp; funext dy dw
  ext
  . simp[add_assoc,add_comm]
  . simp[add_assoc,add_comm]


theorem HAdd.hAdd.arg_a0a1.revDeriv2Proj_rule {ι} [EnumType ι]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)]
  (f g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv2Proj K ι (fun w x => f w x + g w x)
    =
    fun w x i =>
      let adf := revDeriv2Proj K ι f w x i
      let bdg := revDeriv2Proj K ι (fun xy (_ : Unit) => g xy.1 xy.2) (w,x) () i
      (adf.1 + bdg.1,
       fun dy dw =>
         let dwx := adf.2 dy dw
         let dwx := bdg.2 dy dwx
         dwx.1) :=
by
  simp at hf hg
  unfold revDeriv2Proj revDeriv2
  fun_trans
  funext w x i; simp[add_assoc]
  sorry_proof


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------


theorem HSub.hSub.arg_a0a1.revDeriv2_rule
  (f g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv2 K (fun w x => f w x - g w x)
    =
    fun w x =>
      let adf := revDeriv2 K f w x
      let bdg := revDeriv2 K (fun wx (_ : Unit) => g wx.1 wx.2) (w,x) ()
      (adf.1 - bdg.1,
       fun dy dw =>
         let dwx := adf.2 dy dw
         let dwx := bdg.2 (-dy) dwx
         dwx.1) :=
by
  simp at hf hg
  unfold revDeriv2
  fun_trans
  funext w x; simp; funext dy dw
  ext
  . rw[sub_eq_add_zero_sub]; simp[add_assoc,neg_pull]
  . simp[add_assoc,neg_pull]; rw[sub_eq_add_zero_sub]; simp



theorem HSub.hSub.arg_a0a1.revDeriv2Proj_rule {ι} [EnumType ι]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)]
  (f g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv2Proj K ι (fun w x => f w x - g w x)
    =
    fun w x i =>
      let adf := revDeriv2Proj K ι f w x i
      let bdg := revDeriv2Proj K ι (fun xy (_ : Unit) => g xy.1 xy.2) (w,x) () i
      (adf.1 - bdg.1,
       fun dy dw =>
         let dwx := adf.2 dy dw
         let dwx := bdg.2 (-dy) dwx
         dwx.1) :=
by
  simp at hf hg
  unfold revDeriv2Proj
  simp only [HSub.hSub.arg_a0a1.revDeriv2_rule _ _ hf hg]
  funext w x i; simp[revDeriv2,neg_pull]


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------


theorem Neg.neg.arg_a0.revDeriv2_rule
  (f : W → X → Y)
  : (revDeriv2 K fun w x => - f w x)
    =
    fun w x =>
      let ydf := revDeriv2 K f w x
      (-ydf.1,
       fun dy dw =>
         let dwx := ydf.2 (-dy) dw
         dwx) :=
by
  unfold revDeriv2; simp; fun_trans; simp[neg_pull]


theorem Neg.neg.arg_a0.revDeriv2Proj_rule {ι} [EnumType ι]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)]
  (f : W → X → Y)
  : (revDeriv2Proj K ι fun w x => - f w x)
    =
    fun w x i =>
      let ydf := revDeriv2Proj K ι f w x i
      (-ydf.1,
       fun dy dw =>
         let dwx := ydf.2 (-dy) dw
         dwx) :=
by
  unfold revDeriv2Proj revDeriv2; simp; fun_trans; simp[neg_pull]



-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate


theorem HMul.hMul.arg_a0a1.revDeriv2_rule
  (f g : W → X → K)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv2 K (fun w x => f w x * g w x)
    =
    fun w x =>
      let adf := revDeriv2 K f w x
      let bdg := revDeriv2 K (fun wx (_ : Unit) => g wx.1 wx.2) (w,x) ()
      (adf.1 * bdg.1,
       fun dz dw =>
         let dwx := adf.2 (conj bdg.1 * dz) dw
         let dwx := bdg.2 (conj adf.1 * dz) dwx
         dwx.1) :=
by
  simp at hf hg
  unfold revDeriv2
  fun_trans
  funext w w; simp; funext dx dw
  simp[mul_assoc,mul_comm,smul_push,add_assoc]
  ext
  . simp[smul_push]; sorry_proof
  . simp[smul_push]; sorry_proof


theorem HMul.hMul.arg_a0a1.revDeriv2Proj_rule
  (f g : W → X → K)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : revDeriv2Proj K Unit (fun w x => f w x * g w x)
    =
    fun w x _ =>
      let adf := revDeriv2 K f w x
      let bdg := revDeriv2 K (fun wx (_ : Unit) => g wx.1 wx.2) (w,x) ()
      (adf.1 * bdg.1,
       fun dz dw =>
         let dwx := adf.2 (conj bdg.1 * dz) dw
         let dwx := bdg.2 (conj adf.1 * dz) dwx
         dwx.1) :=
by
  unfold revDeriv2Proj
  simp only [HMul.hMul.arg_a0a1.revDeriv2_rule _ _ hf hg]
  funext w x i; simp[revDeriv2, oneHot]



-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

#exit

theorem HSMul.hSMul.arg_a0a1.revDeriv2_rule
  {Y : Type} [SemiHilbert K Y]
  (f : W → X → K) (g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : (revDeriv2 K fun w x => f w x • g w x)
    =
    fun w x =>
      let ydf := revDeriv2 K f w x
      let zdg := revDeriv2 K (fun wx (_:Unit) => g wx.1 wx.2) (w,x) ()
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
  unfold revDeriv2; simp; fun_trans; fun_trans
  funext w x; simp
  funext dy dw'
  ext
  . simp[smul_pull,add_comm,add_assoc]; sorry_proof
  . simp[smul_pull,add_comm]; sorry_proof



theorem HSMul.hSMul.arg_a0a1.revDeriv2Proj_rule {ι} [EnumType ι]
  {Y : Type} [SemiHilbert K Y]
  {YI : ι → Type} [StructType Y ι YI] [∀ i, SemiInnerProductSpace K (YI i)] [SemiInnerProductSpaceStruct K Y ι YI]
  (f : W → X → K) (g : W → X → Y)
  (hf : HasAdjDiff K (fun (w,x) => f w x)) (hg : HasAdjDiff K (fun (w,x) => g w x))
  : (revDeriv2Proj K ι fun w x => f w x • g w x)
    =
    fun w x i =>
      let ydf := revDeriv2 K f w x
      let zdg := revDeriv2Proj K ι (fun wx (_:Unit) => g wx.1 wx.2) (w,x) () i
      (ydf.1 • zdg.1,
       fun dy dw =>
         let dk := inner zdg.1 dy
         let dwx := ydf.2 dk dw
         let dy := (conj ydf.1) • dy
         let dwx := zdg.2 dy dwx
         dwx.1) :=
by
  simp at hf hg
  unfold revDeriv2Proj
  simp only [HSMul.hSMul.arg_a0a1.revDeriv2_rule _ _ hf hg]
  funext w x i; simp
  funext dyi dw; simp[structMake,revDeriv2,structProj,add_assoc]
  sorry_proof


#exit

-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revDeriv2_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : fpropParam (∀ x, g x ≠ 0))
  : (revDeriv2 K fun x => f x / g x)
    =
    fun x =>
      let ydf := revDeriv2 K f x
      let zdg := revDeriv2Update K g x
      (ydf.1 / zdg.1,
       fun dx' => (1 / (conj zdg.1)^2) • (zdg.2 (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 dx'))) :=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDeriv2; simp; fun_trans; fun_trans
  simp[revDeriv2Update,smul_push,neg_pull,revDeriv2,smul_add,smul_sub, ← sub_eq_add_neg]

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revDeriv2Update_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : fpropParam (∀ x, g x ≠ 0))
  : (revDeriv2Update K fun x => f x / g x)
    =
    fun x =>
      let ydf := revDeriv2Update K f x
      let zdg := revDeriv2Update K g x
      (ydf.1 / zdg.1,
       fun dx' dx =>
         let c := (1 / (conj zdg.1)^2)
         let a := -(c * conj ydf.1)
         let b := c * conj zdg.1
         ((zdg.2 (a • dx') (ydf.2 (b • dx') dx)))) :=
by
  funext
  simp[revDeriv2Update]; fun_trans
  simp[revDeriv2Update,smul_push,neg_pull,revDeriv2,smul_add,smul_sub,add_assoc,mul_assoc]

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revDeriv2Proj_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : fpropParam (∀ x, g x ≠ 0))
  : (revDeriv2Proj K Unit fun x => f x / g x)
    =
    fun x =>
      let ydf := revDeriv2 K f x
      let zdg := revDeriv2Update K g x
      (ydf.1 / zdg.1,
       fun _ dx' => (1 / (conj zdg.1)^2) • (zdg.2 (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 dx'))) :=
by
  unfold revDeriv2Proj
  fun_trans; simp[oneHot, structMake]

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.revDeriv2ProjUpdate_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : fpropParam (∀ x, g x ≠ 0))
  : (revDeriv2ProjUpdate K Unit fun x => f x / g x)
    =
    fun x =>
      let ydf := revDeriv2Update K f x
      let zdg := revDeriv2Update K g x
      (ydf.1 / zdg.1,
       fun _ dx' dx =>
         let c := (1 / (conj zdg.1)^2)
         let a := -(c * conj ydf.1)
         let b := c * conj zdg.1
         ((zdg.2 (a • dx') (ydf.2 (b • dx') dx)))) :=
by
  unfold revDeriv2ProjUpdate
  fun_trans; simp[revDeriv2Update,revDeriv2,add_assoc,neg_pull,mul_assoc,smul_push]


-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
def HPow.hPow.arg_a0.revDeriv2_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f)
  : revDeriv2 K (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revDeriv2 K f x
      let y' := (n : K) * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n,
       fun dx' => ydf.2 (y' * dx')) :=
by
  have ⟨_,_⟩ := hf
  funext x
  unfold revDeriv2; simp; funext dx; fun_trans; fun_trans; simp[smul_push,smul_smul]; ring_nf

@[fun_trans]
def HPow.hPow.arg_a0.revDeriv2Update_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f)
  : revDeriv2Update K (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revDeriv2Update K f x
      let y' := n * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n,
       fun dy dx => ydf.2 (y' * dy) dx) :=
by
  unfold revDeriv2Update
  funext x; fun_trans; simp[mul_assoc,mul_comm,add_assoc]

@[fun_trans]
def HPow.hPow.arg_a0.revDeriv2Proj_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f)
  : revDeriv2Proj K Unit (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revDeriv2 K f x
      let y' := (n : K) * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n, fun _ dx' => ydf.2 (y' * dx')) :=
by
  unfold revDeriv2Proj; fun_trans; simp[oneHot,structMake]

@[fun_trans]
def HPow.hPow.arg_a0.revDeriv2ProjUpdate_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f)
  : revDeriv2ProjUpdate K Unit (fun x => f x ^ n)
    =
    fun x =>
      let ydf := revDeriv2Update K f x
      let y' := n * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n,
       fun _ dy dx => ydf.2 (y' * dy) dx) :=
by
  unfold revDeriv2ProjUpdate; fun_trans; simp[oneHot,structMake,revDeriv2Update]


-- EnumType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.EnumType.sum.arg_f.revDeriv2_rule {ι : Type} [EnumType ι]
  (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDeriv2 K (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := fun i => revDeriv2Update K (f · i) x
      (∑ i, (ydf i).1,
       fun dy => Function.repeatIdx (fun i dx => (ydf i).2 dy dx) 0) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  funext
  sorry_proof


@[fun_trans]
theorem SciLean.EnumType.sum.arg_f.revDeriv2Update_rule {ι : Type} [EnumType ι]
  (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDeriv2Update K (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := fun i => revDeriv2Update K (f · i) x
      (∑ i, (ydf i).1,
       fun dy dx => Function.repeatIdx (fun i dx => (ydf i).2 dy dx) dx) :=
by
  simp[revDeriv2Update]
  fun_trans
  sorry_proof


@[fun_trans]
theorem SciLean.EnumType.sum.arg_f.revDeriv2Proj_rule {ι : Type} [EnumType ι]
  (f : X → ι → Y') (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDeriv2Proj K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := fun i => revDeriv2ProjUpdate K Yi (f · i) x
      (∑ i, (ydf i).1,
       fun j dy => Function.repeatIdx (fun (i : ι) dx => (ydf i).2 j dy dx) 0) :=
by
  funext; simp[revDeriv2Proj]; fun_trans; sorry_proof


@[fun_trans]
theorem SciLean.EnumType.sum.arg_f.revDeriv2ProjUpdate_rule {ι : Type} [EnumType ι]
  (f : X → ι → Y') (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDeriv2ProjUpdate K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := fun i => revDeriv2ProjUpdate K Yi (f · i) x
      (∑ i, (ydf i).1,
       fun j dy dx => Function.repeatIdx (fun (i : ι) dx => (ydf i).2 j dy dx) dx) :=
by
  funext; simp[revDeriv2ProjUpdate]; fun_trans; sorry_proof


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem ite.arg_te.revDeriv2_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y)
  : revDeriv2 K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDeriv2 K t y) (revDeriv2 K e y) :=
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem ite.arg_te.revDeriv2Update_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y)
  : revDeriv2Update K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDeriv2Update K t y) (revDeriv2Update K e y) :=
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem ite.arg_te.revDeriv2Proj_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y')
  : revDeriv2Proj K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDeriv2Proj K Yi t y) (revDeriv2Proj K Yi e y) :=
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem ite.arg_te.revDeriv2ProjUpdate_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y')
  : revDeriv2ProjUpdate K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDeriv2ProjUpdate K Yi t y) (revDeriv2ProjUpdate K Yi e y) :=
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]


@[fun_trans]
theorem dite.arg_te.revDeriv2_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (e : ¬c → X → Y)
  : revDeriv2 K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDeriv2 K (t p) y)
             (fun p => revDeriv2 K (e p) y) :=
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem dite.arg_te.revDeriv2Update_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (e : ¬c → X → Y)
  : revDeriv2Update K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDeriv2Update K (t p) y)
             (fun p => revDeriv2Update K (e p) y) :=
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem dite.arg_te.revDeriv2Proj_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y') (e : ¬c → X → Y')
  : revDeriv2Proj K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDeriv2Proj K Yi (t p) y)
             (fun p => revDeriv2Proj K Yi (e p) y) :=
by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem dite.arg_te.revDeriv2ProjUpdate_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y') (e : ¬c → X → Y')
  : revDeriv2ProjUpdate K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => revDeriv2ProjUpdate K Yi (t p) y)
             (fun p => revDeriv2ProjUpdate K Yi (e p) y) :=
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
theorem Inner.inner.arg_a0a1.revDeriv2_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDeriv2 R fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revDeriv2 R f x
      let y₂dg := revDeriv2Update R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1))):=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  funext; simp[revDeriv2,revDeriv2Update]
  fun_trans only; simp
  fun_trans; simp[smul_pull]

@[fun_trans]
theorem Inner.inner.arg_a0a1.revDeriv2Update_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDeriv2Update R fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revDeriv2Update R f x
      let y₂dg := revDeriv2Update R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr dx =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1) dx) ) :=

by
  unfold revDeriv2Update
  fun_trans; simp[revDeriv2Update,add_assoc]

@[fun_trans]
theorem Inner.inner.arg_a0a1.revDeriv2Proj_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDeriv2Proj R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revDeriv2 R f x
      let y₂dg := revDeriv2Update R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1))) :=
by
  funext
  simp[revDeriv2Proj]
  fun_trans; simp[oneHot, structMake]

@[fun_trans]
theorem Inner.inner.arg_a0a1.revDeriv2ProjUpdate_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDeriv2ProjUpdate R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := revDeriv2Update R f x
      let y₂dg := revDeriv2Update R g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr dx =>
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (dr • y₂dg.1) dx)) :=
by
  funext
  simp[revDeriv2ProjUpdate]
  fun_trans; simp[revDeriv2Update,add_assoc]



-- norm2 -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revDeriv2_rule
  (f : X → Y) (hf : HasAdjDiff R f)
  : (revDeriv2 R fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revDeriv2 R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun dr =>
         ((2:R) * dr) • ydf.2 ydf.1):=
by
  have ⟨_,_⟩ := hf
  funext x; simp[revDeriv2]
  fun_trans only
  simp
  fun_trans
  simp[smul_smul]

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revDeriv2Update_rule
  (f : X → Y) (hf : HasAdjDiff R f)
  : (revDeriv2Update R fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revDeriv2Update R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun dr dx =>
          ydf.2 (((2:R)*dr)•ydf.1) dx) :=
by
  have ⟨_,_⟩ := hf
  funext x; simp[revDeriv2Update]
  fun_trans only; simp[revDeriv2,smul_pull]


@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revDeriv2Proj_rule
  (f : X → Y) (hf : HasAdjDiff R f)
  : (revDeriv2Proj R Unit fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revDeriv2 R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr =>
         ((2:R) * dr) • ydf.2 ydf.1):=
by
  have ⟨_,_⟩ := hf
  funext x; simp[revDeriv2Proj]
  fun_trans; simp[oneHot,structMake]

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.revDeriv2ProjUpdate_rule
  (f : X → Y) (hf : HasAdjDiff R f)
  : (revDeriv2ProjUpdate R Unit fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := revDeriv2Update R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr dx =>
          ydf.2 (((2:R)*dr)•ydf.1) dx) :=
by
  have ⟨_,_⟩ := hf
  funext x; simp[revDeriv2ProjUpdate]
  fun_trans only; simp[revDeriv2,revDeriv2Update,smul_pull]


-- norm₂ -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDeriv2_rule_at
  (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDeriv2 R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDeriv2 R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun dr =>
       (ynorm⁻¹ * dr) • ydf.2 ydf.1):=
by
  have ⟨_,_⟩ := hf
  simp[revDeriv2]
  fun_trans only
  simp
  fun_trans
  funext dr; simp[smul_smul]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDeriv2Update_rule_at
  (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDeriv2Update R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDeriv2Update R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun dr dx =>
       ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
by
  have ⟨_,_⟩ := hf
  simp[revDeriv2Update]
  fun_trans only
  simp
  fun_trans
  funext dr; simp[revDeriv2,smul_pull]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDeriv2Proj_rule_at
  (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDeriv2Proj R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDeriv2 R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr =>
       (ynorm⁻¹ * dr) • ydf.2 ydf.1):=
by
  have ⟨_,_⟩ := hf
  simp[revDeriv2Proj]
  fun_trans only; simp[oneHot, structMake]

@[fun_trans]
theorem SciLean.norm₂.arg_x.revDeriv2ProjUpdate_rule_at
  (f : X → Y) (x : X) (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDeriv2ProjUpdate R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDeriv2Update R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr dx =>
       ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
by
  have ⟨_,_⟩ := hf
  simp[revDeriv2ProjUpdate]
  fun_trans only; simp[revDeriv2,revDeriv2Update,smul_pull]

end InnerProductSpace
