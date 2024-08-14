import SciLean.Data.StructType
import SciLean.Analysis.AdjointSpace.Adjoint


namespace SciLean

set_option deprecated.oldSectionVars true

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
def adjointProj [DecidableEq I]
  (f : X → E) (i : I) (de : EI i) : X := adjoint K f (oneHot i de)

@[fun_trans]
noncomputable
def adjointProjUpdate [DecidableEq I]
  (f : X → E) (i : I) (de : EI i) (x : X) : X :=
  let f' := adjointProj K I f
  x + f' i de

--------------------------------------------------------------------------------
-- Lambda calculus rules for adjointProj ------------------------------------
--------------------------------------------------------------------------------

namespace adjointProj

@[fun_trans]
theorem id_rule :
    adjointProj K I (fun x : E => x)
    =
    fun i de => oneHot i de := by
  unfold adjointProj; fun_trans

@[fun_trans]
theorem const_rule
  : adjointProj K I (fun _ : Y => (0:E))
    =
    fun i (de : EI i) => 0 := by
  unfold adjointProj; fun_trans

@[fun_trans]
theorem apply_rule [DecidableEq I] (i : ι) :
    adjointProj K I (fun (f : ι → E) => f i)
    =
    fun j dxj => oneHot (X:=ι→E) (I:=ι×I) (i,j) dxj :=
by
  unfold adjointProj;
  fun_trans; simp[oneHot]
  funext j de i'
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
    (f : Y → E) (g : X → Y) (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g) :
    adjointProj K I (fun x => f (g x))
    =
    fun i e =>
    let y := adjointProj K I f i e
    adjointProj K Unit g () y := by
  unfold adjointProj; fun_trans

@[fun_trans]
theorem let_rule
    (f : X → Y → E) (g : X → Y)
    (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2)) (hg : IsContinuousLinearMap K g) :
    adjointProj K I (fun x => let y := g x; f x y)
    =
    fun i e =>
      let xy := adjointProj K I (fun xy : X×Y => f xy.1 xy.2) i e
      adjointProjUpdate K Unit g () xy.2 xy.1 := by
  unfold adjointProj adjointProjUpdate; fun_trans [oneHot,adjointProj]

@[fun_trans]
theorem pi_rule_unit
    (f :  X → ι → Y) (hf : ∀ i, IsContinuousLinearMap K (f · i)) :
    (adjointProj K Unit fun (x : X) (i : ι) => f x i)
    =
    fun _ y =>
      IndexType.foldl (fun (x : X) i =>
        adjointProjUpdate K Unit (f · i) () (y i) x) (0 : X) := by
  unfold adjointProj
  rw[adjoint.pi_rule (hf:=hf)]
  fun_trans [adjointProjUpdate, adjointProj]
  funext i y
  sorry_proof

@[fun_trans]
theorem pi_rule
    (f :  X → ι → E) (hf : ∀ i, IsContinuousLinearMap K (f · i)) :
    (adjointProj K (ι×I) fun (x : X) (i : ι) => f x i)
    =
    fun (i',i) y =>  adjointProj K I (f · i') i y := by
  unfold adjointProj
  rw[adjoint.pi_rule (hf:=hf)]
  fun_trans
  funext (i',i) e
  sorry_proof


end adjointProj


--------------------------------------------------------------------------------
-- Lambda calculus rules for adjointProjUpdate --------------------------------
--------------------------------------------------------------------------------

namespace adjointProjUpdate

@[fun_trans]
theorem id_rule
  : adjointProjUpdate K I (fun x : E => x)
    =
    fun i e x => structModify i (fun ei => ei + e) x :=
by
  funext x; unfold adjointProjUpdate
  simp[adjointProjUpdate, adjointProj.id_rule]
  sorry_proof


@[fun_trans]
theorem const_rule
  : adjointProjUpdate K I (fun _ : Y => (0:E))
    =
    fun i e x => x :=
by
  unfold adjointProjUpdate; simp[adjointProj.const_rule]

@[fun_trans]
theorem comp_rule
  (f : Y → E) (g : X → Y)
  (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g)
  : adjointProjUpdate K I (fun x => f (g x))
    =
    fun i e x =>
      let y := adjointProj K I f i e
      adjointProjUpdate K Unit g () y x := by
  funext x; unfold adjointProjUpdate
  simp[adjointProjUpdate,adjointProj.comp_rule _ _ _ _ hf hg]


@[fun_trans]
theorem let_rule
  (f : X → Y → E) (g : X → Y)
  (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2)) (hg : IsContinuousLinearMap K g)
  : adjointProjUpdate K I (fun x => let y := g x; f x y)
    =
    fun i e x =>
      let xy := adjointProjUpdate K I (fun xy : X×Y => f xy.1 xy.2) i e (x,0)
      adjointProjUpdate K Unit g () xy.2 xy.1 := by
  unfold adjointProjUpdate
  simp [adjointProj.let_rule _ _ _ _ hf hg,add_assoc,add_comm,adjointProjUpdate]

@[fun_trans]
theorem apply_rule [DecidableEq I] (i : ι)
  : adjointProjUpdate K I (fun (f : ι → E) => f i)
    =
    fun j dxj df i' =>
        if i=i' then
          structModify j (fun xj => xj + dxj) (df i')
        else
          df i' :=
by
  unfold adjointProjUpdate
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
    (f :  X → ι → Y) (hf : ∀ i, IsContinuousLinearMap K (f · i)) :
    (adjointProjUpdate K Unit fun (x : X) (i : ι) => f x i)
    =
    fun _ y x =>
      IndexType.foldl (fun (x : X) i =>
        adjointProjUpdate K Unit (f · i) () (y i) x) x := by
  unfold adjointProjUpdate
  funext i de dx
  rw[adjointProj.pi_rule_unit (hf:=hf)]
  simp
  sorry_proof

@[fun_trans]
theorem pi_rule
    (f :  X → ι → E) (hf : ∀ i, IsContinuousLinearMap K (f · i)) :
    (adjointProjUpdate K (ι×I) fun (x : X) (i : ι) => f x i)
    =
    fun (i',i) y x => adjointProjUpdate K I (f · i') i y x := by
  unfold adjointProjUpdate
  funext (i',i) y x
  rw[adjointProj.pi_rule K I f hf]


end adjointProjUpdate


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

end SciLean
open SciLean

set_option deprecated.oldSectionVars true

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
theorem Prod.mk.arg_fstsnd.adjointProj_rule
    (g : X → Y') (f : X → Z')
    (hg : IsContinuousLinearMap K g) (hf : IsContinuousLinearMap K f) :
    adjointProj K (Yi⊕Zi) (fun x => (g x, f x))
    =
    fun i yz =>
      match i with
      | .inl j => adjointProj K Yi g j yz
      | .inr j => adjointProj K Zi f j yz := by
  unfold adjointProj
  funext i dyz
  fun_trans
  induction i <;>
    { simp[oneHot,structMake]
      apply congr_arg
      congr; funext i; congr; funext h
      subst h; rfl
    }

@[fun_trans]
theorem Prod.mk.arg_fstsnd.adjointProjUpdate_rule
    (g : X → Y') (f : X → Z')
    (hg : IsContinuousLinearMap K g) (hf : IsContinuousLinearMap K f) :
    adjointProjUpdate K (Yi⊕Zi) (fun x => (g x, f x))
    =
    fun i yz x =>
      match i with
      | .inl j => adjointProjUpdate K Yi g j yz x
      | .inr j => adjointProjUpdate K Zi f j yz x := by
  unfold adjointProjUpdate
  funext i de dx;
  fun_trans
  induction i <;> simp


@[fun_trans]
theorem Prod.mk.arg_fstsnd.adjointProj_rule_unit
    (g : X → Y') (f : X → Z')
    (hg : IsContinuousLinearMap K g) (hf : IsContinuousLinearMap K f) :
    adjointProj K Unit (fun x => (g x, f x))
    =
    fun _ yz =>
      let x := adjointProj K Unit g () yz.1
      adjointProjUpdate K Unit f () yz.2 x := by
  unfold adjointProj
  funext x; fun_trans [adjointProjUpdate,adjointProj,oneHot]


@[fun_trans]
theorem Prod.mk.arg_fstsnd.adjointProjUpdate_rule_unit
    (g : X → Y') (f : X → Z')
    (hg : IsContinuousLinearMap K g) (hf : IsContinuousLinearMap K f) :
    adjointProjUpdate K Unit (fun x => (g x, f x))
    =
    fun _ yz x =>
      let x := adjointProjUpdate K Unit g () yz.1 x
      adjointProjUpdate K Unit f () yz.2 x := by
  unfold adjointProjUpdate
  funext x; fun_trans; simp [adjointProjUpdate,adjointProj,oneHot,add_assoc]


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.fst.arg_self.adjointProj_rule
    (f : W → X'×Y) (hf : IsContinuousLinearMap K f) :
    adjointProj K Xi (fun x => (f x).1)
    =
    fun i xy =>
      adjointProj K (Xi⊕Unit) f (.inl i) xy := by
  unfold adjointProj
  funext i xy; fun_trans[adjointProj, oneHot, structMake]
  congr
  funext i
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only


@[fun_trans]
theorem Prod.fst.arg_self.adjointProjUpdate_rule
    (f : W → X'×Y) (hf : IsContinuousLinearMap K f) :
    adjointProjUpdate K Xi (fun x => (f x).1)
    =
    fun i xy w =>
      adjointProjUpdate K (Xi⊕Unit) f (.inl i) xy w := by
  unfold adjointProjUpdate
  funext x; fun_trans


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.snd.arg_self.adjointProj_rule
    (f : W → X×Y') (hf : IsContinuousLinearMap K f) :
    adjointProj K Yi (fun x => (f x).2)
    =
    fun i xy =>
      adjointProj K (Unit⊕Yi) f (.inr i) xy := by
  unfold adjointProj
  funext i e; fun_trans[adjointProj,oneHot]
  congr
  funext i
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only


@[fun_trans]
theorem Prod.snd.arg_self.adjointProjUpdate_rule
    (f : W → X×Y') (hf : IsContinuousLinearMap K f) :
    adjointProjUpdate K Yi (fun x => (f x).2)
    =
    fun i xy w =>
      adjointProjUpdate K (Unit⊕Yi) f (.inr i) xy w := by
  unfold adjointProjUpdate
  funext x; fun_trans


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.adjointProj_rule
    (f g : X → Y') (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g) :
    (adjointProj K Yi fun x => f x + g x)
    =
    fun i y =>
      let x := adjointProj K Yi f i y
      adjointProjUpdate K Yi g i y x := by
  unfold adjointProjUpdate; unfold adjointProj
  fun_trans

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.adjointProjUpdate_rule
    (f g : X → Y') (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g) :
    (adjointProjUpdate K Yi fun x => f x + g x)
    =
    fun i y x =>
      let x := adjointProjUpdate K Yi f i y x
      adjointProjUpdate K Yi g i y x := by
  unfold adjointProjUpdate
  fun_trans; simp[adjointProjUpdate, add_assoc]


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem HSub.hSub.arg_a0a1.adjointProj_rule
    (f g : X → Y') (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g) :
    (adjointProj K Yi fun x => f x - g x)
    =
    fun i y =>
      let x := adjointProj K Yi f i y
      let y' := -y
      adjointProjUpdate K Yi g i y' x := by
  unfold adjointProjUpdate adjointProj
  fun_trans
  simp only [neg_pull, ← sub_eq_add_neg]



@[fun_trans]
theorem HSub.hSub.arg_a0a1.adjointProjUpdate_rule
    (f g : X → Y') (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g) :
    (adjointProjUpdate K Yi fun x => f x - g x)
    =
    fun i y x =>
      let x := adjointProjUpdate K Yi f i y x
      let y' := -y
      adjointProjUpdate K Yi g i y' x := by
  unfold adjointProjUpdate
  fun_trans; simp[adjointProjUpdate, adjointProj,add_assoc]


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem Neg.neg.arg_a0.adjointProj_rule
    (f : X → Y') :
    (adjointProj K Yi fun x => - f x)
    =
    fun i y =>
      let y' := -y
      adjointProj K Yi f i y' := by
  unfold adjointProj; fun_trans; simp only [neg_pull]; sorry_proof

@[fun_trans]
theorem Neg.neg.arg_a0.adjointProjUpdate_rule
    (f : X → Y') :
    (adjointProjUpdate K Yi fun x => - f x)
    =
    fun i y x =>
      let y' := -y
      adjointProjUpdate K Yi f i y' x := by
  unfold adjointProjUpdate; fun_trans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------
open ComplexConjugate

@[fun_trans]
theorem HMul.hMul.arg_a0.adjointProj_rule
    (f : X → K) (c : K) (hf : IsContinuousLinearMap K f) :
    (adjointProj K Unit fun x => f x * c)
    =
    fun _ y =>
      adjointProj K Unit f () (conj c * y) := by
  unfold adjointProj
  fun_trans; simp[oneHot, structMake,adjointProjUpdate, adjointProj, smul_push]

@[fun_trans]
theorem HMul.hMul.arg_a0.adjointProjUpdate_rule
    (f : X → K) (c : K) (hf : IsContinuousLinearMap K f) :
    (adjointProjUpdate K Unit fun x => f x * c)
    =
    fun _ y x =>
      adjointProjUpdate K Unit f () (conj c * y) x := by
  unfold adjointProjUpdate
  fun_trans


@[fun_trans]
theorem HMul.hMul.arg_a1.adjointProj_rule
    (f : X → K) (c : K) (hf : IsContinuousLinearMap K f) :
    (adjointProj K Unit fun x => c * f x)
    =
    fun _ y =>
      adjointProj K Unit f () (conj c * y) := by
  unfold adjointProj
  fun_trans; simp[oneHot, structMake,adjointProjUpdate, adjointProj, smul_push]

@[fun_trans]
theorem HMul.hMul.arg_a1.adjointProjUpdate_rule
    (f : X → K) (c : K) (hf : IsContinuousLinearMap K f) :
    (adjointProjUpdate K Unit fun x => c * f x)
    =
    fun _ y x =>
      adjointProjUpdate K Unit f () (conj c * y) x := by
  unfold adjointProjUpdate
  fun_trans


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

section SMulOnAdjointSpace

variable
  {Y Yi : Type} {YI : Yi → Type} [StructType Y Yi YI] [IndexType Yi] [DecidableEq Yi]
  [NormedAddCommGroup Y] [AdjointSpace K Y] [∀ i, NormedAddCommGroup (YI i)] [∀ i, AdjointSpace K (YI i)] [VecStruct K Y Yi YI]


@[fun_trans]
theorem HSMul.hSMul.arg_a0.adjointProj_rule
    (f : X → K) (y : Y) (hf : IsContinuousLinearMap K f) :
    (adjointProj K Yi fun x => f x • y)
    =
    fun i y' =>
      let dk := ⟪structProj y i, y'⟫[K]
      adjointProj K Unit f () dk := by
  unfold adjointProj
  fun_trans [smul_push]
  sorry_proof


@[fun_trans]
theorem HSMul.hSMul.arg_a0.adjointProjUpdate_rule
    (f : X → K) (y : Y) (hf : IsContinuousLinearMap K f) :
    (adjointProjUpdate K Yi fun x => f x • y)
    =
    fun i y' x =>
      let dk := ⟪structProj y i, y'⟫[K]
      adjointProjUpdate K Unit f () dk x := by
  unfold adjointProjUpdate
  fun_trans

@[fun_trans]
theorem HSMul.hSMul.arg_a1.adjointProj_rule
    (c : K) (g : X → Y) (hg : IsContinuousLinearMap K g) :
    (adjointProj K Yi fun x => c • g x)
    =
    fun i y =>
      let x := adjointProj K Yi g i y
      conj c • x := by
  unfold adjointProj
  fun_trans [smul_push]


@[fun_trans]
theorem HSMul.hSMul.arg_a0a1.adjointProjUpdate_rule
    (c : K) (g : X → Y) (hg : IsContinuousLinearMap K g) :
    (adjointProjUpdate K Yi fun x => c • g x)
    =
    fun i y x =>
      let x := adjointProjUpdate K Yi g i (conj c • y) x
      x := by
  unfold adjointProjUpdate
  fun_trans [smul_push,adjointProj]

end SMulOnAdjointSpace


#exit

-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.adjointProj_rule
    (f g : X → K) (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g) (hx : ∀ x, g x ≠ 0) :
    (adjointProj K Unit fun x => f x / g x)
    =
    fun x =>
      let ydf := adjointProj K Unit f x
      let zdg := adjointProjUpdate K Unit g x
      (ydf.1 / zdg.1,
       fun _ dx' => (1 / (conj zdg.1)^2) • (zdg.2 () (-conj ydf.1 • dx') (conj zdg.1 • ydf.2 () dx'))) :=
by
  unfold adjointProj
  fun_trans (disch:=apply hx); simp[oneHot, structMake,adjointProjUpdate,adjointProj,smul_push]
  sorry_proof

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.adjointProjUpdate_rule
    (f g : X → K) (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g) (hx : ∀ x, g x ≠ 0) :
    (adjointProjUpdate K Unit fun x => f x / g x)
    =
    fun x =>
      let ydf := adjointProjUpdate K Unit f x
      let zdg := adjointProjUpdate K Unit g x
      (ydf.1 / zdg.1,
       fun _ dx' dx =>
         let c := (1 / (conj zdg.1)^2)
         let a := -(c * conj ydf.1)
         let b := c * conj zdg.1
         ((zdg.2 () (a • dx') (ydf.2 () (b • dx') dx)))) :=
by
  unfold adjointProjUpdate
  fun_trans (disch:=assumption)
  simp[adjointProjUpdate,adjointProj,add_assoc,neg_pull,mul_assoc,smul_push]


-- HPow.hPow -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
def HPow.hPow.arg_a0.adjointProj_rule
    (f : X → K) (n : Nat) (hf : IsContinuousLinearMap K f) :
    adjointProj K Unit (fun x => f x ^ n)
    =
    fun x =>
      let ydf := adjointProj K Unit f x
      let y' := (n : K) * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n, fun _ dx' => ydf.2 () (y' * dx')) := by
  unfold adjointProj; fun_trans; simp[oneHot,structMake,smul_push,mul_comm,mul_assoc]

@[fun_trans]
def HPow.hPow.arg_a0.adjointProjUpdate_rule
    (f : X → K) (n : Nat) (hf : IsContinuousLinearMap K f) :
    adjointProjUpdate K Unit (fun x => f x ^ n)
    =
    fun x =>
      let ydf := adjointProjUpdate K Unit f x
      let y' := n * (conj ydf.1 ^ (n-1))
      (ydf.1 ^ n,
       fun _ dy dx => ydf.2 () (y' * dy) dx) := by
  unfold adjointProjUpdate; fun_trans


-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

section IndexTypeSum

variable {ι : Type} [IndexType ι]


@[fun_trans]
theorem IndexType.sum.arg_f.adjointProj_rule [DecidableEq ι]
    (f : X → ι → Y') (hf : ∀ i, IsContinuousLinearMap K (fun x => f x i)) :
    adjointProj K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      -- this is not optimal
      -- we should have but right now there is no appropriate StrucLike instance
      -- let ydf := adjointProj K Yi f x
      let ydf := adjointProjUpdate K (ι×Yi) f x
      (∑ i, ydf.1 i,
       fun j dy =>
         IndexType.foldl (fun dx i => ydf.2 (i,j) dy dx) 0) := by
  unfold adjointProj
  fun_trans
  sorry_proof


@[fun_trans]
theorem IndexType.sum.arg_f.adjointProjUpdate_rule [DecidableEq ι]
    (f : X → ι → Y') (hf : ∀ i, IsContinuousLinearMap K (fun x => f x i)) :
    adjointProjUpdate K Yi (fun x => ∑ i, f x i)
    =
    fun x =>
      let ydf := adjointProjUpdate K (ι×Yi) f x
      (∑ i, ydf.1 i,
       fun j dy dx =>
         IndexType.foldl (fun dx i => ydf.2 (i,j) dy dx) dx) := by
  sorry_proof


end IndexTypeSum


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem ite.arg_te.adjointProj_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y') :
    adjointProj K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (adjointProj K Yi t y) (adjointProj K Yi e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem ite.arg_te.adjointProjUpdate_rule
    (c : Prop) [dec : Decidable c] (t e : X → Y') :
    adjointProjUpdate K Yi (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (adjointProjUpdate K Yi t y) (adjointProjUpdate K Yi e y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]


@[fun_trans]
theorem dite.arg_te.adjointProj_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y') (e : ¬c → X → Y') :
    adjointProj K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => adjointProj K Yi (t p) y)
             (fun p => adjointProj K Yi (e p) y) := by
  induction dec
  case isTrue h  => ext y <;> simp[h]
  case isFalse h => ext y <;> simp[h]

@[fun_trans]
theorem dite.arg_te.adjointProjUpdate_rule
    (c : Prop) [dec : Decidable c]
    (t : c  → X → Y') (e : ¬c → X → Y') :
    adjointProjUpdate K Yi (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => adjointProjUpdate K Yi (t p) y)
             (fun p => adjointProjUpdate K Yi (e p) y) := by
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
theorem Inner.inner.arg_a0a1.adjointProj_rule
    (f : X → Y) (g : X → Y) (hf : IsContinuousLinearMap R f) (hg : IsContinuousLinearMap R g) :
    (adjointProj R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := adjointProj R Unit f x
      let y₂dg := adjointProjUpdate R Unit g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr =>
         y₂dg.2 () (dr • y₁df.1) (y₁df.2 () (dr • y₂dg.1))) := by
  funext
  simp[adjointProj]
  sorry_proof
  -- fun_trans; simp[oneHot, structMake]

@[fun_trans]
theorem Inner.inner.arg_a0a1.adjointProjUpdate_rule
    (f : X → Y) (g : X → Y) (hf : IsContinuousLinearMap R f) (hg : IsContinuousLinearMap R g) :
    (adjointProjUpdate R Unit fun x => ⟪f x, g x⟫[R])
    =
    fun x =>
      let y₁df := adjointProjUpdate R Unit f x
      let y₂dg := adjointProjUpdate R Unit g x
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun _ dr dx =>
         y₂dg.2 () (dr • y₁df.1) (y₁df.2 () (dr • y₂dg.1) dx)) := by
  funext
  simp[adjointProjUpdate]
  fun_trans; simp[adjointProjUpdate,add_assoc]


-- norm2 -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.adjointProj_rule
    (f : X → Y) (hf : IsContinuousLinearMap R f) :
    (adjointProj R Unit fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := adjointProj R Unit f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr =>
         ((2:R) * dr) • ydf.2 () ydf.1) := by
  funext x; simp[adjointProj]
  sorry_proof
  -- fun_trans; simp[oneHot,structMake]

@[fun_trans]
theorem SciLean.Norm2.norm2.arg_a0.adjointProjUpdate_rule
    (f : X → Y) (hf : IsContinuousLinearMap R f) :
    (adjointProjUpdate R Unit fun x => ‖f x‖₂²[R])
    =
    fun x =>
      let ydf := adjointProjUpdate R Unit f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun _ dr dx =>
          ydf.2 () (((2:R)*dr)•ydf.1) dx) := by
  funext x; simp[adjointProjUpdate]
  fun_trans only; simp[adjointProj,adjointProjUpdate,smul_pull]


-- norm₂ -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_trans]
theorem SciLean.norm₂.arg_x.adjointProj_rule_at
    (f : X → Y) (x : X) (hf : IsContinuousLinearMapAt R f x) (hx : f x≠0) :
    (adjointProj R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := adjointProj R Unit f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr =>
       (ynorm⁻¹ * dr) • ydf.2 () ydf.1):= by
  simp[adjointProj]
  sorry_proof
  -- fun_trans (disch:=assumption) only; simp[oneHot, structMake]

@[fun_trans]
theorem SciLean.norm₂.arg_x.adjointProjUpdate_rule_at
    (f : X → Y) (x : X) (hf : IsContinuousLinearMapAt R f x) (hx : f x≠0) :
    (adjointProjUpdate R Unit (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := adjointProjUpdate R Unit f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun _ dr dx =>
       ydf.2 () ((ynorm⁻¹ * dr)•ydf.1) dx):=
by
  have ⟨_,_⟩ := hf
  simp[adjointProjUpdate]
  fun_trans (disch:=assumption) only
  simp[adjointProj,adjointProjUpdate,smul_pull]

@[fun_trans]
theorem SciLean.norm₂.arg_x.adjointProj_rule
    (f : X → Y) (hf : IsContinuousLinearMap R f) (hx : ∀ x, f x≠0) :
    (adjointProj R Unit (fun x => ‖f x‖₂[R]))
    =
    fun x =>
      let ydf := adjointProj R Unit f x
      let ynorm := ‖ydf.1‖₂[R]
      (ynorm,
       fun _ dr =>
         (ynorm⁻¹ * dr) • ydf.2 () ydf.1) := by
  unfold adjointProj
  funext x; simp
  sorry_proof
  -- fun_trans (disch:=assumption) only
  -- simp[oneHot, structMake]

@[fun_trans]
theorem SciLean.norm₂.arg_x.adjointProjUpdate_rule
    (f : X → Y) (hf : IsContinuousLinearMap R f) (hx : ∀ x, f x≠0) :
    (adjointProjUpdate R Unit (fun x => ‖f x‖₂[R]))
    =
    fun x =>
       let ydf := adjointProjUpdate R Unit f x
       let ynorm := ‖ydf.1‖₂[R]
       (ynorm,
        fun _ dr dx =>
          ydf.2 () ((ynorm⁻¹ * dr)•ydf.1) dx) := by
  unfold adjointProjUpdate
  funext x; simp
  fun_trans (disch:=assumption) only
  simp[adjointProj,adjointProjUpdate,smul_pull]

end InnerProductSpace
