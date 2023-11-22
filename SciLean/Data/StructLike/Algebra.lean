import SciLean.Core.Objects.SemiInnerProductSpace
import SciLean.Core.Objects.FinVec
import SciLean.Data.StructLike.Basic

set_option linter.unusedVariables false

namespace SciLean

variable
  (K : Type _) [IsROrC K]
  {ι κ : Type _} [EnumType ι] [EnumType κ]
  {E I : Type _} {EI : I → Type _}
  [StructLike E I EI]
  {F J : Type _} {FJ : J → Type _}
  [StructLike F J FJ]


open StructLike in
class VecStruct (K X I XI) [StructLike X I XI] [IsROrC K] [Vec K X] [∀ i, Vec K (XI i)] : Prop where
  proj_add : ∀ i (x x' : X), proj (x + x') i = proj x i + proj x' i
  proj_smul : ∀ i (k : K) (x : X), proj (k • x) i = k • proj x i
  proj_zero : ∀ i, proj (0 : X) i = 0
  proj_continuous : Continuous (fun (x : X) i =>  proj x i)
  make_continuous : Continuous (fun f => make (X:=X) f)

attribute [simp] VecStruct.proj_add VecStruct.proj_smul VecStruct.proj_zero

open StructLike in
class SemiInnerProductSpaceStruct (K X I XI) [StructLike X I XI] [IsROrC K] [EnumType I] [SemiInnerProductSpace K X] [∀ i, SemiInnerProductSpace K (XI i)] extends VecStruct K X I XI : Prop where
  inner_proj : ∀ (x x' : X), ⟪x,x'⟫[K] = ∑ (i : I), ⟪proj x i, proj x' i⟫[K]
  testFun_proj : ∀ (x : X), TestFunction x ↔ (∀ i, TestFunction (proj x i))

instance (priority:=low) {X} [Vec K X] : VecStruct K X Unit (fun _ => X) where
  proj_add := by simp[StructLike.proj]
  proj_smul := by simp[StructLike.proj]
  proj_zero := by simp[StructLike.proj]
  proj_continuous := sorry_proof
  make_continuous := sorry_proof

instance (priority:=low) {X} [SemiInnerProductSpace K X] : SemiInnerProductSpaceStruct K X Unit (fun _ => X) where
  inner_proj := sorry_proof
  testFun_proj := sorry_proof


@[reducible]
instance [∀ i, Vec K (EI i)] [∀ j, Vec K (FJ j)] (i : I ⊕ J) : Vec K (Prod.TypeFun EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

instance [Vec K E] [Vec K F] [∀ i, Vec K (EI i)] [∀ j, Vec K (FJ j)] 
  [VecStruct K E I EI] [VecStruct K F J FJ]
  : VecStruct K (E×F) (I⊕J) (Prod.TypeFun EI FJ) where
  proj_add := by simp[StructLike.proj]
  proj_smul := by simp[StructLike.proj]
  proj_zero := by simp[StructLike.proj]
  proj_continuous := sorry_proof
  make_continuous := sorry_proof


instance [∀ i, SemiInnerProductSpace K (EI i)] [∀ j, SemiInnerProductSpace K (FJ j)] (i : I ⊕ J) 
  : SemiInnerProductSpace K (Prod.TypeFun EI FJ i) :=
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance


instance 
  [SemiInnerProductSpace K E] [SemiInnerProductSpace K F] 
  [∀ i, SemiInnerProductSpace K (EI i)] [∀ j, SemiInnerProductSpace K (FJ j)] 
  [EnumType I] [EnumType J]
  [SemiInnerProductSpaceStruct K E I EI] [SemiInnerProductSpaceStruct K F J FJ]
  : SemiInnerProductSpaceStruct K (E×F) (I⊕J) (Prod.TypeFun EI FJ) := sorry_proof
  -- inner_proj := sorry_proof
  -- testFun_proj := sorry_proof


instance [∀ i, FinVec ι K (EI i)] [∀ j, FinVec ι K (FJ j)] (i : I ⊕ J) 
  : FinVec ι K (Prod.TypeFun EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance


open StructLike


variable 
  {X XI} [StructLike X I XI] [Vec K X] [∀ i, Vec K (XI i)] [VecStruct K X I XI]

@[simp]
theorem make_zero
  : make (X:=X) (fun _ => 0)
    =
    0 :=
by
  apply StructLike.ext
  simp[VecStruct.proj_zero]
  

@[simp]
theorem make_add (f g : (i : I) →  XI i)
  : make (X:=X) f + make g 
    =
    make (fun i => f i + g i) :=
by
  apply StructLike.ext
  simp[VecStruct.proj_add]


@[simp]
theorem make_smul (k : K) (f : (i : I) →  XI i)
  : k • make (X:=X) f 
    =
    make (fun i => k • f i) :=
by
  apply StructLike.ext
  simp[VecStruct.proj_smul]


@[simp]
theorem make_nsmul (k : ℕ) (f : (i : I) →  XI i)
  : k • make (X:=X) f 
    =
    make (fun i => k • f i) :=
by
  apply StructLike.ext
  sorry_proof


@[simp]
theorem make_zsmul (k : ℤ) (f : (i : I) →  XI i)
  : k • make (X:=X) f 
    =
    make (fun i => k • f i) :=
by
  apply StructLike.ext
  sorry_proof


@[simp]
theorem make_neg (f : (i : I) →  XI i)
  : - make (X:=X) f
    =
    make (fun i => - f i) :=
by
  apply StructLike.ext; intro i
  conv => lhs; enter[1]; equals (-1) • make (X:=X) f => simp
  simp only [make_zsmul]
  simp


@[simp]
theorem make_sub (f g : (i : I) →  XI i)
  : make (X:=X) f - make g 
    =
    make (fun i => f i - g i) :=
by
  apply StructLike.ext; intro i
  conv => lhs; enter[1]; equals make (X:=X) f + (-1) • make g => simp[sub_eq_add_neg]
  simp [sub_eq_add_neg]


