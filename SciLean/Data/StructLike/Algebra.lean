import SciLean.Core.Objects.SemiInnerProductSpace
import SciLean.Core.Objects.FinVec
import SciLean.Data.StructLike.Basic

set_option linter.unusedVariables false

namespace SciLean

variable
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι κ : Type _} [EnumType ι] [EnumType κ]
  {E I : Type _} {EI : I → Type _}
  [StructLike E I EI]
  {F J : Type _} {FJ : J → Type _}
  [StructLike F J FJ]


instance [∀ i, Vec K (EI i)] [∀ j, Vec K (FJ j)] (i : I ⊕ J) : Vec K (Prod.TypeFun EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

instance [∀ i, SemiInnerProductSpace K (EI i)] [∀ j, SemiInnerProductSpace K (FJ j)] (i : I ⊕ J) 
  : SemiInnerProductSpace K (Prod.TypeFun EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

instance [∀ i, FinVec ι K (EI i)] [∀ j, FinVec ι K (FJ j)] (i : I ⊕ J) 
  : FinVec ι K (Prod.TypeFun EI FJ i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance
