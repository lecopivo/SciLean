import SciLean.Core.FunctionTransformations.RevCDeriv
import SciLean.Core.FunctionTransformations.RevDerivUpdate
import SciLean.Data.TypeWithProj

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [EnumType ι]

  {E : Type _} [SemiInnerProductSpace K E]
  {EIdx : Type _}
  {EVal : EIdx → Type _} [∀ i, SemiInnerProductSpace K (EVal i)]
  [TypeWithProj E EIdx EVal]
  {F : Type _} [SemiInnerProductSpace K F]
  {FIdx : Type _}
  {FVal : FIdx → Type _} [∀ i, SemiInnerProductSpace K (FVal i)]
  [TypeWithProj F FIdx FVal]

instance (i : EIdx ⊕ FIdx) : Vec K (Prod.TypeFun EVal FVal i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

instance (i : EIdx ⊕ FIdx) : SemiInnerProductSpace K (Prod.TypeFun EVal FVal i) := 
  match i with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance

noncomputable
def revDerivProj
  (f : X → E) (x : X) : E×((i : EIdx)→EVal i→X) :=
  (f x, fun i de => 
    have := Classical.propDecidable
    (revCDeriv K f x).2 (TypeWithProj.intro fun i' => if h:i=i' then h▸de else 0))

noncomputable
def revDerivProjUpdate
  (f : X → E) (x : X) : E×((i : EIdx)→EVal i→K→X→X) :=
  (f x, fun i de k dx => 
    have := Classical.propDecidable
    (revDerivUpdate K f x).2 (TypeWithProj.intro fun i' => if h:i=i' then h▸de else 0) k x)


--------------------------------------------------------------------------------


theorem revDerivProj.id_rule 
  : revDerivProj K (fun x : E => x)
    =
    fun x => 
      (x,
       fun i de => 
         have := Classical.propDecidable
         TypeWithProj.intro fun i' => if h : i=i' then h▸de else 0):= 
by
  simp[revDerivProj]
  ftrans

theorem revDerivProjUpdate.id_rule 
  : revDerivProjUpdate K (fun x : E => x)
    =
    fun x => 
      (x,
       fun i de k dx => 
         TypeWithProj.modify i (fun ei => ei + k•de) dx) := 
by
  simp[revDerivProjUpdate]
  ftrans
  sorry_proof


theorem revDerivProj.comp_rule
  (f : Y → E) (g : X → Y)
  : revDerivProj K (fun x => f (g x))
    =
    fun x => 
      let ydg' := revCDeriv K g x
      let zdf' := revDerivProj K f ydg'.1
      (zdf'.1,
       fun i de => 
         ydg'.2 (zdf'.2 i de)) := 
by
  sorry_proof

theorem revDerivProjUpdate.comp_rule
  (f : Y → E) (g : X → Y)
  : revDerivProjUpdate K (fun x => f (g x))
    =
    fun x => 
      let ydg' := revDerivUpdate K g x
      let zdf' := revDerivProj K f ydg'.1
      (zdf'.1,
       fun i de k dx => 
         ydg'.2 (zdf'.2 i de) k dx) := 
by
  sorry_proof



theorem Prod.fst.arg_self.revDeriv_rule 
  (f : W → X×Y) (hf : HasAdjDiff K f)
  : revCDeriv K (fun w => (f w).1)
    =
    fun w => 
      let xydf' := revDerivProj K f w
      (xydf'.1.1, fun dx => xydf'.2 (.inl ()) dx) :=
by
  sorry_proof


theorem Prod.fst.arg_self.revDerivProj_rule
  {XIdx : Type _}
  {XVal : XIdx → Type _} [∀ i, SemiInnerProductSpace K (XVal i)]
  [TypeWithProj X XIdx XVal]
  (f : W → X×Y) (hf : HasAdjDiff K f)
  : revDerivProj K (fun w => (f w).1)
    =
    fun w => 
      let xydf' := revDerivProj K f w
      (xydf'.1.1,
       fun i dx => xydf'.2 (.inl i) dx) :=
by
  sorry_proof
