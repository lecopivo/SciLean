import SciLean.Core.HilbertDiff
import SciLean.Core.DifferentialDep
import SciLean.Core.Adjoint

namespace SciLean

variable {α β γ : Type}
variable {X Y Z W : Type} [SemiHilbertDiff X] [SemiHilbertDiff Y] [SemiHilbertDiff Z] [SemiHilbertDiff W]
variable {Y₁ Y₂ Y₃ : Type} [SemiHilbertDiff Y₁] [SemiHilbertDiff Y₂] [SemiHilbertDiff Y₃]
variable {ι : Type} [Enumtype ι]


/-- Transitive closure of `HasAdjDiffDepN`
-/
class HasAdjDiffDepNT {X Y : Type} {Xs Y' : Type} [SemiHilbertDiff Xs] [SemiHilbertDiff Y']
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] : Prop where
  proof : IsSmoothDepNT n f ∧ ∀ x, HasAdjointT (∂ (uncurryN n f) x)

class HasAdjDiffDepN {X Y : Type} {Xs Y' : Type} [SemiHilbertDiff Xs] [SemiHilbertDiff Y']
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] extends HasAdjDiffDepNT n f : Prop

abbrev HasAdjDiffDepT {X Y : Type} [SemiHilbertDiff X] [SemiHilbertDiff Y] (f : X → Y) := HasAdjDiffDepNT 1 f
abbrev HasAdjDiffDep {X Y : Type} [SemiHilbertDiff X] [SemiHilbertDiff Y] (f : X → Y) := HasAdjDiffDepN 1 f

-- class HasAdjDiffDep (f : X → Y) : Prop where
--   isSmooth : IsSmooth f
--   hasAdjDiffDep : ∀ x, HasAdjoint $ ∂ f x
instance (priority:=low-10) {X Y : Type} {Xs Y' : Type} [SemiHilbertDiff Xs] [SemiHilbertDiff Y']
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y']
  [IsSmoothDepN n f] [∀ x, HasAdjoint (∂ (uncurryN n f) x)]
  : HasAdjDiffDepN n f
  := HasAdjDiffDepN.mk (toHasAdjDiffDepNT:= by constructor; constructor; infer_instance; infer_instance)

theorem infer_HasAdjDiffDep {X Y : Type} {Xs Y' : Type} [SemiHilbertDiff Xs] [SemiHilbertDiff Y']
  {n : Nat} {f : X → Y} [Prod.Uncurry n (X → Y) Xs Y'] [IsSmoothDepNT n f]
  : (∀ x, HasAdjointT $ ∂ (uncurryN n f) x) → HasAdjDiffDepNT n f
  := λ h => by constructor; constructor; infer_instance; apply h

--------------------------------------------------------------------------------


--- Removing arguments - generalized this 

instance HasAdjDiffDep2_apply_2 (f : X → Y → Z) [HasAdjDiffDepNT 2 f] (y : Y)
  : HasAdjDiffDepT (λ x => f x y) := sorry_proof

instance HasAdjDiffDep2_apply_1 (f : X → Y → Z) [HasAdjDiffDepNT 2 f] (x : X)
  : HasAdjDiffDepT (λ y => f x y) := sorry_proof

instance (f : X → Y → Z → W) [HasAdjDiffDepNT 3 f] (y z)
  : HasAdjDiffDepT (λ x => f x y z) := sorry_proof

instance (f : X → Y → Z → W) [HasAdjDiffDepNT 3 f] (x z)
  : HasAdjDiffDepT (λ y => f x y z) := sorry_proof

instance (f : X → Y → Z → W) [HasAdjDiffDepNT 3 f] (x y)
  : HasAdjDiffDepT (λ z => f x y z) := sorry_proof


--- Adding arguments - generalized this 

instance HasAdjDiffDep_add_extra_2_1 (f : X → Y) [hf : HasAdjDiffDepT f]
  : HasAdjDiffDepNT 2 (λ (z : Z) x => f x) := sorry_proof

instance HasAdjDiffDep_add_extra_2_2 (f : X → Y) [HasAdjDiffDepT f]
  : HasAdjDiffDepNT 2 (λ x (z : Z) => f x) := sorry_proof

instance HasAdjDiffDep_add_extra_3_1 (f : Y → Z → W) [HasAdjDiffDepNT 2 f]
  : HasAdjDiffDepNT 3 (λ (x : X) y z => f y z) := sorry_proof

instance HasAdjDiffDep_add_extra_3_2 (f : X → Z → W) [HasAdjDiffDepNT 2 f]
  : HasAdjDiffDepNT 3 (λ x (y : Y) z => f x z) := sorry_proof

instance HasAdjDiffDep_add_extra_3_3 (f : X → Y → W) [HasAdjDiffDepNT 2 f]
  : HasAdjDiffDepNT 3 (λ x y (z : Z) => f x y) := sorry_proof



--------------------------------------------------------------------------------

instance id.arg_x.hasAdjDiffDep
  : HasAdjDiffDepT (λ x : X => x) := by apply infer_HasAdjDiffDep; intro; simp; infer_instance


-- TODO: move somewhere else
instance const.arg_x.hasAdjoint_no_index {X} [SemiHilbert X]
  : HasAdjointT (Y:= no_index _) λ (x : X) (i : ι) => x := sorry_proof
--

instance const.arg_x.hasAdjDiffDep
  : HasAdjDiffDepT (λ (x : X) (i : ι) => x) := by apply infer_HasAdjDiffDep; intro; unfold uncurryN; unfold Prod.Uncurry.uncurry; unfold instUncurryOfNatNatInstOfNatNatForAll; simp; infer_instance; done

set_option trace.Meta.Match.unify true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.pp.analyze.tryUnify true in
instance const.arg_y.hasAdjDiffDep (x : X)
  : HasAdjDiffDepT (λ (y : Y) => x) := 
by 
  apply infer_HasAdjDiffDep; intro y;
  unfold uncurryN; unfold Prod.Uncurry.uncurry; unfold instUncurryOfNatNatInstOfNatNatForAll; 
  simp; apply const.arg_y.hasAdjoint (Y:=𝒯[y] Y) (X:=𝒯[x] X); infer_instance

instance (priority := low) swap.arg_y.hasAdjDiffDep
  (f : ι → Y → Z) [inst : ∀ x, HasAdjDiffDepT (f x)]
  : HasAdjDiffDepT (λ y x => f x y) :=
by
  have is := λ x => (inst x).proof.1
  have ia := λ x => (inst x).proof.2
  apply infer_HasAdjDiffDep; intro;
  unfold uncurryN; unfold Prod.Uncurry.uncurry; unfold instUncurryOfNatNatInstOfNatNatForAll; 
  simp; infer_instance; done


instance (priority := mid-1) subst.arg_x.hasAdjDiffDep 
  (f : X → Y → Z) [instf : HasAdjDiffDepNT 2 f]
  (g : X → Y) [instg : HasAdjDiffDepT g] 
  : HasAdjDiffDepT (λ x => f x (g x)) := 
by
  have isf := instf.proof.1
  have iaf := instf.proof.2
  have isg := instg.proof.1
  have iag := instg.proof.2

  apply infer_HasAdjDiffDep; intro; 
  simp[uncurryN, Prod.Uncurry.uncurry, tangentMap]; admit

instance (priority := mid-1) subst2.arg_x.hasAdjDiffDep 
  (f : X → Y → Y₁ → Z) [HasAdjDiffDepNT 3 f]
  (g : X → Y → Y₁) [HasAdjDiffDepNT 2 g] :
  HasAdjDiffDepNT 2 (λ x y => f x y (g x y)) := sorry_proof

instance (priority := mid-1) subst3.arg_x.hasAdjDiffDep 
  (f : X → Y → Z → Y₁ → W) [HasAdjDiffDepNT 4 f]
  (g : X → Y → Z → Y₁) [HasAdjDiffDepNT 3 g] :
  HasAdjDiffDepNT 3 (λ x y z => f x y z (g x y z)) := sorry_proof


instance comp.arg_x.hasAdjDiffDep
  (f : Y → Z) [instf : HasAdjDiffDepT f] 
  (g : X → Y) [instg : HasAdjDiffDepT g]
  : HasAdjDiffDepT (λ x => f (g x)) := by infer_instance 

instance {Ws W' : Type} [SemiHilbertDiff Ws] [SemiHilbertDiff W']
  (f : Z → W) [Prod.Uncurry n W Ws W'] [HasAdjDiffDepNT (n+1) f]
  (g : X → Y → Z) [HasAdjDiffDepNT 2 g]
  : HasAdjDiffDepNT (n+2) fun x y => f (g x y) := sorry_proof

instance {Ws W' : Type} [SemiHilbertDiff Ws] [SemiHilbertDiff W']
  (f : Y₁ → Y₂→ W) [Prod.Uncurry n W Ws W'] [HasAdjDiffDepNT (n+2) f]
  (g₁ : X → Y → Z → Y₁) [HasAdjDiffDepNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [HasAdjDiffDepNT 3 g₂]
  : HasAdjDiffDepNT (n+3) fun x y z => f (g₁ x y z) (g₂ x y z) := sorry_proof

instance comp2.arg_x.HasAdjDiffDep
  (f : Y₁ → Y₂ → Z) [HasAdjDiffDepNT 2 f]
  (g₁ : X → Y → Y₁) [HasAdjDiffDepNT 2 g₁]
  (g₂ : X → Y → Y₂) [HasAdjDiffDepNT 2 g₂]
  : HasAdjDiffDepNT 2 (λ x y => f (g₁ x y) (g₂ x y)) := 
by
  have : HasAdjDiffDepNT 3 fun x y => f (g₁ x y) := by infer_instance
  infer_instance 

instance comp3.arg_x.HasAdjDiffDep 
  (f : Y₁ → Y₂ → Y₃ → W) [HasAdjDiffDepNT 3 f]
  (g₁ : X → Y → Z → Y₁) [HasAdjDiffDepNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [HasAdjDiffDepNT 3 g₂]
  (g₃ : X → Y → Z → Y₃) [HasAdjDiffDepNT 3 g₃]
  : HasAdjDiffDepNT 3 (λ x y z => f (g₁ x y z) (g₂ x y z) (g₃ x y z)) := 
by
  -- have : HasAdjDiffDepNT 4 fun x y z => f (g₁ x y z) (g₂ x y z) := by apply hoho
  infer_instance

instance diag.arg_x.hasAdjDiffDep
  (f : Y₁ → Y₂ → Z) [instf : HasAdjDiffDepNT 2 f] 
  (g₁ : X → Y₁) [instg1 : HasAdjDiffDepT g₁]
  (g₂ : X → Y₂) [instg2 : HasAdjDiffDepT g₂]
  : HasAdjDiffDepT (λ x => f (g₁ x) (g₂ x)) := by infer_instance

instance eval.arg_x.parm1.hasAdjDiffDep
  (f : X → ι → Z) [inst : HasAdjDiffDepT f] (i : ι)
  : HasAdjDiffDepT (λ x => f x i) := 
  by
    have := inst.proof.1
    have := inst.proof.2

    apply infer_HasAdjDiffDep; intro; simp; infer_instance

----------------------------------------------------------------------

instance comp.arg_x.parm1.hasAdjDiffDep
  (a : α)
  (f : Y → α → Z) [HasAdjDiffDepT λ y => f y a]
  (g : X → Y) [HasAdjDiffDepT g]
  : HasAdjDiffDepT λ x => f (g x) a := 
  by 
    apply comp.arg_x.hasAdjDiffDep (λ y => f y a) g
    done

instance diag.arg_x.parm1.hasAdjDiffDep
  (a : α)
  (f : Y₁ → Y₂ → α → Z) [HasAdjDiffDepNT 2 λ y₁ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [HasAdjDiffDepT g₁] 
  (g₂ : X → Y₂) [HasAdjDiffDepT g₂]
  : HasAdjDiffDepT λ x => f (g₁ x) (g₂ x) a := 
  by 
    apply diag.arg_x.hasAdjDiffDep (λ y₁ y₂ => f y₁ y₂ a) g₁ g₂
    done
