import SciLean.Core.Differential
import SciLean.Core.Adjoint

namespace SciLean

variable {α β γ : Type}
variable {X Y Z W : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] [SemiHilbert W]
variable {Y₁ Y₂ Y₃ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂] [SemiHilbert Y₃]
variable {ι : Type} [Enumtype ι]


-- /-- Transitive closure of `HasAdjDiffN`
-- -/
-- class HasAdjDiffNT {X Y : Type} {Xs Y' : Type} [SemiHilbert Xs] [SemiHilbert Y']
--   (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] : Prop where
--   proof : IsSmoothNT n f ∧ ∀ x, HasAdjointT (∂ (uncurryN n f) x)

-- class HasAdjDiffN {X Y : Type} {Xs Y' : Type} [SemiHilbert Xs] [SemiHilbert Y']
--   (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] extends HasAdjDiffNT n f : Prop

-- abbrev HasAdjDiffT {X Y : Type} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) := HasAdjDiffNT 1 f
-- abbrev HasAdjDiff {X Y : Type} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) := HasAdjDiffN 1 f

-- class HasAdjDiff (f : X → Y) : Prop where
--   isSmooth : IsSmooth f
--   hasAdjDiff : ∀ x, HasAdjoint $ ∂ f x
instance (priority:=low-10) {X Y : Type} {Xs Y' : Type} [SemiHilbert Xs] [SemiHilbert Y']
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y']
  [sf : IsSmoothN n f] [∀ x, HasAdjoint (∂ (uncurryN n f) x)]
  : HasAdjDiffN n f
  := HasAdjDiffN.mk (toHasAdjDiffNT:= by constructor; apply sf.1; infer_instance)

theorem infer_HasAdjDiff {X Y : Type} {Xs Y' : Type} [SemiHilbert Xs] [SemiHilbert Y']
  {n : Nat} {f : X → Y} [Prod.Uncurry n (X → Y) Xs Y'] [IsSmoothT (uncurryN n f)]
  : (∀ x, HasAdjointT $ ∂ (uncurryN n f) x) → HasAdjDiffNT n f
  := λ h => by constructor; infer_instance; apply h

theorem infer_HasAdjDiff' {X Y : Type} {Xs Y' : Type} [SemiHilbert Xs] [SemiHilbert Y']
  {n : Nat} {f : X → Y} [Prod.Uncurry n (X → Y) Xs Y'] [IsSmoothT (uncurryN n f)]
  : (∀ x, HasAdjointT $ ∂ (uncurryN n f) x) → HasAdjDiffN n f
  := λ h => sorry

-- instance (priority := low-9) HasAdjoint_HasAdjDiff (f : X → Y) [HasAdjoint f] : HasAdjDiff f := 
-- by apply infer_HasAdjDiff'; symdiff; infer_instance; done

--------------------------------------------------------------------------------


--- Removing arguments - generalized this 

instance HasAdjDiff2_apply_2 (f : X → Y → Z) [HasAdjDiffNT 2 f] (y : Y)
  : HasAdjDiffT (λ x => f x y) := sorry_proof

instance HasAdjDiff2_apply_1 (f : X → Y → Z) [HasAdjDiffNT 2 f] (x : X)
  : HasAdjDiffT (λ y => f x y) := sorry_proof

instance (f : X → Y → Z → W) [HasAdjDiffNT 3 f] (y z)
  : HasAdjDiffT (λ x => f x y z) := sorry_proof

instance (f : X → Y → Z → W) [HasAdjDiffNT 3 f] (x z)
  : HasAdjDiffT (λ y => f x y z) := sorry_proof

instance (f : X → Y → Z → W) [HasAdjDiffNT 3 f] (x y)
  : HasAdjDiffT (λ z => f x y z) := sorry_proof


--- Adding arguments - generalized this 

instance HasAdjDiff_add_extra_2_1 (f : X → Y) [hf : HasAdjDiffT f]
  : HasAdjDiffNT 2 (λ (z : Z) x => f x) := sorry_proof

instance HasAdjDiff_add_extra_2_2 (f : X → Y) [HasAdjDiffT f]
  : HasAdjDiffNT 2 (λ x (z : Z) => f x) := sorry_proof

instance HasAdjDiff_add_extra_3_1 (f : Y → Z → W) [HasAdjDiffNT 2 f]
  : HasAdjDiffNT 3 (λ (x : X) y z => f y z) := sorry_proof

instance HasAdjDiff_add_extra_3_2 (f : X → Z → W) [HasAdjDiffNT 2 f]
  : HasAdjDiffNT 3 (λ x (y : Y) z => f x z) := sorry_proof

instance HasAdjDiff_add_extra_3_3 (f : X → Y → W) [HasAdjDiffNT 2 f]
  : HasAdjDiffNT 3 (λ x y (z : Z) => f x y) := sorry_proof



--------------------------------------------------------------------------------

instance id.arg_x.hasAdjDiff
  : HasAdjDiffT (λ x : X => x) := by apply infer_HasAdjDiff; intro; simp; infer_instance

instance const.arg_x.hasAdjDiff
  : HasAdjDiffT (λ (x : X) (i : ι) => x) := by apply infer_HasAdjDiff; intro; symdiff; infer_instance; done

instance const.arg_y.hasAdjDiff (x : X)
  : HasAdjDiffT (λ (y : Y) => x) := by apply infer_HasAdjDiff; intro; simp; infer_instance

instance (priority := low) swap.arg_y.hasAdjDiff
  (f : ι → Y → Z) [inst : ∀ x, HasAdjDiffT (f x)]
  : HasAdjDiffT (λ y x => f x y) :=
by
  have is := λ x => (inst x).1
  have ia := λ x => (inst x).2
  apply infer_HasAdjDiff; intro; 
  simp[uncurryN, Prod.Uncurry.uncurry]; infer_instance; done


instance (priority := mid-1) subst.arg_x.hasAdjDiff 
  (f : X → Y → Z) [instf : HasAdjDiffNT 2 f]
  (g : X → Y) [instg : HasAdjDiffT g] 
  : HasAdjDiffT (λ x => f x (g x)) := 
by
  have isf := instf.1
  have iaf := instf.2
  have isg := instg.1
  have iag := instg.2
  
  have : ∀ x, IsSmoothT (f x) := sorry_proof
  have : IsSmoothT (λ x => λ y ⟿ f x y) := sorry_proof

  sorry_proof 
  -- apply infer_HasAdjDiff; intro x; 
  -- simp[uncurryN, Prod.Uncurry.uncurry, tangentMap]; 
  -- -- Thise should follow from `iaf`
  -- have : ∀ x y, HasAdjointT λ dx => ∂ f x dx y := sorry_proof
  -- have : ∀ x y, HasAdjointT λ dy => ∂ (f x) y dy := sorry_proof
  -- infer_instance; done

instance (priority := mid-1) subst2.arg_x.hasAdjDiff 
  (f : X → Y → Y₁ → Z) [HasAdjDiffNT 3 f]
  (g : X → Y → Y₁) [HasAdjDiffNT 2 g] :
  HasAdjDiffNT 2 (λ x y => f x y (g x y)) := sorry_proof

instance (priority := mid-1) subst3.arg_x.hasAdjDiff 
  (f : X → Y → Z → Y₁ → W) [HasAdjDiffNT 4 f]
  (g : X → Y → Z → Y₁) [HasAdjDiffNT 3 g] :
  HasAdjDiffNT 3 (λ x y z => f x y z (g x y z)) := sorry_proof


instance comp.arg_x.hasAdjDiff
  (f : Y → Z) [instf : HasAdjDiffT f] 
  (g : X → Y) [instg : HasAdjDiffT g]
  : HasAdjDiffT (λ x => f (g x)) := by infer_instance 

instance {Ws W' : Type} [SemiHilbert Ws] [SemiHilbert W']
  (f : Z → W) [Prod.Uncurry n W Ws W'] [HasAdjDiffNT (n+1) f]
  (g : X → Y → Z) [HasAdjDiffNT 2 g]
  : HasAdjDiffNT (n+2) fun x y => f (g x y) := sorry_proof

instance {Ws W' : Type} [SemiHilbert Ws] [SemiHilbert W']
  (f : Y₁ → Y₂→ W) [Prod.Uncurry n W Ws W'] [HasAdjDiffNT (n+2) f]
  (g₁ : X → Y → Z → Y₁) [HasAdjDiffNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [HasAdjDiffNT 3 g₂]
  : HasAdjDiffNT (n+3) fun x y z => f (g₁ x y z) (g₂ x y z) := sorry_proof

instance comp2.arg_x.HasAdjDiff
  (f : Y₁ → Y₂ → Z) [HasAdjDiffNT 2 f]
  (g₁ : X → Y → Y₁) [HasAdjDiffNT 2 g₁]
  (g₂ : X → Y → Y₂) [HasAdjDiffNT 2 g₂]
  : HasAdjDiffNT 2 (λ x y => f (g₁ x y) (g₂ x y)) := 
by
  have : HasAdjDiffNT 3 fun x y => f (g₁ x y) := by infer_instance
  infer_instance 

instance comp3.arg_x.HasAdjDiff 
  (f : Y₁ → Y₂ → Y₃ → W) [HasAdjDiffNT 3 f]
  (g₁ : X → Y → Z → Y₁) [HasAdjDiffNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [HasAdjDiffNT 3 g₂]
  (g₃ : X → Y → Z → Y₃) [HasAdjDiffNT 3 g₃]
  : HasAdjDiffNT 3 (λ x y z => f (g₁ x y z) (g₂ x y z) (g₃ x y z)) := 
by
  -- have : HasAdjDiffNT 4 fun x y z => f (g₁ x y z) (g₂ x y z) := by apply hoho
  infer_instance

instance diag.arg_x.hasAdjDiff
  (f : Y₁ → Y₂ → Z) [instf : HasAdjDiffNT 2 f] 
  (g₁ : X → Y₁) [instg1 : HasAdjDiffT g₁]
  (g₂ : X → Y₂) [instg2 : HasAdjDiffT g₂]
  : HasAdjDiffT (λ x => f (g₁ x) (g₂ x)) := by infer_instance

instance eval.arg_x.parm1.hasAdjDiff
  (f : X → ι → Z) [inst : HasAdjDiffT f] (i : ι)
  : HasAdjDiffT (λ x => f x i) := 
  by
    have := inst.1
    have := inst.2

    apply infer_HasAdjDiff; intro; simp; infer_instance

----------------------------------------------------------------------

instance comp.arg_x.parm1.hasAdjDiff
  (a : α)
  (f : Y → α → Z) [HasAdjDiffT λ y => f y a]
  (g : X → Y) [HasAdjDiffT g]
  : HasAdjDiffT λ x => f (g x) a := 
  by 
    apply comp.arg_x.hasAdjDiff (λ y => f y a) g
    done

instance diag.arg_x.parm1.hasAdjDiff
  (a : α)
  (f : Y₁ → Y₂ → α → Z) [HasAdjDiffNT 2 λ y₁ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [HasAdjDiffT g₁] 
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : HasAdjDiffT λ x => f (g₁ x) (g₂ x) a := 
  by 
    apply diag.arg_x.hasAdjDiff (λ y₁ y₂ => f y₁ y₂ a) g₁ g₂
    done

