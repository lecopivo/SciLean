import SciLean.Data.Prod
import SciLean.Core.SmoothMap
import SciLean.Experimental.DiffeologicalSpaces.Diff

namespace SciLean


variable {X Y Z W Y₁ Y₂ Y₃} [Diff X] [Diff Y] [Diff Z] [Diff W] [Diff Y₁] [Diff Y₂] [Diff Y₃]


def is_diff [Diff X] [Diff Y] (f : X → Y) : Prop := sorry

class IsSmoothDepNT {Xs Y' : Type} [Diff Xs] [Diff Y']
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] : Prop where
  proof : is_diff (uncurryN n f)

class IsSmoothDepN {Xs Y'}  [Diff Xs] [Diff Y']
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] extends IsSmoothDepNT n f : Prop

abbrev IsSmoothDep (f : X → Y) : Prop
  := IsSmoothDepN 1 f

abbrev IsSmoothDepT (f : X → Y) : Prop
  := IsSmoothDepNT 1 f

--------------------------------------------------------------------------------


instance (priority := low) IsSmoothDep.remove_2_2 (f : X → Y → Z) [IsSmoothDepNT 2 f]
  : IsSmoothDepT (λ x => f x) := sorry_proof

instance (priority := low) IsSmoothDep.remove_2_1 (f : X → Y → Z) [IsSmoothDepNT 2 f] (x : X)
  : IsSmoothDepT (λ y => f x y) := sorry_proof

instance (priority := low) IsSmoothDep.remove_3_2_3 (f : X → Y → Z → W) [IsSmoothDepNT 3 f]
  : IsSmoothDepT (λ x => f x) := sorry_proof

instance (priority := low) IsSmoothDep.remove_3_1_3 (f : X → Y → Z → W) [IsSmoothDepNT 3 f] (x : X)
  : IsSmoothDepT (λ y => f x y) := sorry_proof

instance (priority := low) IsSmoothDep.remove_3_1_2 (f : X → Y → Z → W) [IsSmoothDepNT 3 f] (x : X) (y : Y)
  : IsSmoothDepT (λ z => f x y z) := sorry_proof


-- -- adding arguments

instance (priority := low) IsSmoothDep.add_extra_2_1 (f : X → Y) [IsSmoothDepT f]
  : IsSmoothDepNT 2 (λ (z : Z) x => f x) := sorry_proof

instance (priority := low) IsSmoothDep.add_extra_2_2 (f : X → Y) [IsSmoothDepT f]
  : IsSmoothDepNT 2 (λ x (z : Z) => f x) := sorry_proof

instance (priority := low) IsSmoothDep.add_extra_3_1 (f : Y → Z → W) [IsSmoothDepNT 2 f]
  : IsSmoothDepNT 3 (λ (x : X) y z => f y z) := sorry_proof

instance (priority := low) IsSmoothDep.add_extra_3_2 (f : X → Z → W) [IsSmoothDepNT 2 f]
  : IsSmoothDepNT 3 (λ x (y : Y) z => f x z) := sorry_proof

instance (priority := low) IsSmoothDep.add_extra_3_3 (f : X → Y → W) [IsSmoothDepNT 2 f]
  : IsSmoothDepNT 3 (λ x y (z : Z) => f x y) := sorry_proof

-- Core instances

instance id.arg_x.isSmoothDep
  : IsSmoothDepT λ x : X => x := sorry_proof

-- This is problematic - low priority had to be added to `remove_2_2`
example {α : Type} : IsSmoothDepNT 1 (fun (x : α → Y) => x) := inferInstance

instance const.arg_xy.isSmoothDep
  : IsSmoothDepNT 2 λ (x : X) (y : Y) => x := inferInstance

instance const.arg_x.isSmoothDep
  : IsSmoothDepT λ (x : X) (y : Y) => x := inferInstance

instance const.arg_y.isSmoothDep (x : X)
  : IsSmoothDepT λ (y : Y) => x := IsSmoothDep.remove_2_1 (λ x y => x) x

instance (priority := low) swap.arg_y.isSmoothDep {α : Type}
  (f : α → Y → Z) [∀ x, IsSmoothDepT (f x)]
  : IsSmoothDepT (λ y x => f x y) := sorry_proof

instance parm.arg_x.isSmoothDep
  (f : X → β → Z) [IsSmoothDepT f] (y : β)
  : IsSmoothDepT (λ x => f x y) := sorry_proof

instance (priority := mid-1) subst.arg_x.isSmoothDep
  (f : X → Y → Z) [IsSmoothDepNT 2 f]
  (g : X → Y) [IsSmoothDepT g] :
  IsSmoothDepT (λ x => f x (g x)) := sorry_proof

instance (priority := mid-1) subst2.arg_x.isSmoothDep
  (f : X → Y → Y₁ → Z) [IsSmoothDepNT 3 f]
  (g : X → Y → Y₁) [IsSmoothDepNT 2 g] :
  IsSmoothDepNT 2 (λ x y => f x y (g x y)) := sorry_proof

instance (priority := mid-1) subst3.arg_x.isSmoothDep
  (f : X → Y → Z → Y₁ → W) [IsSmoothDepNT 4 f]
  (g : X → Y → Z → Y₁) [IsSmoothDepNT 3 g] :
  IsSmoothDepNT 3 (λ x y z => f x y z (g x y z)) := sorry_proof

-- @[infer_tc_goals_rl]
instance comp.arg_x.isSmoothDep
  (f : Y → Z) [IsSmoothDepT f]
  (g : X → Y) [IsSmoothDepT g]
  : IsSmoothDepT (λ x => f (g x)) := by infer_instance

instance {Ws W'} [Diff Ws] [Diff W']
  (f : Z → W) [Prod.Uncurry n W Ws W'] [IsSmoothDepNT (n+1) f]
  (g : X → Y → Z) [IsSmoothDepNT 2 g]
  : IsSmoothDepNT (n+2) fun x y => f (g x y) := sorry_proof

instance {Ws W'} [Diff Ws] [Diff W']
  (f : Y₁ → Y₂→ W) [Prod.Uncurry n W Ws W'] [hf : IsSmoothDepNT (n+2) f]
  (g₁ : X → Y → Z → Y₁) [IsSmoothDepNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [IsSmoothDepNT 3 g₂]
  : IsSmoothDepNT (n+3) fun x y z => f (g₁ x y z) (g₂ x y z) := sorry_proof

instance comp2.arg_x.isSmoothDep
  (f : Y₁ → Y₂ → Z) [IsSmoothDepNT 2 f]
  (g₁ : X → Y → Y₁) [IsSmoothDepNT 2 g₁]
  (g₂ : X → Y → Y₂) [IsSmoothDepNT 2 g₂]
  : IsSmoothDepNT 2 (λ x y => f (g₁ x y) (g₂ x y)) :=
by
  infer_instance

instance comp3.arg_x.isSmoothDep
  (f : Y₁ → Y₂ → Y₃ → W) [hf : IsSmoothDepNT ((1:ℕ) + (2:ℕ)) f]
  (g₁ : X → Y → Z → Y₁) [IsSmoothDepNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [IsSmoothDepNT 3 g₂]
  (g₃ : X → Y → Z → Y₃) [IsSmoothDepNT 3 g₃]
  : IsSmoothDepNT 3 (λ x y z => f (g₁ x y z) (g₂ x y z) (g₃ x y z)) :=
by
  infer_instance

instance Prod.fst.arg_xy.isSmoothDep : IsSmoothDep (Prod.fst : X×Y → X) := sorry_proof
instance Prod.snd.arg_xy.isSmoothDep : IsSmoothDep (Prod.snd : X×Y → Y) := sorry_proof
