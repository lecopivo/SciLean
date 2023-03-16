namespace SciLean

set_option synthInstance.maxSize 10000


-- opaque definitions
opaque vec_impl (X : Type) : Type
opaque smooth_impl (f : X → Y) : Prop
opaque ℝ : Type


-- Vec Type
class Vec (X : Type) extends OfNat X 0, Add X, Sub X, Neg X, HMul ℝ X X where impl : vec_impl X
instance : Vec ℝ := sorry
instance {X Y} [Vec X] [Vec Y] : Vec (X×Y) := sorry
instance {α : Type} [Vec X] : Vec (α→X) := sorry

instance {X} [Vec X] : OfNat X 0 := Vec.toOfNat


-- IsSmooth predicate
class IsSmooth {X Y : Type} [Vec X] [Vec Y] (f : X → Y) : Prop where impl : smooth_impl f
class IsSmooth2 {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] (f : X → Y → Z) extends IsSmooth λ (x,y) => f x y
class IsSmooth3 {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] [Vec W] (f : X → Y → Z → W) extends IsSmooth λ (x,y,z) => f x y z


-- SmoothMap
structure SmoothMap (X Y) [Vec X] [Vec Y] where
  val : X → Y
  [property : IsSmooth val]

infixr:25 " ⟿ " => SmoothMap

instance {X Y} [Vec X] [Vec Y] : Vec (X ⟿ Y) := sorry
instance {X Y} [Vec X] [Vec Y] : CoeFun (X ⟿ Y) (λ _ => X → Y) := ⟨λ f => f.val⟩

-- Lambda notation
open Lean.TSyntax.Compat in
macro "λ"   xs:Lean.explicitBinders " ⟿ " b:term : term =>
  Lean.expandExplicitBinders `SciLean.SmoothMap.mk xs b


variable {X Y Z W W' Y₁ Y₂ U V} [Vec X] [Vec Y] [Vec Z] [Vec W] [Vec W'] [Vec Y₁] [Vec Y₂] [Vec U] [Vec V] {α : Type}


-- These are the core properties that needs to be proven
-- They are summarized on this wiki page: https://en.wikipedia.org/wiki/Convenient_vector_space#Main_properties_of_smooth_calculus

-- Basic property of category (with fully internalized composition)
def id : X ⟿ X := 
  SmoothMap.mk (property := sorry) λ x => x
def comp : (Y ⟿ Z) ⟿ (X ⟿ Y) ⟿ (X⟿Z) := 
  SmoothMap.mk (property := sorry) λ f => 
  SmoothMap.mk (property := sorry) λ g => 
  SmoothMap.mk (property := sorry) λ x => f (g x)

-- forgetful functor
def forget : (X⟿Y)⟿(X→Y) := 
  SmoothMap.mk (property := sorry) λ f x => f x

-- Cartesion closed
def curry : (X×Y ⟿ Z) ⟿ (X⟿Y⟿Z) := 
  SmoothMap.mk (property := sorry) λ f => 
  SmoothMap.mk (property := sorry) λ x => 
  SmoothMap.mk (property := sorry) λ y => f (x,y)

def uncurry : (X⟿Y⟿Z) ⟿ (X×Y ⟿ Z) := 
  SmoothMap.mk (property := sorry) λ f => 
  SmoothMap.mk (property := sorry) λ (x,y) => f x y

-- Arbitrary product
-- universal property
def forallMap : (α → X⟿Y) ⟿ (α → X) ⟿ (α → Y) := 
  SmoothMap.mk (property := sorry) λ f => 
  SmoothMap.mk (property := sorry) λ x a => f a (x a)
-- projection
def proj (a : α) : (α → X) ⟿ X := 
  SmoothMap.mk (property := sorry) λ f => f a
-- generalized diagonal rule - X⟿X×X
def const : X⟿(α→X) := 
  SmoothMap.mk (property := sorry) λ x a => x

-- Binary product -- these should relatively easily follow from forallMap and eval
-- universal property
def prodMap : (X⟿Y) ⟿ (X⟿Z) ⟿ (X⟿Y×Z) := 
  SmoothMap.mk (property := sorry) λ f => 
  SmoothMap.mk (property := sorry) λ g => 
  SmoothMap.mk (property := sorry) λ x => (f x, g x)
-- projections
def fst : X×Y ⟿ X := 
  SmoothMap.mk (property := sorry) λ (x,y) => x
def snd : X×Y ⟿ Y := 
  SmoothMap.mk (property := sorry) λ (x,y) => y
-- diagonal
def diag : X ⟿ X×X := 
  SmoothMap.mk (property := sorry) λ x => (x,x)


-- No sorries pass this point!
--------------------------------------------------------------------------------

def swap : X×Y⟿Y×X := prodMap snd fst
def eval : X⟿(X⟿Y)⟿Y := curry (comp (uncurry id) swap)

-- Smoothness of SmoothMap.val
instance SmoothMap.val.arg_x.isSmooth {X Y} [Vec X] [Vec Y] (f : X ⟿ Y)
  : IsSmooth f.1 := f.2
instance SmoothMap.val.arg_fx.isSmooth {X Y} [Vec X] [Vec Y]
  : IsSmooth2 (λ (f : X⟿Y) (x : X) => f x) := IsSmooth2.mk (toIsSmooth := 
by 
    have h : (λ ((f,x) : (X⟿Y)×X) => f x) = uncurry id := by simp[uncurry,id]
    rw[h]; infer_instance)


--------------------------------------------------------------------------------
-- Expressing IsSmooth2, IsSmooth3, ... in terms of IsSmooth
--------------------------------------------------------------------------------
/-
instance IsSmooth2_curry (f : X → Y → Z)
  [∀ x, IsSmooth (f x)] [IsSmooth λ x => λ y ⟿ f x y]
  : IsSmooth2 f := IsSmooth2.mk (toIsSmooth := 
by   
  have h : (λ (x,y) => f x y) = uncurry (λ x y ⟿ f x y) := by simp[uncurry]
  rw[h]; infer_instance)
  -/
  

instance IsSmooth2_uncurry_y (f : X → Y → Z) [IsSmooth2 f] (x : X)
  : IsSmooth (λ y => f x y) := 
by
  let f' := SmoothMap.mk λ (x,y) => f x y
  have h : (λ y => f x y) = curry f' x := by simp[curry]
  rw[h]; infer_instance

instance IsSmooth2_uncurry_x (f : X → Y → Z) [IsSmooth2 f]
  : IsSmooth (λ x => λ y ⟿ f x y) := 
by
  let f' := SmoothMap.mk λ (x,y) => f x y
  have h : (λ x => λ y ⟿ f x y) = curry f' := by simp[curry]
  rw[h]; infer_instance

/-
instance IsSmooth3_curry (f : X → Y → Z → W)
  [∀ x y, IsSmooth (λ z => f x y z)] [∀ x, IsSmooth λ y => λ z ⟿ f x y z] [IsSmooth λ x => λ y z ⟿ f x y z]
  : IsSmooth3 f := IsSmooth3.mk (toIsSmooth := 
by
  have h : (λ (x,y,z) => f x y z) = uncurry (comp uncurry (λ x y z ⟿ f x y z)) := by simp[uncurry,comp]
  rw[h]; infer_instance)
  -/

instance IsSmooth3_uncurry_z (f : X → Y → Z → W) [IsSmooth3 f] (x : X) (y : Y)
  : IsSmooth (λ z => f x y z) :=
by
  let f' := SmoothMap.mk λ (x,y,z) => f x y z
  have h : (λ z => f x y z) = curry (curry f' x) y := by simp[curry]
  rw[h]; infer_instance

instance IsSmooth3_uncurry_y (f : X → Y → Z → W) [IsSmooth3 f] (x : X)
  : IsSmooth (λ y => λ z ⟿ f x y z) := 
by
  let f' := SmoothMap.mk λ (x,y,z) => f x y z
  have h : (λ y => λ z ⟿ f x y z) = curry (curry f' x) := by simp[curry]
  rw[h]; infer_instance

instance IsSmooth3_uncurry_x (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ x => λ y z ⟿ f x y z) := 
by 
  let f' := SmoothMap.mk λ (x,y,z) => f x y z
  have h : (λ x => λ y z ⟿ f x y z) = comp curry (λ x ⟿ curry f' x) := by simp[curry,comp]
  rw[h]; infer_instance

-- ...

--------------------------------------------------------------------------------
-- Forgetting smoothness
--------------------------------------------------------------------------------

instance IsSmooth2_forget_y (f : X → Y → Z) [∀ x, IsSmooth (f x)] [IsSmooth λ x => λ y ⟿ f x y] -- [IsSmooth2 f]
  : IsSmooth f := 
by 
  try infer_instance
  have h : f = comp forget (λ x y ⟿ f x y) := by simp[comp,forget]
  rw[h]; infer_instance

instance IsSmooth3_forget_z (f : X → Y → Z → W) [∀ x y, IsSmooth (λ z => f x y z)] [∀ x, IsSmooth λ y => λ z ⟿ f x y z] [IsSmooth λ x => λ y z ⟿ f x y z]-- [IsSmooth3 f]
  : IsSmooth (λ x => λ y ⟿ λ z => f x y z) := 
by 
  try infer_instance
  have h : (λ x => λ y ⟿ λ z => f x y z) 
           = 
           comp (comp forget) (λ x y z ⟿ f x y z) 
         := by simp[comp,forget]
  rw[h]; infer_instance

instance IsSmooth3_forget_y (f : X → Y → Z → W) (y : Y) [∀ x y, IsSmooth (λ z => f x y z)] [∀ x, IsSmooth λ y => λ z ⟿ f x y z] [IsSmooth λ x => λ y z ⟿ f x y z] -- [IsSmooth3 f] 
  : IsSmooth (λ x => λ z ⟿ f x y z) := 
by 
  try infer_instance
  have h : (λ x => λ z ⟿ f x y z) 
           = 
           comp (eval y) (λ x y z ⟿ f x y z) 
         := by simp[comp, eval, swap, curry, uncurry, id, prodMap, fst, snd]
  rw[h]; infer_instance

-- ...

--------------------------------------------------------------------------------
-- Lambda calculus rules for IsSmooth
--------------------------------------------------------------------------------

instance IsSmooth_rule_I : IsSmooth (λ x : X => x) := id.property

instance IsSmooth_rule_K₂ (x : X) : IsSmooth (λ _ : Y => x) := 
by
  have h : (λ _ : Y => x) = curry fst x := by simp[curry,fst]
  rw[h]; infer_instance

instance IsSmooth_rule_K₁ : IsSmooth (λ (x : X) => λ (_ : Y) ⟿ x) := 
by
  have h : (λ (x : X) => λ (_ : Y) ⟿ x) = curry fst := by simp[curry,fst]
  rw[h]; infer_instance

instance IsSmooth_rule_S₃
  (f : X → Y → Z) [∀ x, IsSmooth (f x)] [IsSmooth λ x => λ y ⟿ f x y] -- [IsSmooth2 f]
  (g : X → Y)  [IsSmooth g]
  : IsSmooth (λ x => f x (g x)) := 
by
  have h : (λ x => f x (g x)) 
           = 
           comp (uncurry (λ x y ⟿ f x y)) (prodMap id (λ x ⟿ g x)) 
         := by simp[comp, uncurry, prodMap, id]
  rw[h]; infer_instance

instance IsSmooth_rule_S₂ 
  (f : X → Y → Z)   [∀ x, IsSmooth (f x)] [IsSmooth λ x => λ y ⟿ f x y] -- [IsSmooth2 f] 
  (g : V → (X → Y)) [∀ v, IsSmooth (g v)] [IsSmooth λ v => λ x ⟿ g v x] -- [IsSmooth2 g]
  : IsSmooth (λ v => λ x ⟿ f x (g v x)) := 
by
  let f' := uncurry (λ x y ⟿ f x y)
  let g' := prodMap snd (uncurry (λ v x ⟿ g v x))
  have h : (λ v => λ x ⟿ f x (g v x)) 
           = 
           curry (comp f' g') 
         := by simp[comp,curry,uncurry,prodMap,fst,snd]
  rw[h]; infer_instance

instance IsSmooth_rule_S₁ 
  (f : U → (X → Y → Z)) [∀ u x, IsSmooth (λ y => f u x y)] [∀ u, IsSmooth λ x => λ y ⟿ f u x y] [IsSmooth λ u => λ x y ⟿ f u x y] -- [IsSmooth3 f] 
  (g : V → (X → Y))      [∀ v, IsSmooth (g v)] [IsSmooth λ v => λ x ⟿ g v x]  -- [IsSmooth2 g]
  : IsSmooth (λ u => λ v x ⟿ f u x (g v x)) := 
by
  let f' := uncurry (comp uncurry (λ u x y ⟿ f u x y))
  let g' := prodMap (fst (X:=U)) (prodMap (comp snd snd) (comp (uncurry (λ v x ⟿ g v x)) snd))
  have h : (λ u => λ v x ⟿ f u x (g v x)) 
           = 
           comp curry (curry (comp f' g')) 
         := by simp[comp,curry,uncurry,prodMap,fst,snd]
  rw[h]; infer_instance


instance (priority:=low) IsSmooth_rule_C₂ 
  (f : α → X → Y) [∀ a, IsSmooth (f a)]
  : IsSmooth λ x a => f a x := 
by
  have h : (λ x a => f a x) 
           = 
           comp (forallMap (λ a => λ x ⟿ f a x)) const 
         := by simp[comp, forallMap, const]
  rw[h]; infer_instance

instance (priority:=low) IsSmooth_rule_C₁ 
  (f : U → α → X → Y) [∀ a u, IsSmooth (λ x => f u a x)] [∀ a, IsSmooth (λ u => λ x ⟿ f u a x)] -- [∀ a, IsSmooth2 (λ u x => f u a x)]
  : IsSmooth λ u => λ x ⟿ λ a => f u a x :=
by
  have h : (λ u => λ x ⟿ λ a => f u a x) 
           =
           curry (λ xy ⟿ λ a => uncurry (λ u x ⟿ f u a x) xy)
         := by simp[curry,uncurry]
  rw[h]; infer_instance
 
instance (priority:=low) IsSmooth_rule_C'₂ 
  (f : X → α → Y) (a : α) [IsSmooth f] 
  : IsSmooth λ x => f x a :=
by
  have h : (λ x => f x a) = comp (proj a) (λ x ⟿ f x) := by simp[comp,proj]
  rw[h]; infer_instance

instance (priority:=low) IsSmooth_rule_C'₁ 
  (f : U → X → α → Y) (a : α) [∀ u, IsSmooth (f u)] [IsSmooth λ u => λ x ⟿ f u x] -- [IsSmooth2 f] 
  : IsSmooth λ u => λ x ⟿ f u x a :=
by
  have h : (λ u => λ x ⟿ f u x a) 
           = 
           curry (λ xy ⟿ uncurry (λ u x ⟿ f u x) xy a) 
         := by simp[curry, uncurry]
  rw[h]; infer_instance


instance (priority:=low-1) IsSmooth_rule_C'' (f : X → Y → Z)  [∀ x, IsSmooth (f x)] [IsSmooth λ x => λ y ⟿ f x y]
  : IsSmooth (λ y => λ x ⟿ f x y) := by infer_instance


--------------------------------------------------------------------------------

-- Permuting arguments

example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ x => λ z y ⟿ f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ x => λ z ⟿ f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ x y => λ z ⟿ f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ y => λ x z ⟿ f x y z) := by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ z => λ x y ⟿ f x y z) := by infer_instance


example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ y => λ x z ⟿ f x y z) := by infer_instance



example (f : X → X → X → Z) [IsSmooth3 f]
  : IsSmooth (λ x => λ x' y ⟿ f x' x y) := 
by infer_instance

example (f : X → X → X → Z) [IsSmooth3 f]
  : IsSmooth (λ x => λ x' y ⟿ f x' x y) := 
by infer_instance

instance IsSmooth_uncurry_S (f : X → Y → W → Z) [IsSmooth3 f]
  (g : X → Y → W) [IsSmooth2 g]
  : IsSmooth (λ x => λ y ⟿ f x y (g x y)) := by (try infer_instance); admit


instance IsSmooth_uncurry_S' (f : X → Y → W → Z) [IsSmooth3 f]
  (g : X → Y → W) [IsSmooth2 g]
  : IsSmooth (λ x => λ x' y ⟿ f x y (g x' y)) := by infer_instance


set_option synthInstance.maxSize 300 in
instance (f : Y₁ → Y₂ → Z) [IsSmooth2 f]
  (g₁ : X → Y₁) [IsSmooth g₁]
  : IsSmooth fun x => λ y₂ ⟿ f (g₁ x) y₂ := 
by 
  try infer_instance
  apply IsSmooth_uncurry_S (λ x y w => f w y) (λ x y => g₁ x)


set_option synthInstance.maxSize 300 in
instance IsSmooth_rule_D (f : Y₁ → Y₂ → Z) [IsSmooth2 f]
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : IsSmooth (λ x => f (g₁ x) (g₂ x)) := 
by infer_instance


instance (f : X → Y → Z) [IsSmooth2 f]
  (g : W → Y → X) [IsSmooth2 g]
  : IsSmooth fun y => f (g w y) y := 
by infer_instance


set_option synthInstance.maxSize 300 in
instance IsSmooth_uncurry_x_comp (f : X → Y → Z) [IsSmooth2 f]
  (g : W → Y → X) [IsSmooth2 g]
  : IsSmooth (λ w => λ y ⟿ f (g w y) y) := 
by 
  try infer_instance
  apply IsSmooth_uncurry_S (λ a b c => f c b) g


-- Test in forgeting smoothenss in various components
example (f : X → Y → Z) [IsSmooth2 f]
  : IsSmooth f := 
by infer_instance

example (f : X → Y → Z) [IsSmooth2 f] (x : X)
  : IsSmooth (f x) := 
by infer_instance

example (f : X → Y → Z) [IsSmooth2 f] (y : Y)
  : IsSmooth (λ y => f x y) := 
by infer_instance


-- IsSmooth3 to IsSmooth
example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ x y z => f x y z) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f] (x : X)
  : IsSmooth (f x) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f] (x : X) (y : Y)
  : IsSmooth (f x y) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f] (x : X) (z : Z)
  : IsSmooth (λ y => f x y z) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f] (y : Y) (z : Z)
  : IsSmooth (λ x => f x y z) := 
by infer_instance


-- IsSmooth3 to IsSmooth2
example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ x => λ y ⟿ λ z => f x y z) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ x => λ z ⟿ λ y => f x y z) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ y => λ x ⟿ λ z => f x y z) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ y => λ z ⟿ λ x => f x y z) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ z => λ x ⟿ λ y => f x y z) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ z => λ y ⟿ λ x => f x y z) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f] (z : Z)
  : IsSmooth (λ x => λ y ⟿ f x y z) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f] (y : Y)
  : IsSmooth (λ x => λ z ⟿ f x y z) := 
by infer_instance

example (f : X → Y → Z → W) [IsSmooth3 f] (x : X)
  : IsSmooth (λ y => λ z ⟿ f x y z) := 
by infer_instance


-- Duplicating arguments
example (f : X → X → Z) [IsSmooth2 f]
  : IsSmooth (λ x => f x x) := 
by infer_instance

example (f : X → X → X → Z) [IsSmooth3 f]
  : IsSmooth (λ x => λ y ⟿ f x x y) := 
by infer_instance

example (f : X → X → X → Z) [IsSmooth3 f]
  : IsSmooth (λ x => λ y ⟿ f x x y) := 
by infer_instance

example (f : X → X → X → Z) [IsSmooth3 f]
  : IsSmooth (λ x => λ y ⟿ f x y x) := 
by infer_instance

example (f : X → X → X → Z) [IsSmooth3 f]
  : IsSmooth (λ x => λ y ⟿ f y x x) := 
by infer_instance

example (f : X → X → X → Z) [IsSmooth3 f]
  : IsSmooth (λ x => λ y ⟿ f x y y) := 
by infer_instance

example (f : X → X → X → Z) [IsSmooth3 f]
  : IsSmooth (λ x => λ y ⟿ f y x y) := 
by infer_instance

example (f : X → X → X → Z) [IsSmooth3 f]
  : IsSmooth (λ x => λ y ⟿ f x y y) := 
by infer_instance
