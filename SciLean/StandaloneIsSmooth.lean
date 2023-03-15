namespace SciLean

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

variable {X Y Z W W' Y₁ Y₂ U V} [Vec X] [Vec Y] [Vec Z] [Vec W] [Vec W'] [Vec Y₁] [Vec Y₂] [Vec U] [Vec V] {α : Type}


-- These are the core properties that needs to be proven

-- Basic category 
def id : X ⟿ X := SmoothMap.mk (λ x => x) (property := sorry)
def comp : (Y ⟿ Z) → (X ⟿ Y) → (X⟿Z) := λ f g => SmoothMap.mk (λ x => f (g x)) (property := sorry)

-- forgetful functor
def forget : (X⟿Y)⟿(X→Y) := SmoothMap.mk (λ f x => f x) (property := sorry)

-- Cartesion closed
def curry : (X×Y ⟿ Z) ⟿ (X⟿Y⟿Z) := SmoothMap.mk (λ f => SmoothMap.mk (λ x => SmoothMap.mk (λ y => f (x,y)) (property := sorry)) (property := sorry)) (property := sorry)
def uncurry : (X⟿Y⟿Z) ⟿ (X×Y ⟿ Z) := SmoothMap.mk (λ f => SmoothMap.mk (λ (x,y) => f x y) (property := sorry)) (property := sorry)

-- Arbitrary product
-- universal property
def forallMap : (α → X⟿Y) → (α → X) ⟿ (α → Y) := λ f => SmoothMap.mk (λ x a => f a (x a)) (property := sorry)
-- projection
def eval (a : α) : (α → X) ⟿ X := SmoothMap.mk (λ f => f a) (property := sorry)
-- generalized diagonal rule - X⟿X×X
def const : X⟿(α→X) := SmoothMap.mk (λ x a => x) (property := sorry)

-- Binary product -- these should relatively easily follow from forallMap and eval
-- universal property
def prodMap : (X⟿Y) → (X⟿Z) → (X⟿Y×Z) := λ f g => SmoothMap.mk (λ x => (f x, g x)) (property := sorry)
-- projections
def fst : X×Y ⟿ X := SmoothMap.mk (λ (x,y) => x) (property := sorry)
def snd : X×Y ⟿ Y := SmoothMap.mk (λ (x,y) => y) (property := sorry)
-- diagonal
def diag : X ⟿ X×X := SmoothMap.mk (λ x => (x,x)) (property := sorry)


-- Smoothness of SmoothMap.val
instance SmoothMap.val.arg_x.isSmooth {X Y} [Vec X] [Vec Y] (f : X ⟿ Y)
  : IsSmooth f.1 := f.2
instance SmoothMap.val.arg_fx.isSmooth {X Y} [Vec X] [Vec Y]
  : IsSmooth2 (λ (f : X⟿Y) (x : X) => f x) := IsSmooth2.mk (toIsSmooth := 
by 
    have h : (λ ((f,x) : (X⟿Y)×X) => f x) = uncurry id := by simp[uncurry,id]
    rw[h]; infer_instance)

-- Lambda notation
open Lean.TSyntax.Compat in
macro "λ"   xs:Lean.explicitBinders " ⟿ " b:term : term =>
  Lean.expandExplicitBinders `SciLean.SmoothMap.mk xs b


--------------------------------------------------------------------------------
-- Expressing IsSmooth2 in terms of IsSmooth
--------------------------------------------------------------------------------

instance IsSmooth_curry (f : X → Y → Z)
  [∀ x, IsSmooth (f x)] [IsSmooth λ x => λ y ⟿ f x y]
  : IsSmooth2 f := IsSmooth2.mk (toIsSmooth := 
by   
  have h : (λ (x,y) => f x y) = uncurry (λ x y ⟿ f x y) := by simp[uncurry]
  rw[h]; infer_instance)
  

instance IsSmooth_uncurry_y (f : X → Y → Z) [IsSmooth2 f] (x : X)
  : IsSmooth (λ y => f x y) := 
by
  let g := SmoothMap.mk λ (x,y) => f x y
  have h : (λ y => f x y) = curry g x := by simp[curry]
  rw[h]; infer_instance

instance IsSmooth_uncurry_x (f : X → Y → Z) [IsSmooth2 f]
  : IsSmooth (λ x => λ y ⟿ f x y) := 
by
  let g := SmoothMap.mk λ (x,y) => f x y
  have h : (λ x => λ y ⟿ f x y) = curry g := by simp[curry]
  rw[h]; infer_instance


instance IsSmooth3_curry (f : X → Y → Z → W)
  [∀ x y, IsSmooth (λ z => f x y z)] [∀ x, IsSmooth λ y => λ z ⟿ f x y z] [IsSmooth λ x => λ y z ⟿ f x y z]
  : IsSmooth3 f := IsSmooth3.mk (toIsSmooth := sorry)

instance IsSmooth3_uncurry_z (f : X → Y → Z → W) [IsSmooth3 f] (x : X) (y : Y)
  : IsSmooth (λ z => f x y z) := by (try infer_instance); admit
instance IsSmooth3_uncurry_y (f : X → Y → Z → W) [IsSmooth3 f] (x : X)
  : IsSmooth (λ y => λ z ⟿ f x y z) := by (try infer_instance); admit
instance IsSmooth3_uncurry_x (f : X → Y → Z → W) [IsSmooth3 f]
  : IsSmooth (λ x => λ y z ⟿ f x y z) := by (try infer_instance); admit

--------------------------------------------------------------------------------
-- Lambda calculus rules for IsSmooth
--------------------------------------------------------------------------------

-- Core I,K,S,C,C' rules for IsSmooth
instance IsSmooth_rule_I : IsSmooth (λ x : X => x) := id.property

instance IsSmooth_rule_K₂ (x : X) : IsSmooth (λ _ : Y => x) := 
by
  have h : (λ _ : Y => x) = curry fst x := by simp[curry,fst]
  rw[h]; infer_instance

instance IsSmooth_rule_K₁ : IsSmooth (λ (x : X) => λ (_ : Y) ⟿ x) := 
by
  have h : (λ (x : X) => λ (_ : Y) ⟿ x) = curry fst := by simp[curry,fst]
  rw[h]; infer_instance

instance IsSmooth_rule_S₃ (f : X → Y → Z) (g : X → Y) [IsSmooth2 f] [IsSmooth g]
  : IsSmooth (λ x => f x (g x)) := 
by
  have h : (λ x => f x (g x)) = comp (uncurry (λ x y ⟿ f x y)) (prodMap id (λ x ⟿ g x)) := by simp[comp, uncurry, prodMap, id]
  rw[h]; infer_instance

instance IsSmooth_rule_S₂ (f : X → Y → Z) [IsSmooth2 f] 
  (g : V → (X → Y)) [IsSmooth2 g]
  : IsSmooth (λ v => λ x ⟿ f x (g v x)) := 
by
  let f' := uncurry (λ x y ⟿ f x y)
  let g' := prodMap snd (uncurry (λ v x ⟿ g v x))
  have h : (λ v => λ x ⟿ f x (g v x)) = curry (comp f' g') := by simp[comp,curry,uncurry,prodMap,fst,snd]
  rw[h]; infer_instance

instance IsSmooth_rule_S₁ (f : U → (X → Y → Z)) [IsSmooth3 f] 
  (g : V → (X → Y)) [IsSmooth2 g]
  : IsSmooth (λ u => λ v x ⟿ f u x (g v x)) := 
by
  let f' := uncurry (comp uncurry (λ u x y ⟿ f u x y))
  let g' := prodMap (fst (X:=U)) (prodMap (comp snd snd) (comp (uncurry (λ v x ⟿ g v x)) snd))
  have h : (λ u => λ v x ⟿ f u x (g v x)) = comp curry (curry (comp f' g')) := by simp[comp,curry,uncurry,prodMap,fst,snd]
  rw[h]; infer_instance


instance IsSmooth_rule_C₂ (f : α → X → Y) [∀ a, IsSmooth (f a)]
  : IsSmooth λ x a => f a x := 
by
  have h : (λ x a => f a x) = comp (forallMap (λ a => λ x ⟿ f a x)) const := by simp[comp, forallMap, const]
  rw[h]; infer_instance

instance IsSmooth_rule_C₁.unif_hint (f : U → α → X → Y) [∀ a, IsSmooth2 (λ u x => f u a x)] (a : α) (u : U)
  : IsSmooth (λ x => f u a x) := 
by 
  try infer_instance
  have := IsSmooth_uncurry_y (λ u x => f u a x)
  infer_instance

instance IsSmooth_rule_C₁ (f : U → α → X → Y) [∀ a, IsSmooth2 (λ u x => f u a x)]
  : IsSmooth λ u => λ x ⟿ λ a => f u a x :=
by
  have h : (λ u => λ x ⟿ λ a => f u a x) 
           =
           curry (λ xy ⟿ λ a => uncurry (λ u x ⟿ f u a x) xy)
         := by simp[curry,uncurry]
  rw[h]; infer_instance
 
instance IsSmooth_rule_C'₂ (f : X → α → Y) [IsSmooth f] (a : α)
  : IsSmooth λ x => f x a :=
by
  have h : (λ x => f x a) = comp (eval a) (λ x ⟿ f x) := by simp[comp,eval]
  rw[h]; infer_instance

instance IsSmooth_rule_C'₁ (f : U → X → α → Y) [IsSmooth2 f] (a : α)
  : IsSmooth λ u => λ x ⟿ f u x a :=
by
  have h : (λ u => λ x ⟿ f u x a) 
           = 
           curry (λ xy ⟿ uncurry (λ u x ⟿ f u x) xy a) 
         := by simp[curry, uncurry]
  rw[h]; infer_instance



--------------------------------------------------------------------------------


instance IsSmooth_uncurry_S (f : X → Y → W → Z) [IsSmooth3 f]
  (g : X → Y → W) [IsSmooth2 g]
  : IsSmooth (λ x => λ y ⟿ f x y (g x y)) := by (try infer_instance); admit


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
