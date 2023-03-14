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
class IsSmooth3 {W X Y Z : Type} [Vec W] [Vec X] [Vec Y] [Vec Z] (f : W → X → Y → Z) extends IsSmooth λ (w,x,y) => f w x y


-- Differential
opaque differential (f : X → Y) : X → X → Y := sorry

prefix:max " ∂ " => differential


-- SmoothMap
structure SmoothMap (X Y) [Vec X] [Vec Y] where
  val : X → Y
  [property : IsSmooth val]

infix:25 " ⟿ " => SmoothMap

instance {X Y} [Vec X] [Vec Y] : Vec (X ⟿ Y) := sorry
instance {X Y} [Vec X] [Vec Y] : CoeFun (X ⟿ Y) (λ _ => X → Y) := ⟨λ f => f.val⟩

instance SmoothMap.val.arg_fx.isSmooth {X Y} [Vec X] [Vec Y]
  : IsSmooth2 (λ (f : X⟿Y) (x : X) => f x) := sorry


-- Lambda notation
open Lean.TSyntax.Compat in
macro "λ"   xs:Lean.explicitBinders " ⟿ " b:term : term =>
  Lean.expandExplicitBinders `SciLean.SmoothMap.mk xs b


variable {X Y Z W W'} [Vec X] [Vec Y] [Vec Z] [Vec W] [Vec W'] {α : Type}

--------------------------------------------------------------------------------
-- IsSmooth rules
--------------------------------------------------------------------------------

-- Core I,K,S,C,C' rules for IsSmooth
instance IsSmooth_rule_I : IsSmooth (λ x : X => x) := sorry
instance IsSmooth_rule_K (x : X) : IsSmooth (λ y : Y => x) := sorry
instance IsSmooth_rule_S (f : X → Y → Z) (g : X → Y) [IsSmooth2 f] [IsSmooth g]
  : IsSmooth (λ x => f x (g x)) := sorry

instance IsSmooth_rule_C  (f : α → X → Y) [∀ a, IsSmooth (f a)]
  : IsSmooth λ x a => f a x := sorry
instance IsSmooth_rule_C' (f : X → α → Y) [IsSmooth f] (a : α)
  : IsSmooth λ x => f x a := sorry

-- Curry and uncurry for IsSmooth
instance IsSmooth_curry (f : X → Y → Z)
  [∀ x, IsSmooth (f x)] [IsSmooth λ x => λ y ⟿ f x y]
  : IsSmooth2 f := IsSmooth2.mk (toIsSmooth := sorry)

instance IsSmooth_uncurry_y (f : X → Y → Z) [IsSmooth2 f] (x : X)
  : IsSmooth (λ y => f x y) := sorry
instance IsSmooth_uncurry_x (f : X → Y → Z) [IsSmooth2 f]
  : IsSmooth (λ x => λ y ⟿ f x y) := sorry

instance IsSmooth_uncurry_x_comp (f : X → Y → Z) [IsSmooth2 f]
  (g : W → X) [IsSmooth g]
  : IsSmooth (λ w => λ y ⟿ f (g w) y) := sorry
instance IsSmooth_uncurry_x_const (f : X → Z) [IsSmooth f] 
  : IsSmooth (λ (x : X) => λ (y : Y) ⟿ f x) := sorry

--------------------------------------------------------------------------------
-- Differential rules
--------------------------------------------------------------------------------

@[simp ↓]
theorem differential_rule_I
  : ∂ (λ x : X => x)
    =
    λ x dx => dx := sorry

@[simp ↓]
theorem differential_rule_K (x : X)
  : ∂ (λ y : Y => x)
    =
    λ y Y => 0 := sorry

@[simp ↓ low]
theorem differential_rule_S
  (f : X → Y → Z) (g : X → Y) [IsSmooth2 f] [IsSmooth g]
  : ∂ (λ x => f x (g x))
    =
    λ x dx =>
      ∂ f x dx (g x)
      +
      ∂ (f x) (g x) (∂ g x dx) := sorry

@[simp ↓ low-2]
theorem differential_rule_C (f : α → X → Y) [∀ a, IsSmooth (f a)]
  : ∂ (λ x a => f a x)
    =
    λ x dx a => ∂ (f a) x dx := sorry

@[simp ↓ low-1]
theorem differential_rule_C' (f : X → α → Y) [IsSmooth f] (a : α)
  : ∂ (λ x => f x a)
    =
    λ x dx => ∂ f x dx a := sorry



-- Some basic properties of addition, multiplication and zero
instance : IsSmooth2 (λ x y : X => x + y) := sorry
@[simp] theorem HAdd.hAdd.arg_x.diff_simp : ∂ (λ x y : X => x + y) = λ x dx y => dx := sorry
@[simp] theorem HAdd.hAdd.arg_y.diff_simp (x : X) : ∂ (λ y : X => x + y) = λ y dy => dy := sorry

instance : IsSmooth2 (λ (x : ℝ) (y : X) => x * y) := sorry
@[simp] theorem HMul.hMul.arg_x.diff_simp : ∂ (λ (x : ℝ) (y : X) => x * y) = λ x dx y => dx * y := sorry
@[simp] theorem HMul.hMul.arg_y.diff_simp (x : ℝ) : ∂ (λ y : X => x * y) = λ y dy : X => x * dy := sorry


@[simp] theorem add_zero (x : X) : x + 0 = x := sorry
@[simp] theorem zero_add (x : X) : 0 + x = x := sorry
@[simp] theorem mul_zero (x : X) : (0:ℝ) * x = (0:X) := sorry

@[simp] theorem zero_app (a : α) : (0 : α → X) a = (0 : X) := sorry
@[simp] theorem differential_zero (f : X → Y) [IsSmooth f] (x : X): ∂ f x 0 = 0 := sorry


@[simp high] -- prefer this over S rule
theorem chain_rule
  (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
  : ∂ (λ x => f (g x))
    =
    λ x dx => ∂ f (g x) (∂ g x dx) := by simp

@[simp high] -- prefer this over S rule
theorem binop_chain_rule {Y₁ Y₂} [Vec Y₁] [Vec Y₂]
  (f : Y₁ → Y₂ → Z) [IsSmooth2 f] 
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : ∂ (λ x => f (g₁ x) (g₂ x))
    =
    λ x dx => 
      ∂ f (g₁ x) (∂ g₁ x dx) (g₂ x)
      +
      ∂ (f (g₁ x)) (g₂ x) (∂ g₂ x dx) := 
by 
  funext x dx
  rw[differential_rule_S (λ x y => f (g₁ x) y) g₂]; dsimp
  rw[differential_rule_C]; dsimp
  rw[differential_rule_S (λ _ x' => f x' (g₂ x)) g₁]
  simp
  done


--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

namespace maintests

  variable {α β γ : Type}

  variable (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] (h : X → X) [IsSmooth h] (h' : Y → Y) [IsSmooth h']
  variable (a : α) (b : β)
  variable (F : Y → α → X) [IsSmooth F]
  variable (G : X → α → β → Y) [IsSmooth G]
  variable (G' : X → Z → W → Y) (z : Z) (w : W) [IsSmooth G']
  variable (H : α → X → β → Y) [IsSmooth (H a)]
  variable (H': α → β → X → Y) [IsSmooth (H' a b)]

  example : IsSmooth (λ x => g x) := by infer_instance
  example : IsSmooth (λ x => f (g x)) := by infer_instance
  example : IsSmooth (λ x => f (g (h (h x)))) := by infer_instance
  example : IsSmooth (λ (g' : X → Y) => f ∘ g') := by unfold Function.comp; infer_instance
  example : IsSmooth (λ (x : X) => F (g (h x)) a) := by infer_instance
  example : IsSmooth (f ∘ g) := by unfold Function.comp; infer_instance
  example : IsSmooth (λ (f : Y → Z) (x : X) => (f (g x))) := by infer_instance
  example : IsSmooth (λ (h'' : X → X) (x : X) => h (h (h (h'' ((h ∘ h) (h x)))))) := by infer_instance
  example : IsSmooth (λ (x : X) => G (h x) a b) := by infer_instance
  example : IsSmooth (λ (x : X) => H a (h x) b) := by infer_instance
  example : IsSmooth (λ (x : X) => H' a b (h x)) := by infer_instance
  example (f : β → Y → Z) [∀ b, IsSmooth (f b)] : IsSmooth (λ (g : α → Y) (b : β) (a : α) => f b (g a)) := by infer_instance
  example (f : X → X → Y) [IsSmooth2 f]: IsSmooth (λ x => f x x) := by infer_instance
  example (f : X → X → Y) [IsSmooth2 f]: IsSmooth (λ x => f (h x) x) := by infer_instance
  example (f : X → X → Y) [IsSmooth2 f] : IsSmooth (λ x => f x (h x)) := by infer_instance
  example : IsSmooth (λ (h : X → X) (x : X) => H' a b (h x)) := by infer_instance
  example (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] : IsSmooth (f ∘ g) := by unfold Function.comp; infer_instance
  example (g : α → β) : IsSmooth (λ (f : β → Z) (a : α) => (f (g a))) := by infer_instance
  example (f : Y → β → Z) (g : X → Y) (b : β) [IsSmooth f] [IsSmooth g] : IsSmooth (λ x => f (g x) d) := by infer_instance
  example (f : Y → β → Z) (g : X → Y) (h : X → X) (b : β) [IsSmooth f] [IsSmooth g] [IsSmooth h] : IsSmooth (λ x => f (g (h (h x))) d) := by infer_instance
  example (f : α → Y → Z) [∀ a, IsSmooth (f a)] : IsSmooth (λ y a => f a y) := by infer_instance
  example (f : α → β → X → Y) [∀ a b, IsSmooth (f a b)] : IsSmooth (λ x b a => f a b x) := by infer_instance
  example (f : α → β → X → Y) [∀ a b, IsSmooth (f a b)] : IsSmooth (λ x a b => f a b x) := by infer_instance
  example (f : α → β → γ → X → Y) [∀ a b c, IsSmooth (f a b c)] : IsSmooth (λ x a b c => f a b c x) := by infer_instance
  example (f : X → X) [IsSmooth f] : IsSmooth (λ (g : X → X) x => f (f (g x))) := by infer_instance
  example (f : X → X → β → Y) [IsSmooth2 f] : IsSmooth (λ x b => f x x b) := by infer_instance
  example : IsSmooth (λ (g : X → Y) (x : X) => F (g (h x)) a) := by infer_instance
  example : IsSmooth (λ (x : X) => G' (h x) z w) := by infer_instance
  example (f : X → X → β → Y) [IsSmooth2 f]  (b) : IsSmooth (λ x => f x x b) := by infer_instance
  example : IsSmooth (λ (h : X → X) (x : X) => G (h x)) := by infer_instance

  example : IsSmooth (λ (h : X → X) (x : X) => G (h x) a b) := by infer_instance
  example : IsSmooth (λ (h : X → X) (x : X) => H a (h x) b) := by infer_instance
  example : IsSmooth (λ (x : X) => h (F (h' ((h' ∘ g) (h x))) a)) := by unfold Function.comp; infer_instance
  set_option synthInstance.maxSize 200 in
  example : IsSmooth (λ (h'' : X → X) (x : X) => (h ∘ h ∘ h) (h (h'' (h ((h ∘ h) x))))) := by unfold Function.comp; infer_instance

end maintests


namespace foldtest

variable {α β γ : Type} 
variable {X : Type} {Y : Type} {Z : Type} [Vec X] [Vec Y] [Vec Z]

variable (f : X → X) [IsSmooth f]


example : IsSmooth (λ x => f x) := by infer_instance
example : IsSmooth (λ x => x |> f) := by infer_instance
example : IsSmooth (λ x => x |> f |> f) := by infer_instance
example : IsSmooth (λ (g : X → X) x => f (g x)) := by infer_instance
example : IsSmooth (λ (g : X → X) x => g (f x)) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> g) := by infer_instance
example : IsSmooth (λ (g : X → X) x => f (f (g x))) := by infer_instance
example : IsSmooth (λ (g : X → X) x => f (g (f x))) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> g |> f) := by infer_instance
example : IsSmooth (λ (g : X → X)  x => g (f (f x))) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> f |> g) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> f |> g |> g) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> g |> g) := by infer_instance
example : IsSmooth (λ (g : X → X)  x => x |> g |> f |> f |> f) := by infer_instance
example : IsSmooth (λ (g : X → X)  x => x |> f |> g |> f |> f) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> g |> f |> f) := by infer_instance
example : IsSmooth (λ (g : X → X)  x => x |> f |> f |> g |> f) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> f |> g |> f) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> f |> g |> g |> f) := by infer_instance
example : IsSmooth (λ (g : X ⟿ X) x => x |> g |> g |> g |> f) := by infer_instance
example : IsSmooth (λ (g : X → X)  x => x |> f |> f |> f |> g) := by infer_instance

end foldtest


section differentiation_tests

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]


example (f : Y → Z) [IsSmooth f] (g : X → Y) [IsSmooth g]
  : ∂ (λ x => f (g x)) = λ x dx => ∂ f (g x) (∂ g x dx) := by simp


example (a : α) (f : Y → α → Z) [IsSmooth f] (g : X → Y) [IsSmooth g]
  : ∂ (λ x => f (g x) a) = λ x dx => ∂ f (g x) (∂ g x dx) a := by simp

example (f : Y → Z) [IsSmooth f]
  : ∂ (λ (g : α → Y) (a : α) => f (g a)) = λ g dg a => ∂ f (g a) (dg a) := by simp

example
  : ∂ (λ (f : β → Z) (g : α → β) (a : α) => f (g a)) = λ f df (g : α → β) a => df (g a) := by simp

example (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] (b) 
  : ∂ (λ x => f (g x) b) = λ x dx => ∂ f (g x) (∂ g x dx) b := by simp

example (f : Y → β → Z) [IsSmooth f] (b)
  : ∂ (λ (g : α → Y) a => f (g a) b) = λ g dg a => ∂ f (g a) (dg a) b := by simp

example (f : β → Y → Z) (g : β → X → Y) [∀ b, IsSmooth (f b)] [∀ b, IsSmooth (g b)]
  : ∂ (λ x b => f b (g b x)) = λ x dx b => ∂ (f b) (g b x) (∂ (g b) x dx) := by simp

example (f : Y → β → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
  : ∂ (λ x b => f (g x) b) = λ x dx b => ∂ f (g x) (∂ g x dx) b := by simp

set_option synthInstance.maxSize 300 in
example (f : Y → β → Z) [IsSmooth f]
  : ∂ (λ (g : α → Y) a b => f (g a) b) = λ g dg a b => ∂ f (g a) (dg a) b := by simp

example (f : Y₁ → β2 → Z) (g2 : α → β2) [IsSmooth f] (g dg)
  : ∂ (λ  (g1 : α → Y₁) a => f (g1 a) (g2 a)) g dg = λ a => ∂ f (g a) (dg a) (g2 a) := by simp

example (f : β1 → Y₂ → Z) (g1 : α → β1) [∀ y1, IsSmooth (f y1)] 
  : ∂ (λ (g2 : α → Y₂) a => f (g1 a) (g2 a)) = λ g dg a => ∂ (f (g1 a)) (g a) (dg a) := by simp


variable (f : Y → Z) [IsSmooth f]
variable (g : X → Y) [IsSmooth g]
variable (f1 : X → X) [IsSmooth f1]
variable (f2 : Y → Y) [IsSmooth f2]
variable (f3 : Z → Z) [IsSmooth f3]
variable (F : X → Y → Z) [IsSmooth2 F]
variable (G : X × Y → Z) [IsSmooth G]

variable (x dx : X) (y dy : Y) (z dz : Z)

example : ∂ (λ x => f (g (f1 x))) x dx = ∂ f (g (f1 x)) (∂ g (f1 x) (∂ f1 x dx)) := by simp

example : ∂ (λ (x : X) => F x (g x)) x dx = ∂ F x dx (g x) + ∂ (F x) (g x) (∂ g x dx) := by simp
example : ∂ (λ (x : X) => f3 (F x (g x))) x dx = ∂ f3 (F x (g x)) (∂ F x dx (g x) + ∂ (F x) (g x) (∂ g x dx)) := by simp
example g dg x : ∂ (λ (g : X → Y) => f (g x)) g dg = ∂ f (g x) (dg x) := by simp
example g dg x : ∂ (λ (g : X → Y) (x : X) => F x (g x)) g dg x = ∂ (F x) (g x) (dg x) := by simp


-- The following tests rely on `binop_chain_rule`

example g dg x : ∂ (λ (g : X → X) (y : Y) => F (g x) y) g dg y = ∂ F (g x) (dg x) y := by simp
example g dg y : ∂ (λ (g : X → X) (x : X) => F (g x) y) g dg x = ∂ F (g x) (dg x) y := by simp

example (r dr : ℝ) : ∂ (λ x : ℝ => x*x) r dr = dr * r + r * dr := by simp
example (r dr : ℝ) : ∂ (λ x : ℝ => x*x + x) r dr = dr * r + r * dr + dr := by simp
example (r dr : ℝ) : ∂ (λ x : ℝ => x*x*x + x) r dr = (dr * r + r * dr) * r + r * r * dr + dr := by simp

example (f : X → α → Y) [IsSmooth f] (a : α) (y : Y)
  : ∂ (fun (x : X) => (f x a) + y)
    =
    λ x dx => ∂ f x dx a := by simp

example (f g : X → α → Y) [IsSmooth f] [IsSmooth g]
  : ∂ (λ x a => f x a + g x a) 
    =
    λ x dx a => ∂ f x dx a + ∂ g x dx a := by simp

end differentiation_tests
