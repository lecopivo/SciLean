--- these will be hopefully defined in mathlib
import SciLean.Algebra

--   ___           _    _           _
--  / __|___ _ __ | |__(_)_ _  __ _| |_ ___ _ _ ___
-- | (__/ _ \ '  \| '_ \ | ' \/ _` |  _/ _ \ '_(_-<
--  \___\___/_|_|_|_.__/_|_||_\__,_|\__\___/_| /__/

section Combinators

   variable {X : Type u}

   def const (Y : Type v) (x : X) (y : Y) := x

   variable {Y : Type v} {Z : Type w}

   def comp (f : Y→Z) (g : X→Y) (x : X) := f (g x)
   def swap (f : X→Y→Z) (y : Y) (x : X) := f x y
   def subs (f : X→Y→Z) (g : X→Y) (x : X) := (f x) (g x)

   @[simp] def const.reduce (Y : Type v) (x : X) (y : Y) : const Y x y = x  := by simp[const]
   @[simp] def comp.reduce (f : Y→Z) (g : X→Y) (x : X) : (comp f g x) = f (g x) := by simp[comp]
   @[simp] def swap.reduce (f : X→Y→Z) (y : Y) (x : X) : (swap f y x) = f x y := by simp[swap]
   @[simp] def subs.reduce (f : X→Y→Z) (g : X→Y) (x : X) : (subs f g x) = (f x) (g x) := by simp[subs]

   -- Reduction of basic combinators in Type Class resolution for proof automation
   class FetchProof {α} (P : α → Prop) (a : α) where
      (fetch_proof : P a)

   instance (P : X → Prop) (x : X) [FetchProof P x] : P (id x) := by simp; apply FetchProof.fetch_proof
   instance (P : X → Prop) (x : X) (y : Y) [FetchProof P x] : P (const Y x y) := by simp; apply FetchProof.fetch_proof
   instance (P : Z → Prop) (f : X → Y → Z) (x : X) (y : Y) [FetchProof P (f x y)] : P (swap f y x) := by simp; apply FetchProof.fetch_proof
   instance (P : Z → Prop) (f : Y → Z) (g : X → Y) (x : X) [FetchProof P (f (g x))] : P (comp f g x) := by simp; apply FetchProof.fetch_proof
   instance (P : Z → Prop) (f : X → Y → Z) (g : X → Y) (x : X) [FetchProof P ((f x) (g x))] : P (subs f g x) := by simp; apply FetchProof.fetch_proof

   abbrev curry (f : X × Y → Z) (x : X) (y : Y) : Z := f (x,y)
   abbrev uncurry (f : X → Y → Z) (p : X×Y) : Z := f p.1 p.2

end Combinators

--  ___                 _   _ _    _
-- |_ _|_ ___ _____ _ _| |_(_) |__| |___
--  | || ' \ V / -_) '_|  _| | '_ \ / -_)
-- |___|_||_\_/\___|_|  \__|_|_.__/_\___|
class IsInv {X Y} (f : X → Y) : Prop := 
  (inj : ∀ x y, f x = f y → x = y)
  (surj : ∀ y, ∃ x, f x = y)

instance {X Y} (f : X → Y) [IsInv f] : FetchProof IsInv f := by constructor; assumption

def inverse {U V} : (U → V) → (V → U) := sorry
postfix:1024 "⁻¹" => inverse

axiom inverse.definition {U V} (f : U → V) (u : U) (v : V) [IsInv f] : f u = v → f⁻¹ v = u

--  _    _
-- | |  (_)_ _  ___ __ _ _ _
-- | |__| | ' \/ -_) _` | '_|
-- |____|_|_||_\___\__,_|_|
class IsLin {U V} [Vec U] [Vec V] (f : U → V)  : Prop :=
  ( add : ∀ x y, f (x + y) = f x + f y )
  ( mul : ∀ (s : ℝ) x, f (s*x) = s * (f x) )

instance {X Y} (f : X → Y) [Vec X] [Vec Y] [IsLin f] : FetchProof IsLin f := by constructor; assumption

def dual {U} [Hilbert U] := (Inner.inner : U → U → ℝ)⁻¹
def pullback {U V} (f : U → V) : (V → ℝ) → (U → ℝ) := λ v' u => v' (f u)
def adjoint {U V} (f : U → V) [Hilbert U] [Hilbert V] := dual ∘ (pullback f) ∘ inner

prefix:1024 "†" => adjoint


--    _    __  __ _
--   /_\  / _|/ _(_)_ _  ___
--  / _ \|  _|  _| | ' \/ -_)
-- /_/ \_\_| |_| |_|_||_\___|

class IsAff {U V} [Vec U] [Vec V] (f : U → V) : Prop := (is_affine : IsLin (f - const U (f 0)))

instance {X Y} (f : X → Y) [Vec X] [Vec Y] [IsAff f] : FetchProof IsAff f := by constructor; assumption

--  ___                _   _
-- / __|_ __  ___  ___| |_| |_
-- \__ \ '  \/ _ \/ _ \  _| ' \
-- |___/_|_|_\___/\___/\__|_||_|

--- We need formalization of Convenient Vector Spaces: https://en.wikipedia.org/wiki/Convenient_vector_space
def convenient.is_diff_at {X Y} (f : X → Y) (x : X) [Vec X] [Vec Y] : Prop := sorry  -- conveniently differentiable function
def convenient.differential {X Y} (f : X → Y) [Vec X] [Vec Y] (h : ∀ x, convenient.is_diff_at f x) : (X → X → Y) := sorry

class IsDiff {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := (is_diff : ∀ x, convenient.is_diff_at f x)

instance {X Y} (f : X → Y) [Vec X] [Vec Y] [IsDiff f] : FetchProof IsDiff f := by constructor; assumption

def differential {X Y} (f : X → Y) [Vec X] [Vec Y] : (X → X → Y) := sorry
prefix:1024 "δ" => differential

axiom differential.definition {X Y} (f : X → Y) [Vec X] [Vec Y] [IsDiff f] : δ f = convenient.differential f IsDiff.is_diff

@[simp] def derivative {X}   (f : ℝ → X) [Vec X] : ℝ → X := swap (δ f) 1
@[simp] def gradient {X} (f : X → ℝ) [Hilbert X] : X → X := comp dual (δ f)
@[simp] def tangent_map {X Y} (f : X → Y) [Vec X] [Vec Y] : X×X → Y×Y := uncurry $ λ x dx => (f x, δ f x dx)
@[simp] def backprop {X Y} (f : X → Y) [Hilbert X] [Hilbert Y] : X → Y×(Y→X) := λ x => (f x, †(δ f x))

prefix:1024 "∇" => gradient
prefix:1024 "ⅆ" => derivative
prefix:1024 "𝕋" => tangent_map


--   ___         _   _
--  / __|___ _ _| |_(_)_ _ _  _ ___ _  _ ___
-- | (__/ _ \ ' \  _| | ' \ || / _ \ || (_-<
--  \___\___/_||_\__|_|_||_\_,_\___/\_,_/__/
--- Define continuity. This is probably continouity w.r.t. to locally convex topology on Vec (note: Vec will be Convenient Vector Space)
def is_cont_at {X Y} [Vec X] [Vec Y] (f : X → Y) (x : X) : Prop := sorry  

class IsCont {U V} [Vec U] [Vec V] (f : U → V) : Prop := (is_cont : ∀ x, is_cont_at f x)

instance {X Y} (f : X → Y) [Vec X] [Vec Y] [IsCont f] : FetchProof IsCont f := by constructor; assumption

--  ___      ____
-- |_ _|___ |_  /___ _ _ ___
--  | |(_-<  / // -_) '_/ _ \
-- |___/__/ /___\___|_| \___/

class IsZero {X} [Vec X] (x : X) : Prop := (is_zero : x = 0)

instance {X} [Vec X] (x : X) [IsZero x] : FetchProof IsZero x := by constructor; assumption

--  _  _          ____
-- | \| |___ _ _ |_  /___ _ _ ___
-- | .` / _ \ ' \ / // -_) '_/ _ \
-- |_|\_\___/_||_/___\___|_| \___/

class NonZero {X} [Vec X] (x : X) : Prop := (non_zero : x ≠ 0)

instance {X} [Vec X] (x : X) [NonZero x] : FetchProof NonZero x := by constructor; assumption

--  _    _       _ _
-- | |  (_)_ __ (_) |_
-- | |__| | '  \| |  _|
-- |____|_|_|_|_|_|\__|

def has_limit {X} (lim : Nat → X) [Vec X] : Prop := sorry

class HasLim {X} [Vec X] (lim : Nat → X) : Prop := (has_lim : has_limit lim)

instance {X} [Vec X] (lim : Nat → X) [HasLim lim] : FetchProof HasLim lim := by constructor; assumption

def limit {X} (lim : Nat → X) [Vec X] : X := sorry


--   ___  ___  ___   ___      _
--  / _ \|   \| __| / __| ___| |_ _____
-- | (_) | |) | _|  \__ \/ _ \ \ V / -_)
--  \___/|___/|___| |___/\___/_|\_/\___|
def ode_solve {X} (f : X → X) (x₀ : X) (t : ℝ) [Vec X] : X := sorry

instance ode_solve.is_diff {X} (f : X → X) (x₀ : X) [Vec X] [IsCont f] : IsDiff (ode_solve f x₀) := sorry
@[simp] axiom ode_solve.definition {X} (f : X → X) (x₀ : X) (t dt : ℝ) [Vec X] [IsCont f] : δ (ode_solve f x₀) t dt = dt * f (ode_solve f x₀ t)

--  ___     _                     _
-- |_ _|_ _| |_ ___ __ _ _ _ __ _| |_ ___
--  | || ' \  _/ -_) _` | '_/ _` |  _/ -_)
-- |___|_||_\__\___\__, |_| \__,_|\__\___|
--                 |___/
def integrate {X} (f : ℝ → X) (a b : ℝ) [Vec X] : X := sorry

prefix:1024 "∫" => integrate

instance {X} (a : ℝ) (f : ℝ → X) [Vec X] [IsCont f] : IsDiff (∫ f a) := sorry
axiom integrate.swap_limit {X} (a b : ℝ) (f : ℝ → X) [Vec X] [IsCont f] : (∫ f a b = - ∫ f b a)
@[simp] axiom integrate.definition {X} (a t dt : ℝ) (f : ℝ → X) [Vec X] [IsCont f] : δ (∫ f a) t dt  = dt * (f t)


--    _            __  __ _
--   /_\  _ _ __ _|  \/  (_)_ _
--  / _ \| '_/ _` | |\/| | | ' \
-- /_/ \_\_| \__, |_|  |_|_|_||_|
--           |___/
def is_minimum {X} (f : X → ℝ) (x : X) : Prop := ∀ y, f x < f y
def is_unique_minimum {X} (f : X → ℝ) (x : X) : Prop := ∀ y, is_minimum f y → y = x
def has_unique_minimum {X} (f : X → ℝ) : Prop := ∃ x, is_unique_minimum f x

class HasArgMin {X} (f : X → ℝ) : Prop := (has_argmin : has_unique_minimum f)

instance {X} (f : X → ℝ) [HasArgMin f] : FetchProof HasArgMin f := by constructor; assumption

def argmin {X} (f : X → ℝ) : X := sorry

axiom argmin.definition {X} (f : X → ℝ) (x : X) [HasArgMin f] : x = argmin f → is_unique_minimum f x

