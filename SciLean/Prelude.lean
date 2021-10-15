--- these will be hopefully defined in mathlib
import SciLean.Algebra
import SciLean.Meta

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
   @[simp] def subs.reduce (f : X→Y→Z) (g : X→Y) (x : X) : (subs f g x) = let x' := x; (f x') (g x') := by simp[subs]

   -- Reduction of basic combinators in Type Class resolution 
   -- This is crucial in proof automation
   class FetchProof {α} (P : α → Prop) (a : α) where
      (fetch_proof : P a)

   instance (P : X → Prop) (x : X) [FetchProof P x] : P (id x) := by simp; apply FetchProof.fetch_proof
   instance (P : X → Prop) (x : X) (y : Y) [FetchProof P x] : P (const Y x y) := by simp; apply FetchProof.fetch_proof
   instance (P : Z → Prop) (f : X → Y → Z) (x : X) (y : Y) [FetchProof P (f x y)] : P (swap f y x) := by simp; apply FetchProof.fetch_proof
   instance (P : Z → Prop) (f : Y → Z) (g : X → Y) (x : X) [FetchProof P (f (g x))] : P (comp f g x) := by simp; apply FetchProof.fetch_proof
   instance (P : Z → Prop) (f : X → Y → Z) (g : X → Y) (x : X) [FetchProof P ((f x) (g x))] : P (subs f g x) := by simp; apply FetchProof.fetch_proof

   -- Extra arguments reduction -- is this enough?
   variable {α : Type _}
   instance (P : Z → Prop) (f : X → Y → α → Z) (x : X) (y : Y) (a : α) [FetchProof P (f x y a)] : P (swap f y x a) := by simp; apply FetchProof.fetch_proof
   instance (P : Z → Prop) (f : Y → α → Z) (g : X → Y) (x : X) (a : α) [FetchProof P (f (g x) a)] : P (comp f g x a) := by simp; apply FetchProof.fetch_proof
   instance (P : Z → Prop) (f : X → Y → α → Z) (g : X → Y) (x : X) (a : α) [FetchProof P ((f x) (g x) a)] : P (subs f g x a) := by simp; apply FetchProof.fetch_proof



   abbrev curry (f : X × Y → Z) (x : X) (y : Y) : Z := f (x,y)
   abbrev uncurry (f : X → Y → Z) (p : X×Y) : Z := f p.1 p.2

end Combinators

infixr:90 " • "  => comp

--  ___                 _   _ _    _
-- |_ _|_ ___ _____ _ _| |_(_) |__| |___
--  | || ' \ V / -_) '_|  _| | '_ \ / -_)
-- |___|_||_\_/\___|_|  \__|_|_.__/_\___|
-- Implementing this as `class IsInv f extends IsLInv f, IsRInv f` would break proof automation.
-- We want to automatize `IsInv f → IsRInv f` and `IsInv f → IsLInv f`
-- Adding automatization for `IsRInv f ∧ IsLinv f → IsInv f` would likely cause an infinite loop in type class resolution
class IsInv {X Y} (f : X → Y) : Prop := 
  (inj : ∀ x y, f x = f y → x = y)
  (surj : ∀ y, ∃ x, f x = y)

instance {X Y} (f : X → Y) [IsInv f] : FetchProof IsInv f := by constructor; assumption

--  ___ _      _   _     ___                 _   _ _    _
-- | _ (_)__ _| |_| |_  |_ _|_ ___ _____ _ _| |_(_) |__| |___
-- |   / / _` | ' \  _|  | || ' \ V / -_) '_|  _| | '_ \ / -_)
-- |_|_\_\__, |_||_\__| |___|_||_\_/\___|_|  \__|_|_.__/_\___|
--       |___/
class IsRInv {X Y} (f : X → Y) : Prop := 
  (surj : ∀ y, ∃ x, f x = y)

instance {X Y} (f : X → Y) [IsRInv f] : FetchProof IsRInv f := by constructor; assumption

--  _         __ _     ___                 _   _ _    _
-- | |   ___ / _| |_  |_ _|_ ___ _____ _ _| |_(_) |__| |___
-- | |__/ -_)  _|  _|  | || ' \ V / -_) '_|  _| | '_ \ / -_)
-- |____\___|_|  \__| |___|_||_\_/\___|_|  \__|_|_.__/_\___|
class IsLInv {X Y} (f : X → Y) : Prop := 
  (inj : ∀ x y, f x = f y → x = y)

instance {X Y} (f : X → Y) [IsLInv f] : FetchProof IsLInv f := by constructor; assumption

--  _    _
-- | |  (_)_ _  ___ __ _ _ _
-- | |__| | ' \/ -_) _` | '_|
-- |____|_|_||_\___\__,_|_|
class IsLin {U V} [Vec U] [Vec V] (f : U → V) : Prop :=
  ( add : ∀ x y, f (x + y) = f x + f y )
  ( mul : ∀ (s : ℝ) x, f (s*x) = s * (f x) )

instance {X Y} [Vec X] [Vec Y] (f : X → Y) [IsLin f] : FetchProof IsLin f := by constructor; assumption

--  ___                _   _
-- / __|_ __  ___  ___| |_| |_
-- \__ \ '  \/ _ \/ _ \  _| ' \
-- |___/_|_|_\___/\___/\__|_||_|
--- We need formalization of Convenient Vector Spaces: https://en.wikipedia.org/wiki/Convenient_vector_space
def convenient.is_smooth {X Y} (f : X → Y) [Vec X] [Vec Y] : Prop := sorry  -- conveniently differentiable function

class IsSmooth {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := (is_diff : convenient.is_smooth f)

instance {X Y} (f : X → Y) [Vec X] [Vec Y] [IsSmooth f] : FetchProof IsSmooth f := by constructor; assumption

def SmoothMap (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsSmooth f }

--  ___  _  __  __                 _   _      _    _
-- |   \(_)/ _|/ _|___ _ _ ___ _ _| |_(_)__ _| |__| |___
-- | |) | |  _|  _/ -_) '_/ -_) ' \  _| / _` | '_ \ / -_)
-- |___/|_|_| |_| \___|_| \___|_||_\__|_\__,_|_.__/_\___|
-- Only one time differentiable functions
--- We need formalization of Convenient Vector Spaces: https://en.wikipedia.org/wiki/Convenient_vector_space
def convenient.is_diff_at {X Y} (f : X → Y) (x : X) [Vec X] [Vec Y] : Prop := sorry  -- conveniently differentiable function

class IsDiff {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := (is_diff : ∀ x, convenient.is_diff_at f x)

instance {X Y} (f : X → Y) [Vec X] [Vec Y] [IsDiff f] : FetchProof IsDiff f := by constructor; assumption

def DiffMap (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsDiff f }

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

--  ___        _ _   _
-- | _ \___ __(_) |_(_)_ _____
-- |  _/ _ (_-< |  _| \ V / -_)
-- |_| \___/__/_|\__|_|\_/\___|

class IsPos (x : ℝ) : Prop := (is_positive : x > 0)

instance (x : ℝ) [IsPos x] : FetchProof IsPos x := by constructor; assumption

--   ___                             ___             _   _
--  / _ \ _ __  __ _ __ _ _  _ ___  | __|  _ _ _  __| |_(_)___ _ _  ___
-- | (_) | '_ \/ _` / _` | || / -_) | _| || | ' \/ _|  _| / _ \ ' \(_-<
--  \___/| .__/\__,_\__, |\_,_\___| |_| \_,_|_||_\__|\__|_\___/_||_/__/
--       |_|           |_|

--  ___
-- |_ _|_ ___ _____ _ _ ___ ___
--  | || ' \ V / -_) '_(_-</ -_)
-- |___|_||_\_/\___|_| /__/\___|

-- add [Inhabited U]
def inverse {U V} : (U → V) → (V → U) := sorry
postfix:1024 "⁻¹" => inverse

axiom inverse.definition {U V} (f : U → V) (u : U) (v : V) [IsInv f] : (∀ u, f⁻¹ (f u) = u) ∧ (∀ v, f (f⁻¹ v) = v)

--  ___  _  __  __                 _   _      _
-- |   \(_)/ _|/ _|___ _ _ ___ _ _| |_(_)__ _| |
-- | |) | |  _|  _/ -_) '_/ -_) ' \  _| / _` | |
-- |___/|_|_| |_| \___|_| \___|_||_\__|_\__,_|_|

def differential {X Y} [Vec X] [Vec Y] (f : X → Y) : (X → X → Y) := sorry
prefix:1024 "δ" => differential

--- We need formalization of Convenient Vector Spaces: https://en.wikipedia.org/wiki/Convenient_vector_space
def convenient.differential {X Y} [Vec X] [Vec Y] (f : X → Y) (x dx : X) (h : convenient.is_diff_at f x) : Y := sorry
axiom differential.definition {X Y} [Vec X] [Vec Y] (f : X → Y) [IsDiff f] (x dx : X) : δ f x dx = convenient.differential f x dx (IsDiff.is_diff x)

--  _    _       _ _
-- | |  (_)_ __ (_) |_
-- | |__| | '  \| |  _|
-- |____|_|_|_|_|_|\__|

def has_limit {X} [Vec X] (lim : Nat → X) : Prop := sorry

def limit {X} [Vec X] (lim : Nat → X) : X := sorry

-- Maybe we will add this proof automation 
-- class HasLim {X} [Vec X] (lim : Nat → X) : Prop := (has_lim : has_limit lim)
-- instance {X} [Vec X] (lim : Nat → X) [HasLim lim] : FetchProof HasLim lim := by constructor; assumption

--   ___  ___  ___   ___      _
--  / _ \|   \| __| / __| ___| |_ _____
-- | (_) | |) | _|  \__ \/ _ \ \ V / -_)
--  \___/|___/|___| |___/\___/_|\_/\___|
def ode_solve {X} [Vec X] (f : X → X) (t : ℝ) (x₀ : X) : X := sorry

@[simp] axiom ode_solve.definition {X} [Vec X] (f : X → X) (t dt : ℝ) (x₀ : X) [IsCont f] : δ (ode_solve f) t dt x₀ = dt * f (ode_solve f t x₀)

--  ___     _                     _
-- |_ _|_ _| |_ ___ __ _ _ _ __ _| |_ ___
--  | || ' \  _/ -_) _` | '_/ _` |  _/ -_)
-- |___|_||_\__\___\__, |_| \__,_|\__\___|
--                 |___/
def integrate {X} [Vec X] (f : ℝ → X) (a b : ℝ) : X := sorry

prefix:1024 "∫" => integrate

axiom integrate.swap_limit {X} [Vec X] (a b : ℝ) (f : ℝ → X) [IsCont f] : (∫ f a b = - ∫ f b a)
@[simp] axiom integrate.definition {X} [Vec X] (a t dt : ℝ) (f : ℝ → X) [IsCont f] : δ (∫ f) a t dt = dt * (f t)

--  ___            _
-- |   \ _  _ __ _| |
-- | |) | || / _` | |
-- |___/ \_,_\__,_|_|

def dual {U} [Vec U] : (U → ℝ) → U := sorry

axiom dual.definition_hilbert {U} [Hilbert U] (f : U → ℝ) [IsLin f] : dual f = (inverse inner) f 

def dual' {U I} [Vec U] [Vec I] : (U → I) → U := sorry

axiom dual'.definition_hilbert {U} [Hilbert U] (u : U) : dual' (λ v => ⟨u, v⟩) = u
axiom dual'.definition_integral {U} [Hilbert U] (f : ℝ → U) [IsCont f] : dual' (λ (g : ℝ → U) => ∫ (λ t => ⟨f t, g t⟩)) = f

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


--  ___          _            _    ___                     _
-- |   \ ___ _ _(_)_ _____ __| |  / _ \ _ __  ___ _ _ __ _| |_ ___ _ _ ___
-- | |) / -_) '_| \ V / -_) _` | | (_) | '_ \/ -_) '_/ _` |  _/ _ \ '_(_-<
-- |___/\___|_| |_|\_/\___\__,_|  \___/| .__/\___|_| \__,_|\__\___/_| /__/
--                                     |_|
-- Usefull very common operators derived from opaque ones.
-- They deserve their own reduction rules 


--    _      _  _     _     _
--   /_\  __| |(_)___(_)_ _| |_
--  / _ \/ _` || / _ \ | ' \  _|
-- /_/ \_\__,_|/ \___/_|_||_\__|
--           |__/

def pullback {U V} (f : U → V) : (V → ℝ) → (U → ℝ) := λ v' u => v' (f u)
def adjoint {U V} [Hilbert U] [Hilbert V] (f : U → V) := dual ∘ (pullback f) ∘ inner

prefix:1024 "†" => adjoint

--   ___             _     _____                       _     __  __
--  / __|_ _ __ _ __| |   |_   _|_ _ _ _  __ _ ___ _ _| |_  |  \/  |__ _ _ __
-- | (_ | '_/ _` / _` |_    | |/ _` | ' \/ _` / -_) ' \  _| | |\/| / _` | '_ \_
--  \___|_| \__,_\__,_( )   |_|\__,_|_||_\__, \___|_||_\__| |_|  |_\__,_| .__( )
--                    |/                 |___/                          |_|  |/

@[simp] def derivative {X} [Vec X] (f : ℝ → X) : ℝ → X := swap (δ f) 1
def gradient {X} [Vec X] (f : X → ℝ) : X → X := comp dual (δ f)
def tangent_map {X Y} [Vec X] [Vec Y] (f : X → Y) : X×X → Y×Y := uncurry $ λ x dx => (f x, δ f x dx)
def backprop {X Y} [Hilbert X] [Hilbert Y] (f : X → Y) : X → Y×(Y→X) := λ x => (f x, †(δ f x))

prefix:1024 "∇" => gradient
prefix:1024 "ⅆ" => derivative
prefix:1024 "𝕋" => tangent_map
