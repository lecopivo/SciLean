import SciLean.Core.Defs

namespace SciLean

open SciLean.Mathlib.Convenient

--------------------------------------------------------------------------------

variable {α β : Type}
variable {X Y Z W U V: Type} [Vec X] [Vec Y] [Vec Z] [Vec W] [Vec U] [Vec V]
variable {Y₁ Y₂ Y₃ : Type} [Vec Y₁] [Vec Y₂] [Vec Y₃]

open Smooth

@[fun_prop_rule]
theorem IsSmooth.rule_id 
  : IsSmooth (λ x : X => x) := sorry


@[fun_prop_rule]
theorem IsSmooth.rule_const (x : X)
  : IsSmooth (λ y : Y => x) := sorry


@[fun_prop_rule]
theorem IsSmooth.rule_comp 
  (f : Y → Z) [IsSmooth f]
  (g : X → Y) [IsSmooth g]
  : IsSmooth (λ x => f (g x)) := sorry

@[fun_prop_rule]
theorem IsSmooth.rule_prodMk
  (f : X → Y) [IsSmooth f]
  (g : X → Z) [IsSmooth g]
  : IsSmooth (λ x => (f x, g x)) := sorry

@[fun_prop_rule]
theorem IsSmooth.rule_pi
  (f : α → X → Y) [∀ a, IsSmooth (f a)]
  : IsSmooth (λ x a => f a x) := sorry

@[fun_prop_rule]
theorem IsSmooth.rule_eval (a : α)
  : IsSmooth (λ (f : α → X)  => f a) := sorry

@[fun_prop_rule]
theorem IsSmooth.rule_comp_eval 
  (a : α) (f : X → α → Y) [IsSmooth f]
  : IsSmooth (λ x => f x a) := IsSmooth.rule_comp (λ g : α → Y => g a) f


@[fun_prop_rule]
theorem IsSmooth.rule_fst
  : IsSmooth (λ xy : X×Y => xy.1) := sorry

@[fun_prop_rule]
theorem IsSmooth.rule_snd
  : IsSmooth (λ xy : X×Y => xy.2) := sorry


--------------------------------------------------------------------------------

instance (priority := low-1) IsSmooth.rule_comp_binop {X Y₁ Y₂ Z} [Vec X] [Vec Y₁] [Vec Y₂] [Vec Z]
  (f : Y₁ → Y₂ → Z) [IsSmooth λ (yy : Y₁×Y₂) => f yy.1 yy.2]
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : IsSmooth (λ x => f (g₁ x) (g₂ x)) := sorry


#exit

instance IsSmooth1_to_IsSmoothT (f : X → Y) [inst : IsSmoothN 1 f] 
  : IsSmoothT f := 
by 
  induction inst; infer_instance


instance IsSmooth2_to_IsSmoothT_2 (f : X → Y → Z) [inst : IsSmoothN 2 f] (x : X) 
  : IsSmoothT (λ y => f x y) := 
by
  induction inst
  apply show_smoothness_via ((λ xy ⟿ (uncurryN 2 f) xy) |> (λ f => curry f x)) 
    (by ext y; simp)

instance IsSmooth2_to_IsSmoothT_1 (f : X → Y → Z) [inst : IsSmoothN 2 f] 
  : IsSmoothT (λ x => λ y ⟿ f x y) :=
by
  induction inst
  apply show_smoothness_via ((λ xy ⟿ (uncurryN 2 f) xy) |> curry) 
    (by ext x y; simp)


instance IsSmooth3_to_IsSmoothT_3 (f : X → Y → Z → W) [inst : IsSmoothN 3 f] (x : X) (y : Y)
  : IsSmoothT (λ z => f x y z) := 
by
  induction inst
  apply show_smoothness_via ((λ xyz ⟿ (uncurryN 3 f) xyz) |> (λ f => curry f x) |> (λ f => curry f y))
    (by ext z; simp)

instance IsSmooth3_to_IsSmoothT_2 (f : X → Y → Z → W) [inst : IsSmoothN 3 f] (x : X) 
  : IsSmoothT (λ y => λ z ⟿ f x y z) := 
by
  induction inst
  apply show_smoothness_via (curry ((curry (λ xyz ⟿ (uncurryN 3 f) xyz)) x))
    (by ext y; simp)

instance IsSmooth3_to_IsSmoothT_1 (f : X → Y → Z → W) [inst : IsSmoothN 3 f] 
  : IsSmoothT (λ x => λ y z ⟿ f x y z) :=
by
  induction inst
  apply show_smoothness_via ((λ xyz ⟿ (uncurryN 3 f) xyz) |> curry |> comp curry) 
    (by ext x y; simp)

-- ...

-- instance uncurry1_isSmooth {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmoothT f] : IsSmoothT (uncurryN (no_index 1) f) := sorry

instance uncurry2_isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y] : IsSmoothT (uncurryN (no_index 2) f) := 
  show_smoothness_via (Smooth.uncurry (λ x y ⟿ f x y)) (by ext xy; simp)


--------------------------------------------------------------------------------
-- Forgetting smoothness
--------------------------------------------------------------------------------

instance IsSmooth2_forget_y (f : X → Y → Z) 
  [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y] -- [IsSmoothN 2 f]
  : IsSmoothT f := 
by 
  try infer_instance
  apply show_smoothness_via (comp forget (λ x y ⟿ f x y))
    (by ext x y; simp[comp'])

instance IsSmooth3_forget_z (f : X → Y → Z → W) 
  [∀ x y, IsSmoothT (λ z => f x y z)] [∀ x, IsSmoothT λ y => λ z ⟿ f x y z] 
  [IsSmoothT λ x => λ y z ⟿ f x y z] -- [IsSmoothN 3 f]
  : IsSmoothT (λ x => λ y ⟿ λ z => f x y z) := 
by 
  try infer_instance
  apply show_smoothness_via (comp (comp forget) (λ x y z ⟿ f x y z))
    (by ext x y; simp[comp'])

instance IsSmooth3_forget_y (f : X → Y → Z → W) (y : Y) 
  [∀ x y, IsSmoothT (λ z => f x y z)] [∀ x, IsSmoothT λ y => λ z ⟿ f x y z] 
  [IsSmoothT λ x => λ y z ⟿ f x y z] -- [IsSmoothN 3 f] 
  : IsSmoothT (λ x => λ z ⟿ f x y z) := 
by 
  try infer_instance
  apply show_smoothness_via (comp (eval y) (λ x y z ⟿ f x y z))
    (by ext x y; simp[comp'])

-- ...


--------------------------------------------------------------------------------
-- Lambda calculus rules for IsSmooth
--------------------------------------------------------------------------------


-- I: X⟿X

instance (priority:=high) IsSmoothT_rule_I : IsSmoothT (λ x : X => x) := id.property


-- K: X⟿Y⟿X

instance (priority:=high) IsSmoothT_rule_K₂ (x : X) : IsSmoothT (λ _ : Y => x) := 
by
  have h : (λ _ : Y => x) = curry fst x := by simp[curry,fst]
  rw[h]; infer_instance

instance (priority:=high) IsSmoothT_rule_K₁ : IsSmoothT (λ (x : X) => λ (_ : Y) ⟿ x) := 
by
  have h : (λ (x : X) => λ (_ : Y) ⟿ x) = curry fst := by simp[curry,fst]
  rw[h]; infer_instance


-- S: (X⟿Y⟿Z)⟿(X⟿Y)⟿X⟿Z

instance IsSmoothT_rule_S₃
  (f : X → Y → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y] -- [IsSmoothN 2 f]
  (g : X → Y)  [IsSmoothT g]
  : IsSmoothT (λ x => f x (g x)) := 
by
  have h : (λ x => f x (g x)) 
           = 
           comp (uncurry (λ x y ⟿ f x y)) (prodMap id (λ x ⟿ g x)) 
         := by simp[comp, uncurry, prodMap, Smooth.id]
  rw[h]; infer_instance

-- formulated `g` as unbundled morphism
instance IsSmoothT_rule_S₂
  (f : X → Y → Z)   [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y] -- [IsSmoothN 2 f]
  (g : V → (X → Y)) [∀ v, IsSmoothT (g v)] [IsSmoothT λ v => λ x ⟿ g v x] -- [IsSmoothN 2 g]
  : IsSmoothT (λ v => λ x ⟿ f x (g v x)) := 
by
  let f' := uncurry (λ x y ⟿ f x y)
  let g' := prodMap snd (uncurry (λ v x ⟿ g v x))
  have h : (λ v => λ x ⟿ f x (g v x)) 
           = 
           curry (comp f' g') 
         := by simp[comp,curry,uncurry,prodMap,fst,snd]
  rw[h]; infer_instance

-- we get the bundled morphism version automatically
example 
  (f : X → Y → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y] -- [IsSmoothN 2 f]
  : IsSmoothT (λ (g : X⟿Y) => λ x ⟿ f x (g x)) := 
by
  infer_instance

instance IsSmoothT_rule_S₁ 
  (f : U → (X → Y → Z)) [∀ u x, IsSmoothT (λ y => f u x y)] [∀ u, IsSmoothT λ x => λ y ⟿ f u x y] [IsSmoothT λ u => λ x y ⟿ f u x y] -- [IsSmoothT3 f] 
  (g : V → (X → Y))      [∀ v, IsSmoothT (g v)] [IsSmoothT λ v => λ x ⟿ g v x]  -- [IsSmoothN 2 g]
  : IsSmoothT (λ u => λ v x ⟿ f u x (g v x)) := 
by
  let f' := uncurry (comp uncurry (λ u x y ⟿ f u x y))
  let g' := prodMap (fst (X:=U)) (prodMap (comp snd snd) (comp (uncurry (λ v x ⟿ g v x)) snd))
  have h : (λ u => λ v x ⟿ f u x (g v x)) 
           = 
           comp curry (curry (comp f' g')) 
         := by simp[comp,curry,uncurry,prodMap,fst,snd]
  rw[h]; infer_instance


-- Π : (α→X⟿Y)⟿(α→X)⟿α→Y

instance IsSmoothT_rule_forall₂
  (f : α → X → Y) [∀ a, IsSmoothT (f a)]
  : IsSmoothT λ (g : α → X) a => f a (g a) :=
by
  have h : (λ (g : α → X) a => f a (g a)) = forallMap' (λ a => λ x ⟿ f a x) := by simp[forallMap']
  rw[h]; infer_instance

instance IsSmoothT_rule_forall₁
  (f : U → α → X → Y) [∀ u a, IsSmoothT (f u a)] [IsSmoothT λ u a => λ x ⟿ (f u a x)]
  : IsSmoothT λ u => λ (g : α → X) ⟿ λ a => f u a (g a) :=
by
  let f' := forallMap' (λ a => uncurry (comp (proj a) (λ u ⟿ λ a => λ x ⟿ f u a x)))
  let p  := comp forallMap (forallMap' (λ _ : α => pair (X:=U) (Y:=X)))
  have h : (λ u => λ (g : α → X) ⟿ λ a => f u a (g a)) 
           =
           comp (comp (comp f') p) (const α)
         := by ext u g a; simp[comp']
  rw[h]; infer_instance


-- π : (α→X)⟿X

instance IsSmoothT_rule_proj (a : α)
  : IsSmoothT λ (f : α → X) => f a := 
by 
  have h : (λ (f : α → X) => f a) = proj a := by simp[proj]
  rw[h]; infer_instance


-- const : X⟿(α→X)

instance IsSmoothT_rule_const
  : IsSmoothT λ (x : X) (_ : α) => x := 
by
  have h : (λ (x : X) (_ : α) => x) = const α := by simp[const]
  rw[h]; infer_instance


-- C : (α→X⟿Y)⟿X⟿α→Y

instance IsSmoothT_rule_C₂ 
  (f : α → X → Y) [∀ a, IsSmoothT (f a)]
  : IsSmoothT λ x a => f a x := 
by
  try infer_instance
  -- have : IsSmoothT λ x => λ y ⟿ (λ (_ : X) (g : α → X) a => f a (g a)) x y := by simp; infer_instance 
  -- apply IsSmoothT_rule_S₃ (λ _ (g : α → X) a => f a (g a)) (λ x _ => x)
  have h : (λ x a => f a x) 
           = 
           comp (forallMap (λ a => λ x ⟿ f a x)) (const α)
         := by simp[comp, forallMap, const]
  rw[h]; infer_instance


instance (priority:=low) IsSmoothT_rule_C₁ 
  (f : U → α → X → Y) [∀ a u, IsSmoothT (λ x => f u a x)] [∀ a, IsSmoothT (λ u => λ x ⟿ f u a x)] -- [∀ a, IsSmoothN 2 (λ u x => f u a x)]
  : IsSmoothT λ u => λ x ⟿ λ a => f u a x :=
by
  try infer_instance
  apply show_smoothness_via
        (curry (λ xy ⟿ λ a => uncurry (λ u x ⟿ f u a x) xy))
        (by ext u x a; simp[curry'])


-- C' : (X⟿α→Y)⟿α→X⟿Y

instance (priority:=low) IsSmoothT_rule_C'₂ 
  (f : X → α → Y) (a : α) [IsSmoothT f] 
  : IsSmoothT λ x => f x a :=
by
  try infer_instance
  have h : (λ x => f x a) = comp (proj a) (λ x ⟿ f x) := by simp[comp,proj]
  rw[h]; infer_instance

instance (priority:=low) IsSmoothT_rule_C'₁ 
  (f : U → X → α → Y) (a : α) [∀ u, IsSmoothT (f u)] [IsSmoothT λ u => λ x ⟿ f u x] -- [IsSmoothN 2 f] 
  : IsSmoothT λ u => λ x ⟿ f u x a :=
by
  try infer_instance
  apply show_smoothness_via 
        (curry (λ xy ⟿ uncurry (λ u x ⟿ f u x) xy a))
        (by ext u x; simp[uncurry'])
  done


--------------------------------------------------------------------------------
-- Unification hints and short circuits to reduce timeouts
--------------------------------------------------------------------------------

-- As a proper unification hint this causes all sorts of timeouts
instance (priority := low) IsSmoothT_rule_S₂.unif_hint_1
  (f : Y → X → Z) [∀ y, IsSmoothT (f y)] [IsSmoothT λ y => λ x ⟿ f y x]
  (g : U → Y) [IsSmoothT g] 
  : IsSmoothT λ u => λ x ⟿ f (g u) x := 
by 
  try infer_instance
  apply IsSmoothT_rule_S₂ (λ x y => f y x) (λ u _ => g u)


-- (Y⟿Z)⟿(X⟿Y)⟿X⟿Z

instance IsSmoothT_comp₃
  (f : Y → Z) [IsSmoothT f]
  (g : X → Y) [IsSmoothT g]
  : IsSmoothT fun x => f (g x) := by infer_instance

instance IsSmoothT_comp₂
  (f : Y → Z) [IsSmoothT f]
  (g : V → (X → Y))      [∀ v, IsSmoothT (g v)] [IsSmoothT λ v => λ x ⟿ g v x]  -- [IsSmoothT2 g]
  : IsSmoothT λ v => λ x ⟿ f (g v x) := by infer_instance

instance IsSmoothT_comp₁
  (f : U → (Y → Z)) [∀ u, IsSmoothT (λ y => f u y)] [IsSmoothT λ u => λ y ⟿ f u y] -- [IsSmoothT2 f] 
  (g : V → (X → Y)) [∀ v, IsSmoothT (g v)] [IsSmoothT λ v => λ x ⟿ g v x]  -- [IsSmoothT2 g]
  : IsSmoothT λ u => λ v x ⟿ f u (g v x) := 
by 
  have : IsSmoothT fun u => λ (_ : X) (y : Y) ⟿ f u y := by (try infer_instance); apply IsSmoothT_comp₃ (λ x => λ _ ⟿ x) (λ u => λ y ⟿ f u y)
  infer_instance


-- (X⟿Y⟿Z)⟿Y⟿X⟿Z


theorem IsSmoothT_swap_arguments₃
  (f : X → Y → Z)  [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y]
  : IsSmoothT (λ x => f x y) := by infer_instance

-- this is marked as instance to speed up some inferences
-- it seems to be quite dangerous hence the low priority
instance (priority:=low-10) IsSmoothT_swap_arguments₂
  (f : X → Y → Z)  [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y]
  : IsSmoothT (λ y => λ x ⟿ f x y) := by infer_instance

-- This one seems to be dangerous
-- instance (priority:=low-10) IsSmoothT_swap_arguments₁
--   (f : U → X → Y → Z)  [∀ u x, IsSmoothT (f u x)] [∀ u, IsSmoothT λ x => λ y ⟿ f u x y] [IsSmoothT λ u => λ x y ⟿ f u x y]
--   : IsSmoothT (λ u => λ y x ⟿ f u x y) := by infer_instance

-- instance (priority:=low-10) IsSmoothT_swap_arguments₁'
--   (f : U → X → Y → Z)  [∀ u x, IsSmoothT (f u x)] [∀ u, IsSmoothT λ x => λ y ⟿ f u x y] [IsSmoothT λ u => λ x y ⟿ f u x y]
--   : IsSmoothT (λ x => λ y u ⟿ f u x y) := by infer_instance

-- instance (priority:=low-10) IsSmoothT_swap_arguments₁''
--   (f : U → X → Y → Z)  [∀ u x, IsSmoothT (f u x)] [∀ u, IsSmoothT λ x => λ y ⟿ f u x y] [IsSmoothT λ u => λ x y ⟿ f u x y]
--   : IsSmoothT (λ y => λ x u ⟿ f u x y) := by infer_instance

-- instance (priority:=low-10) IsSmoothT_swap_arguments₁'''
--   (f : U → X → Y → Z)  [∀ u x, IsSmoothT (f u x)] [∀ u, IsSmoothT λ x => λ y ⟿ f u x y] [IsSmoothT λ u => λ x y ⟿ f u x y]
--   : IsSmoothT (λ y => λ u x ⟿ f u x y) := by infer_instance

-- instance (priority:=low-10) IsSmoothT_swap_arguments₀
--   (f : U → V → X → Y → Z)  [∀ u v x, IsSmoothT (f u v x)] [∀ u v, IsSmoothT λ x => λ y ⟿ f u v x y] [∀ u, IsSmoothT λ v => λ x y ⟿ f u v x y] [IsSmoothT λ u => λ v x y ⟿ f u v x y]
--   : IsSmoothT (λ u => λ v y x ⟿ f u v x y) := by infer_instance

-- instance (priority:=low-10) IsSmoothT_swap_arguments₀'
--   (f : U → V → X → Y → Z)  [∀ u v x, IsSmoothT (f u v x)] [∀ u v, IsSmoothT λ x => λ y ⟿ f u v x y] [∀ u, IsSmoothT λ v => λ x y ⟿ f u v x y] [IsSmoothT λ u => λ v x y ⟿ f u v x y]
--   : IsSmoothT (λ u => λ x y v ⟿ f u v x y) := by infer_instance


-- (X⟿X⟿Y)⟿(X⟿Y)

theorem IsSmoothT_duplicate_argument
  (f : X → X → Y) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ x' ⟿ f x x'] -- [IsSmoothT2 f]
  : IsSmoothT (λ x => f x x) := by infer_instance

instance (priority:=low-10) IsSmoothT_duplicate_argument.unif_hint_1
  (f : X → X → Y → Z) [∀ u x, IsSmoothT (λ y => f u x y)] [∀ u, IsSmoothT λ x => λ y ⟿ f u x y] [IsSmoothT λ u => λ x y ⟿ f u x y] -- [IsSmoothT3 f]
  : IsSmoothT (λ x => λ y ⟿ f x x y) :=
by
  try infer_instance
  apply IsSmoothT_duplicate_argument (λ x x' => λ y ⟿ f x x' y)

instance (priority:=low-1) IsSmoothT_duplicate_argument.unif_hint_2
  (f : U → (X → Y → Z)) [∀ u x, IsSmoothT (λ y => f u x y)] [∀ u, IsSmoothT λ x => λ y ⟿ f u x y] [IsSmoothT λ u => λ x y ⟿ f u x y] -- [IsSmoothT3 f]
  (g : U → (X → Y))      [∀ v, IsSmoothT (g v)] [IsSmoothT λ v => λ x ⟿ g v x]  -- [IsSmoothT2 g]
  : IsSmoothT (λ u => λ x ⟿ f u x (g u x)) :=
by
  try infer_instance
  apply IsSmoothT_duplicate_argument (λ u u' => λ x ⟿ f u x (g u' x))


-- (Y₁⟿Y₂⟿Z)⟿(X⟿Y₁)⟿(X⟿Y₂)⟿X⟿Z

instance IsSmoothT_comp_binop₄
  (f : Y₁ → Y₂ → Z) [∀ y₁, IsSmoothT (f y₁)] [IsSmoothT λ y₁ => λ y₂ ⟿ f y₁ y₂]
  (g₁ : X → Y₁) [IsSmoothT g₁]
  (g₂ : X → Y₂) [IsSmoothT g₂]
  : IsSmoothT fun x => f (g₁ x) (g₂ x) := by infer_instance

instance IsSmoothT_comp_binop₃ {V₂} [Vec V₂]
  (f : Y₁ → Y₂ → Z) [∀ y₁, IsSmoothT (f y₁)] [IsSmoothT λ y₁ => λ y₂ ⟿ f y₁ y₂]
  (g₁ : X → Y₁) [IsSmoothT g₁]
  (g₂ : V₂ → (X → Y₂)) [∀ v₂, IsSmoothT (g₂ v₂)] [IsSmoothT λ v₂ => λ x ⟿ g₂ v₂ x]
  : IsSmoothT λ v₂ => λ x ⟿ f (g₁ x) (g₂ v₂ x) := by infer_instance

instance IsSmoothT_comp_binop₂ {V₁ V₂} [Vec V₁] [Vec V₂]
  (f : Y₁ → Y₂ → Z) [∀ y₁, IsSmoothT (f y₁)] [IsSmoothT λ y₁ => λ y₂ ⟿ f y₁ y₂]
  (g₁ : V₁ → (X → Y₁)) [∀ v₁, IsSmoothT (g₁ v₁)] [IsSmoothT λ v₁ => λ x ⟿ g₁ v₁ x]
  (g₂ : V₂ → (X → Y₂)) [∀ v₂, IsSmoothT (g₂ v₂)] [IsSmoothT λ v₂ => λ x ⟿ g₂ v₂ x]
  : IsSmoothT λ v₁ => λ v₂ x ⟿ f (g₁ v₁ x) (g₂ v₂ x) := 
by 
  have : IsSmoothT fun v₁ => λ x y ⟿ f (g₁ v₁ x) y := by (try infer_instance); apply IsSmoothT_rule_S₂ (λ _ y₁ => λ y₂ ⟿ f y₁ y₂) g₁
  infer_instance

instance IsSmoothT_comp_binop₁ {Y₁ Y₂ V₁ V₂} [Vec Y₁] [Vec Y₂] [Vec V₁] [Vec V₂]
  (f : U → (Y₁ → Y₂ → Z)) [∀ u y₁, IsSmoothT (λ y₂ => f u y₁ y₂)] [∀ u, IsSmoothT λ y₁ => λ y₂ ⟿ f u y₁ y₂] [IsSmoothT λ u => λ y₁ y₂ ⟿ f u y₁ y₂] -- [IsSmoothT3 f] 
  (g₁ : V₁ → (X → Y₁))      [∀ v₁, IsSmoothT (g₁ v₁)] [IsSmoothT λ v₁ => λ x ⟿ g₁ v₁ x]  -- [IsSmoothN 2 g]
  (g₂ : V₂ → (X → Y₂))      [∀ v₂, IsSmoothT (g₂ v₂)] [IsSmoothT λ v₂ => λ x ⟿ g₂ v₂ x]  -- [IsSmoothN 2 g]
  : IsSmoothT (λ u => λ v₁ v₂ x ⟿ f u (g₁ v₁ x) (g₂ v₂ x)) := 
by
  sorry_proof
  -- have h : IsSmoothT (λ u => λ v₂ x v₁ ⟿ f u (g₁ v₁ x) (g₂ v₂ x))
  --          → 
  --          IsSmoothT (λ u => λ v₁ v₂ x ⟿ f u (g₁ v₁ x) (g₂ v₂ x)) := by intro h; infer_instance
  -- apply h

  -- have : IsSmoothT fun u => λ x y v₁ ⟿ f u (g₁ v₁ x) y := by infer_instance
  -- apply IsSmoothT_rule_S₁ (λ u x y => λ v₁ ⟿ f u (g₁ v₁ x) y)



--------------------------------------------------------------------------------
-- Unification hints
--------------------------------------------------------------------------------

unif_hint IsSmoothT_comp.unif_hint.one_trailing_arg
  (f? : Y → Z) (g? : X → Y) 
  (f : Y → α → Z) (g : X → Y) (a : α)
 where
  f? =?= λ x => f x a
  g? =?= g
  |-
  IsSmoothT (λ x => f? (g? x)) =?= IsSmoothT (λ x => f (g x) a)

unif_hint IsSmoothT_comp.unif_hint.two_trailing_arg
  (f? : Y → Z) (g? : X → Y)
  (f : Y → α → β → Z) (g : X → Y) (a : α) (b : β) 
where
  f? =?= λ x => f x a b
  g? =?= g
  |-
  IsSmoothT (λ x => f? (g? x)) =?= IsSmoothT (λ x => f (g x) a b)
         

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------


set_option synthInstance.maxSize 2000 

-- TODO: make these work!

theorem comp3.arg_x.isSmooth_3 -- test also in y and x !
  (f : Y₁ → Y₂ → Y₃ → W) [IsSmoothN 3 f]
  (g₁ : X → Y → Z → Y₁) [IsSmoothN 3 g₁]
  (g₂ : X → Y → Z → Y₂) [IsSmoothN 3 g₂]
  (g₃ : X → Y → Z → Y₃) [IsSmoothN 3 g₃]
  : IsSmoothT (λ z => f (g₁ x y z) (g₂ x y z) (g₃ x y z)) := 
by
  (try infer_instance); admit


-- TODO: move these to tests

-- Test of S: (X⟿Y⟿Z)⟿(X⟿Y)⟿X⟿Z with boundled morphisms
example [Vec X] [Vec Y] [Vec Z] (f : X⟿Y⟿Z) (g : X⟿Y) 
  : IsSmoothT λ (x : X) => f x (g x) := by infer_instance

example [Vec X] [Vec Y] [Vec Z] (f : X⟿Y⟿Z)
  : IsSmoothT λ (g : X⟿Y) => λ (x : X) ⟿ f x (g x) := by infer_instance

example [Vec X] [Vec Y] [Vec Z] 
  : IsSmoothT λ (f : X⟿Y⟿Z) => λ (g : X⟿Y) (x : X) ⟿ f x (g x) := by infer_instance

-- binary operation
-- example
--   (f : Y₁ → Y₂ → Z) [IsSmoothN 2 f]
--   (g₁ : X → Y → Y₁) [IsSmoothN 2 g₁]
--   (g₂ : X → Y → Y₂) [IsSmoothN 2 g₂]
--   : IsSmoothT (λ x => λ y ⟿ f (g₁ x y) (g₂ x y)) := by infer_instance
