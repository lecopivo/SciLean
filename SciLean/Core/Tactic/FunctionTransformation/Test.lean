import SciLean.Core.Tactic.FunctionTransformation.Core

import SciLean.Core.Defs
-- import SciLean.Data.ArrayType.Notation
-- import SciLean.Data.ArrayType.PowType
-- import SciLean.Data.DataArray

namespace SciLean

@[fun_trans_def]
def diff {X Y} [Vec X] [Vec Y] (f : X → Y) : X → X → Y := sorry

@[fun_trans_def]
def inv {X Y} [Nonempty X] (f : X → Y) : Y → X := sorry

@[fun_trans_def]
def adj {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : Y → X := sorry

@[fun_trans_rule]
theorem diff_id (X) [Vec X]
  : diff (λ x : X => x)
    =
    λ x dx => dx := sorry

@[fun_trans_rule]
theorem diff_const {X} (Y : Type) [Vec X] [Vec Y] (x : X)
  : diff (λ y : Y => x)
    =
    λ y dy => 0 := sorry

@[fun_trans_rule]
theorem diff_comp {X Y Z} [Vec X] [Vec Y] [Vec Z]
  (f : Y → Z) (g : X → Y) -- [IsSmoothT f] [IsSmoothT g]
  : diff (λ x : X => f (g x))
    =
    λ x dx => diff f (g x) (diff g x dx) := sorry

@[fun_trans_rule]
theorem diff_swap {α X Y : Type} [Vec X] [Vec Y]
  (f : α → X → Y) 
  : diff (λ (x : X) (a : α) => f a x)
    =
    λ x dx a => diff (f a) x dx := sorry

@[fun_trans_rule]
theorem diff_forallMap {α X Y : Type} [Vec X] [Vec Y]
  (f : α → X → Y)
  : diff (λ (g : α → X) (a : α) => f a (g a))
    =
    λ g dg a => diff (f a) (g a) (dg a) := sorry

@[fun_trans_rule]
theorem diff_eval {α} (X) [Vec X] (a : α)
  : diff (λ (f : α → X) => f a)
    =
    λ f df => df a := sorry

@[fun_trans_rule]
theorem diff_prodMap {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y) (g : X → Z)
  : diff (λ x => (f x, g x))
    =
    λ x dx => (diff f x dx, diff g x dx) := sorry


@[fun_trans_rule]
theorem diff_letBinop {X Y Z} [Vec X] [Vec Y] [Vec Z]
  (f : X → Y → Z) (g : X → Y)
  : diff (λ (x : X) => let y := g x; f x y)
    =
    λ x dx =>
      let y  := g x
      let dy := diff g x dx 
      diff (λ xy => f xy.1 xy.2) (x,y) (dx,dy) := sorry

@[fun_trans_rule]
theorem diff_letComp {X Y Z} [Vec X] [Vec Y] [Vec Z]
  (f : Y → Z) (g : X → Y)
  : diff (λ (x : X) => let y := g x; f y)
    =
    λ x dx =>
      let y  := g x
      let dy := diff g x dx 
      diff f y dy := sorry

@[fun_trans]
theorem diff_fst (X Y) [Vec X] [Vec Y]
  : diff (λ (xy : X×Y) => xy.1)
    =
    λ xy dxy => dxy.1 := sorry

@[fun_trans]
theorem diff_snd (X Y) [Vec X] [Vec Y]
  : diff (λ (xy : X×Y) => xy.2)
    =
    λ xy dxy => dxy.2 := sorry

@[fun_trans_rule]
theorem adj_id (X) [SemiHilbert X]
  : adj (λ x : X => x)
    =
    λ x => x := sorry

-- no const rule for adj

@[fun_trans_rule]
theorem adj_comp {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  (f : Y → Z) (g : X → Y)
  : adj (λ x => f (g x))
    =
    λ z => adj g (adj f z) := sorry

@[fun_trans_rule]
theorem adj_swap {X Y ι} [SemiHilbert X] [SemiHilbert Y] [Enumtype ι]
  (f : ι → X → Y)
  : adj (λ x i => f i x)
    =
    λ g => ∑ i, adj (f i) (g i) 
  := sorry

@[fun_trans_rule]
theorem adj_eval (X) {ι} [SemiHilbert X] [Enumtype ι]
  (i : ι)
  : adj (λ (f : ι → X) => f i)
    =
    λ x j => [[i=j]]•x
  := sorry

@[fun_trans_rule]
theorem adj_forallMap {X Y ι} [SemiHilbert X] [SemiHilbert Y] [Enumtype ι]
  (f : ι → X → Y) 
  : adj (λ (g : ι → X) i => f i (g i))
    =
    λ h i => adj (f i) (h i)
  := sorry

@[fun_trans_rule]
theorem adj_prodMap {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  (f : X → Y) (g : X → Z)
  : adj (λ x => (f x, g x))
    =
    λ yz => adj f yz.1 + adj g yz.2
  := sorry

@[fun_trans_rule]
theorem adj_letBinop {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  (f : X → Y → Z) (g : X → Y)
  : adj (λ x => let y := g x; f x y)
    =
    λ z => 
      let xy := adj (uncurryN 2 f) z
      xy.1 + adj g xy.2 := sorry

@[fun_trans_rule]
theorem adj_letComp {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  (f : Y → Z) (g : X → Y)
  : adj (λ x => let y := g x; f y)
    =
    λ z => 
      let y := adj f z
      adj g y := sorry


example {X Y ι} [SemiHilbert X] [SemiHilbert Y] [Enumtype ι]
  : adj (λ (x : X) (i : ι) => x)
    =
    λ f => ∑ i, f i := 
by
  fun_trans

example {X Y₁ Y₂ Z} [SemiHilbert X] [SemiHilbert Y₁] [SemiHilbert Y₂] [SemiHilbert Z]
  (f : Y₁ → Y₂ → Z) (g₁ : X → Y₁) (g₂ : X → Y₂)
  : adj (λ (x : X) => f (g₁ x) (g₂ x))
    =
    λ z => 
      let xy := adj (uncurryN 2 f) z
      adj g₁ xy.1 + adj g₂ xy.2 
  :=
by
  fun_trans




-- @[fun_trans_rule]
-- theorem adj_const {X} (ι : Type)  [SemiHilbert X]
--   : adj (λ i : ι => x)
--     =
--     λ x => x := sorry

#eval show IO Unit from do

  let rules ← funTransRulesMapRef.get 
  IO.println s!"{String.join (rules.toList.map (λ r => toString r ++ "\n"))}"


#check (2 + 4) rewrite_by simp; trace_state

variable {α β γ : Type} {X Y Y₁ Y₂ Z : Type} [Vec X] [Vec Y] [Vec Z] [Vec Y₁] [Vec Y₂]

set_option pp.all true in
set_option trace.Meta.Tactic.fun_trans true 
set_option trace.Meta.Tactic.fun_trans.rewrite true 
set_option trace.Meta.Tactic.fun_trans.missing_rule true
set_option trace.Meta.Tactic.fun_trans.normalize_let true 

example
  : diff (λ x : X => x) 
    = 
    λ x dx => dx 
  := by fun_trans


example (x : X)
  : diff (λ y : Y => x) y
    = 
    λ dy => 0
  := by fun_trans

example (a : α) (f : α → X)
  : diff (λ f' : α → X => f' a) f
    = 
    λ df => df a
  := by fun_trans


example (f : Y → Z) (g : X → Y) -- [IsSmoothT f] [IsSmoothT g]
  : diff (λ x : X => f (g x))
    = 
    λ x dx => diff f (g x) (diff g x dx)
  := by fun_trans


example (f : X → Y → Z) (g : X → Y) -- [IsSmoothT (uncurryN 2 f)] [IsSmoothT g]
  : diff (λ x : X => f x (g x))
    = 
    λ x dx => diff (uncurryN 2 f) (x, g x) (dx, diff g x dx)
  := by fun_trans


example (f : Y₁ → Y₂ → Z) (g₁ : X → Y₁) (g₂ : X → Y₂)
  -- [IsSmoothT (uncurryN 2 f)] [IsSmoothT g₁] [IsSmoothT g₂]
  : diff (λ x : X => f (g₁ x) (g₂ x))
    = 
    λ x dx => diff (uncurryN 2 f) (g₁ x, g₂ x) (diff g₁ x dx, diff g₂ x dx)
  := by fun_trans


example {ι : Type} [Enumtype ι] (f g : ι → X)
  : f + g = λ i => f i + g i := by rfl

@[simp ↓]
theorem add_diff : diff (uncurryN 2 λ x y : X => x + y) = λ xy dxy => dxy.1 + dxy.2 := sorry

example {ι : Type} [Enumtype ι]
  : diff (λ (g : ι → X) i => g i + g i)
    =
    λ g dg i => (2 : ℝ) • (dg i)
  := by fun_trans; fun_trans; done

example {ι : Type} [Enumtype ι] (p q : ℝ → ℝ) (x : ℝ)
  : diff (λ (f : ℝ → ℝ) x => f x + ⅆ f x)
    =
    λ f df => df + diff differentialScalar f df
  := by fun_trans; fun_trans; done

example 
  (p q f : ℝ → ℝ)
  : ((fun x => p x * f x) + fun x => q x * differentialScalar f x)
    =
    fun x => p x * f x + q x * differentialScalar f x
  := by rfl

example {ι : Type} [Enumtype ι] (p q : ℝ → ℝ) (x : ℝ) (c : ℝ)
  : diff (λ (f : ℝ → ℝ) => x * f x)
    =
    λ f df => x * df x
  := by fun_trans; done

-- @[fun_trans_guard] -- do not recurse inside of this term
noncomputable
def invChoice {α} [h : Nonempty α] /- {val : α} -/ : α  := Classical.choice h

@[simp ↓]
theorem setElem_inv {XI X I} [ArrayType XI I X] [Nonempty XI] [Nonempty X] (i : I) 
  : inv (uncurryN 2 λ (x : XI) (xi : X) => setElem x i xi)
    =
    λ x => (uncurryN 2 λ (x : XI) (xi : X) => (setElem x i xi, x[i])) (x,invChoice)
    := 
by  
  sorry

@[simp ↓]
theorem setElem_inv' {XI X I} [ArrayType XI I X] [Nonempty XI] [Nonempty X] (i : I) 
  : inv (uncurryN 2 λ (x : XI) (xi : X) => (setElem x i xi, x[i]))
    =
    λ xxi : XI×X => 
      let x := xxi.1
      let xi := xxi.2
      (setElem x i xi, x[i])
    := 
by
  sorry

@[simp ↓]
theorem setElem_inv'' {XI X I} [ArrayType XI I X] [Nonempty XI] (i j : I) 
  : inv (λ (x : XI) => (setElem x i x[j], x[i]))
    =
    λ xxi : XI×X => 
      let x := xxi.1
      let xi := xxi.2
      setElem x i xi
    := 
by
  sorry

@[fun_trans_rule]
theorem inv_id (X) [Nonempty X]
  : inv (λ x : X => x)
    =
    λ x => x := sorry

@[fun_trans_rule]
theorem inv_comp {α β γ : Type} [Nonempty α] [Nonempty β]
  (f : β → γ) (g : α → β)
  : inv (λ x => f (g x))
    =
    λ z => inv g (inv f z)
  := sorry


set_option pp.notation true in
example (n : ℕ) (i j : Fin n)
  : (inv (λ x : ℝ^{n} => Id.run do
      let mut x := x
      let tmp := x[i]
      x[i] := x[j]
      x[j] := tmp
      x))
    =
    (λ x : ℝ^{n} => Id.run do
      let mut x := x
      let tmp := x[j]
      x[j] := x[i]
      x[i] := tmp
      x)
  := 
by
  dsimp [Id.run]
  fun_trans
  dsimp
  done

