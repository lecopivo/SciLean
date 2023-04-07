-- import SciLean.Core.Tactic.FunctionTransformation.Core

import SciLean.Core.Defs

import SciLean.Core.Differential
import SciLean.Core.Adjoint
import SciLean.Core.AdjDiff

import SciLean.Core.CoreFunctions
-- import SciLean.Data.ArrayType.Notation
-- import SciLean.Data.ArrayType.PowType
-- import SciLean.Data.DataArray

namespace SciLean

#eval show IO Unit from do 
  let map ← funTransRulesMapRef.get
  IO.println (map.toList.foldl (init:="") λ m e => m ++ toString e ++ "\n")


set_option trace.Meta.Tactic.fun_trans true in
set_option trace.Meta.Tactic.fun_trans.missing_rule true in
set_option trace.Meta.Tactic.fun_trans.rewrite true in
example {X Y ι : Type} [SemiHilbert X] [SemiHilbert Y] [Enumtype ι]
  : (λ (x : X) (i : ι) => x)†
    =
    λ f => ∑ i, f i := 
by
  fun_trans
  done

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



#exit
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

