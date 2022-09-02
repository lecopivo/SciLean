import SciLean
open SciLean

/-!
Running queries
===============
Alectryon captures the results of `#check`, `#eval`, and the like:
-/

variable (f : ℝ → ℝ) [IsSmooth f]

def x : Nat := 5
#reduce 5 + x

#check differential

#check (∂ f)  -- ℝ → ℝ → ℝ

#check (differential f)  -- ℝ → ℝ → ℝ

set_option pp.notation false in
#check (differential f)  -- ℝ → ℝ → ℝ

set_option pp.notation false in
#check (∂ f)  -- ℝ → ℝ → ℝ

set_option trace.Meta.Tactic.simp.rewrite true in
example : (ⅆ x, Math.sin x) = λ x => Math.cos x :=
by
  conv => 
    lhs                    -- focus on lhs
    simp only[derivative]  -- unfold derivative
    simp (config := {singlePass := true}) -- run simplifier
  done

/-!
By default, these results are folded and are displayed upon hovering or clicking.  We can unfold them by default using annotations or directives:
-/


def foo (x : ℝ) (y : ℝ) : ℝ := x*x*y + y
argument x
  isSmooth,
  diff?
argument y
  isSmooth,
  diff?


#check Nat /- .unfold -/

/-!
.. lean4:: unfold
-/

#check Bool
#eval 1 + 1


/-!
.. 

Hohoho

 -/

variable (f : ℝ → ℝ) 

#check ∂ f /- .unfold -/


/-!
.. 
 
Euler Lagrange equations
========================

The Euler-Lagrange equations are usually written in the following way:
[asdf](www.google.com)
  
.. math:: \frac{d}{dt} \frac{\partial}{\partial \dot x} L(x(t),\dot x(t)) - \frac{\partial}{\partial x} L(x(t),\dot x(t))

.. 

The usual partial derivative notation is really confusing. To make it
a bit more clear, we can add vertical bars indicating what you should
pass after derivative:

.. math:: \frac{d}{ds}\bigg\rvert_{s=t} \frac{\partial}{\partial v}\bigg\rvert_{v=\dot y(s)} L(y(s),v) - \frac{\partial}{\partial x}\bigg\rvert_{x=y(t)} L(x, \dot y(t))

-/

section EulerLagrange

/-!

Let's introduce few variable, first Lagrangian

 -/ 

  variable {X ι} [Enumtype ι] [FinVec X ι]  
  variable (L : X → X → ℝ)                     -- Lagrangian 
  variable [IsSmooth L] [∀ x, IsSmooth (L x)]  -- It is smooth 
  -- variable [∀ v, HasAdjDiff (λ x => L x v)] 
  -- variable [∀ x, HasAdjDiff (λ v => L x v)]    -- It has gradients

#check Nat × Nat × Nat

theorem invert_first  {X₁ X₂ Y₁ Y₂ : Type} 
  [Nonempty X₁] [Nonempty Y₁] [Nonempty X₂] [Nonempty Y₂] 
  (f : X₁×X₂ → Y₁×Y₂) [IsInv f]
  : f⁻¹ = λ (y₁,y₂) => 
      let g₁ := λ x₂ => (λ x₁ => (f (x₁, x₂)).1)⁻¹ y₁
      let x₂ := (λ x₂ => (f (g₁ x₂, x₂)).2)⁻¹ y₂
      (g₁ x₂, x₂) := sorry

theorem invert_second  {X₁ X₂ Y₁ Y₂ : Type} 
  [Nonempty X₁] [Nonempty Y₁] [Nonempty X₂] [Nonempty Y₂] 
  (f : X₁×X₂ → Y₁×Y₂) [IsInv f]
  : f⁻¹ = λ (y₁,y₂) => 
      let g₂ := λ x₁ => (λ x₂ => (f (x₁, x₂)).2)⁻¹ y₂
      let x₁ := (λ x₁ => (f (x₁, g₂ x₁)).1)⁻¹ y₁
      (x₁, g₂ x₁) := sorry

/-!

and a trajectory of our system

 -/ 

  notation "⦃" x ", " y "⦄[" Ω "]" => SemiInner.semiInner x y Ω

#check@SemiHilbert.semi_inner_add--⦃x + y, z⦄[Ω]=⦃x, z⦄[Ω]+⦃y, z⦄[Ω]
  #check @SemiHilbert.semi_inner_mul
  #check @SemiHilbert.semi_inner_sym
  #check @SemiHilbert.semi_inner_pos


  variable (y : ℝ → X)  -- trajectory 
  variable [IsSmooth y] -- it is smooth


/-! 

..
  
With all this setup, let's have a look a the second term:

.. math:: \frac{\partial}{\partial x}\bigg\rvert_{x=y(t)} L(x, \dot y(t))

 -/ 

  #check λ t => ∇ (x:=y t), L x (ⅆ y t)

/-! 
..
  
The first term is a bit more complicated:

.. math::  \frac{d}{ds}\bigg\rvert_{s=t} \frac{\partial}{\partial v}\bigg\rvert_{v=\dot y(s)} L(y(s),v)

 -/ 

  #check λ t => ⅆ (s:=t), ∇ (v:=ⅆ y s), L (y s) v

end EulerLagrange


/-!

.. 
  
Multiline equation

.. raw:: html

  \begin{align}
    y &= \int_\Omega e^{-x^2} dx \\
      &= \pi ...
  \end{align}

-/ 


/-!

..

  Here is a video

.. raw:: html

  <div>
    <div style="position:relative;padding-top:56.25%;">
      <iframe src="https://www.youtube.com/embed/qcE9hFPgYkg?rel=0" frameborder="0" allowfullscreen
        style="position:absolute;top:0;left:0;width:100%;height:100%;"></iframe>
    </div>
  </div>

 -/

/-!

..

  Here is a picture

.. raw:: html

  <img width=100% src="https://metropole.at/wp-content/uploads/2018/06/MG_1069_preview-696x363.jpeg">
  <img width=50% src="https://metropole.at/wp-content/uploads/2018/06/MG_1069_preview-696x363.jpeg">

 -/



/-!
Documenting proofs
==================
Alectryon also captures goals and hypotheses as proofs progress:
-/

theorem test (p q : Prop) (hp : p) (hq : q): p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h
    apply And.intro
    . exact hq   -- hoho
    . exact hp   /- hihi -/
  . intro h
    apply And.intro
    . exact hp
    . exact hq
