import Qq

import Mathlib.Tactic

import SciLean.Tactic.FunGTrans.Decl
import SciLean.Tactic.FunGTrans.Theorems
import SciLean.Tactic.FunGTrans.Attr
import SciLean.Tactic.FunGTrans.Core

open Lean Meta Qq

namespace SciLean.Tactic.FunGTrans


def HasDeriv (f : α → β) (df : outParam <| α → α → β) : Prop := sorry

#eval addGTransDecl ``HasDeriv

theorem hasDeriv_id : HasDeriv (fun x : α => x) (fun x dx => dx) := sorry
theorem hasDeriv_const [Inhabited β] (b : β) : HasDeriv (fun x : α => b) (fun x dx => default) := sorry
theorem hasDeriv_comp
  (f : β → γ) (g : α → β)
  (f' : β → β → γ) (g' : α → α → β)
  (hf : HasDeriv f f') (hg : HasDeriv g g') :
  HasDeriv (fun x => f (g x)) (fun x dx => f' (g x) (g' x dx)) := sorry

theorem hasDeriv_add [Add β]
  (f g : α → β)
  (f' g' : α → α → β)
  (hf : HasDeriv f f') (hg : HasDeriv g g') :
  HasDeriv
    (fun x => f x + g x)
    (fun x dx =>
      let dy := f' x dx
      let dz := g' x dx
      dy + dz) := sorry

theorem hasDeriv_mul [Add β] [Mul β]
  (f g : α → β)
  (f' g' : α → α → β)
  (hf : HasDeriv f f') (hg : HasDeriv g g') :
  HasDeriv
    (fun x => f x * g x)
    (fun x dx =>
      let y := f x
      let dy := f' x dx
      let z := g x
      let dz := g' x dx
      y*dz+z*dy) := sorry

#eval addTheorem ``hasDeriv_comp
#eval addTheorem ``hasDeriv_id
#eval addTheorem ``hasDeriv_const
#eval addTheorem ``hasDeriv_add
#eval addTheorem ``hasDeriv_mul

-- set_option trace.Meta.Tactic.gtrans.candidates true
set_option trace.Meta.Tactic.gtrans true
-- set_option trace.Meta.Tactic.gtrans.normalize true

#eval show MetaM Unit from do

  withLocalDeclDQ `n q(Nat) fun n => do

  let e := q(HasDeriv (fun x : Nat => x*x*x*x*x*x))
  let (xs,_,b) ← forallMetaTelescope (← inferType e)
  let e := e.beta xs
  let _ ← gtrans 100 e

  IO.println (← ppExpr e)



@[gtrans]
def HasDerivOn (f : α → β) (x : outParam <| Set α) (df : outParam <| α → α → β) : Prop := sorry


@[gtrans]
theorem hasDerivOn_id : HasDerivOn (fun x : α => x) ⊤ (fun x dx => dx) := sorry

@[gtrans]
theorem hasDerivOn_const [Inhabited β] (b : β) (s : Set α) : HasDerivOn (fun x : α => b) ⊤ (fun x dx => default) := sorry

@[gtrans]
theorem hasDerivOn_comp
  (f : β → γ) (g : α → β) (s : Set α)
  (f' : β → β → γ) (g' : α → α → β)
  (hf : HasDerivOn f (g '' s) f') (hg : HasDerivOn g s g') :
  HasDerivOn (fun x => f (g x)) s (fun x dx => f' (g x) (g' x dx)) := sorry

@[gtrans]
theorem hasDerivOn_add [Add β]
  (f g : α → β)
  (f' g' : α → α → β) (sf sg : Set α)
  (hf : HasDerivOn f sf f') (hg : HasDerivOn g sg g') :
  HasDerivOn
    (fun x => f x + g x)
    (sf ∩ sg)
    (fun x dx =>
      let dy := f' x dx
      let dz := g' x dx
      dy + dz) := sorry

@[gtrans]
theorem hasDerivOn_mul [Add β] [Mul β]
  (f g : α → β)
  (f' g' : α → α → β) (sf sg : Set α)
  (hf : HasDerivOn f sf f') (hg : HasDerivOn g sg g') :
  HasDerivOn
    (fun x => f x * g x)
    (sf ∩ sg)
    (fun x dx =>
      let y := f x
      let dy := f' x dx
      let z := g x
      let dz := g' x dx
      y*dz+z*dy) := sorry

@[gtrans]
theorem hasDerivOn_div [Add β] [Sub β] [Mul β] [Div β] [Inhabited β]
  (f g : α → β)
  (f' g' : α → α → β) (sf sg : Set α)
  (hf : HasDerivOn f sf f') (hg : HasDerivOn g sg g') :
  HasDerivOn
    (fun x => f x / g x)
    (sf ∩ sg ∩ g ⁻¹' {default}ᶜ)
    (fun x dx =>
      let y := f x
      let dy := f' x dx
      let z := g x
      let dz := g' x dx
      (dy*z-y*dz)/(z*z)) := sorry


set_option trace.Meta.Tactic.gtrans true
set_option trace.Meta.Tactic.gtrans.candidates true

#eval show MetaM Unit from do

  withLocalDeclDQ `n q(Nat) fun n => do

  let e := q(HasDerivOn (fun x : Nat => x*x/(x+x*x*$n)))
  let (xs,_,_) ← forallMetaTelescope (← inferType e)
  let e := e.beta xs
  let _ ← gtrans 100 e

  IO.println (← ppExpr e)



theorem deriv_hihi
  (f : α → β)
  (f' : α → α → β)
  (hf' : ∂ f = f')
  (g : α → β)
  (g' : α → α → β)
  (hg' : ∂ g = g') :
  ∂ (fun x => f x + g x) = fun x dx => f' x dx + g' x dx := sorry
