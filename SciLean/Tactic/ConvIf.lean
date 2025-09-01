import Lean

namespace SciLean.ConvIf

@[inline]
abbrev convIf {α} (P : Prop) (_ : Decidable P) (x : P → α) (y : ¬P → α) : α := if h : P then x h else y h

def convIf.rhs {α} (P : Prop) [inst : Decidable P] (a : α) := convIf P inst (λ _ => a) (λ _ => a)

theorem convIf.id {α} (P : Prop) [inst : Decidable P] (a : α) : a = convIf P inst (λ _ => a) (λ _ => a) :=
by
  simp[convIf]

open Lean.Parser.Tactic.Conv Lean
syntax (name := conv_if) "if" binderIdent ":" term  "then" convSeq "else" convSeq : conv

open Lean.Elab Tactic Conv in
@[tactic conv_if]
def convIfTactic : Tactic
| `(conv| if $h : $P then $trueConv else $falseConv) => do
   withMainContext do

     let p ← elabTerm P none
     let t' ← Lean.Meta.mkAppM ``convIf.rhs #[p, (← getLhs)]
     let h' ← Lean.Meta.mkAppM ``convIf.id  #[p, (← getLhs)]

     updateLhs t' h'
     evalTactic (←
       `(convSeq| unfold convIf.rhs
                  conv => enter[3]; intro $h; ($trueConv)
                  conv => enter[4]; intro $h; ($falseConv)
                  unfold convIf))
| _ => throwUnsupportedSyntax
