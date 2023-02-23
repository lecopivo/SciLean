import Lean.Parser

namespace SciLean

open Lean Parser.Term 

abbrev BracketedBinder := TSyntax ``bracketedBinder

def BracketedBinder.getIdents (b : BracketedBinder) : Array Ident :=
  match b with
  | `(bracketedBinderF| ($x* $[: $X]?)) => x.map λ i => ⟨i.raw⟩  -- TODO: remove the hack ⟨i.raw⟩
  | `(bracketedBinderF| {$x* $[: $X]?}) => x.map λ i => ⟨i.raw⟩  -- TODO: remove the hack ⟨i.raw⟩
  | `(bracketedBinderF| [$x : $_]) => #[x]
  | _ => default

def BracketedBinder.getIdent (b : BracketedBinder) : Ident :=
  b.getIdents.getD 0 default
  
def BracketedBinder.getType (b : BracketedBinder) : TSyntax `term :=
  match b with
  | `(bracketedBinderF| ($x* : $X)) => X
  | `(bracketedBinderF| {$x* : $X}) => X
  | `(bracketedBinderF| [$[$x :]? $X]) => X
  | _ => default


def BracketedBinder.isExplicit (b : BracketedBinder) : Bool :=
  b.raw.getKind = ``Lean.Parser.Term.explicitBinder


def BracketedBinder.isImplicit (b : BracketedBinder) : Bool :=
  b.raw.getKind = ``Lean.Parser.Term.implicitBinder


def BracketedBinder.isInst (b : BracketedBinder) : Bool :=
  b.raw.getKind = ``Lean.Parser.Term.instBinder


def BracketedBinder.split (b : BracketedBinder) : MacroM (Array BracketedBinder) :=
  match b with
  | `(bracketedBinderF| ($x* : $X)) => x.mapM λ x => `(bracketedBinderF| ($x : $X))
  | `(bracketedBinderF| {$x* : $X}) => x.mapM λ x => `(bracketedBinderF| {$x : $X})
  | _ => pure #[b]


def BracketedBinder.toFunBinder (b : BracketedBinder) : MacroM (TSyntax ``Parser.Term.funBinder) :=
  match b with
  | `(bracketedBinderF| ($x : $X)) => let x : Ident := ⟨x.raw⟩; `(funBinder| ($x : $X))  -- TODO: remove the hack ⟨x.raw⟩
  | `(bracketedBinderF| {$x : $X}) => let x : Ident := ⟨x.raw⟩; `(funBinder| {$x : $X})  -- TODO: remove the hack ⟨x.raw⟩
  | `(bracketedBinderF| [$[$x :]? $X]) => `(funBinder| [$X])
  | _ => default


