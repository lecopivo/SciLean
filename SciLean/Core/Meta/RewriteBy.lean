import Lean

open Lean Parser.Term Lean.Elab Meta

namespace SciLean

-- This is like `ExactSolution` but it is intended to be used in automation.
inductive AutoExactSolution {α : Type _} : (α → Prop) → Type _ where
| exact {spec : α → Prop} (a : α) (h : spec a) : AutoExactSolution spec

def AutoImpl {α} (a : α) := AutoExactSolution λ x => x = a

@[inline]
def AutoImpl.val {α} {a : α} (x : AutoImpl a) : α :=
match x with
| .exact val _ => val

def AutoImpl.finish {α} {a : α} : AutoImpl a := .exact a rfl

theorem AutoImpl.impl_eq_spec (x : AutoImpl a) : a = x.val :=
by
  cases x; rename_i a' h; 
  simp[AutoImpl.val, val, h]
  done

-- This is a dirty hack
-- I really need to figure out how to dispatch conv tactic on Expr level without elaborating tactic.
-- Then this whole mess with AutoImpl can be ditched
axiom AutoImpl.injectivity_axiom {α} {a b : α} : (AutoImpl a = AutoImpl b) → (a = b)

-- Do we really need AutoImpl.injectivity_axiom?
@[simp] theorem AutoImpl.normalize_val {α : Type u} (a b : α) (h : (AutoImpl a = AutoImpl b)) 
  : AutoImpl.val (Eq.mpr h (AutoImpl.finish (a:=b))) = b := 
by
  have h' : a = b := by apply AutoImpl.injectivity_axiom; apply h
  revert h; rw[h']
  simp[val,finish,Eq.mpr]
  done

-- -- This is a new version of `AutoImpl.normalize_val`, some tactic uses `cast` instead of `Eq.mpr` now
-- -- TODO: clean this up
-- @[simp] theorem AutoImpl.normalize_val' {α : Type u} (a b : α) (h : (AutoImpl a = AutoImpl b)) 
--   : AutoImpl.val (cast h (AutoImpl.finish (a:=a))) = a := 
-- by sorry
--   -- have h' : a = b := by apply AutoImpl.injectivity_axiom; apply h
--   -- revert h; rw[h']
--   -- simp[val,finish,Eq.mpr]
--   -- done


example {α : Type} (a b : α) (A : (Σ' x, x = a)) (h : (Σ' x, x = a) = (Σ' x, x = b))
  : (a = b) ↔ (h ▸ A).1 = A.1 := 
by
  constructor
  {
    intro eq; rw[A.2]; conv => rhs; rw [eq]
    apply (h ▸ A).2
  }
  {
    intro eq; rw[← A.2]; rw[← eq]
    apply (h ▸ A).2
  }

open Lean.Parser.Tactic.Conv


-- TODO: turn `rewrite_by` to an elaborator and do not use `AutoImpl`
/--
Rewrites term by conv tactic. 

Example: `5 + 0 rewrite_by simp` returns `5`

To also produce a proof, use `rewrite_by'`

WARRNING: It is using some dubious hackary inside. Should be easily fixable by someone with better metaprogramming skills!
-/
syntax term:max "rewrite_by" convSeq : term
/--
Rewrites term by conv tactic. Returns the new value and a proof that it is equal to the old one.

Example: `5 + 0 rewrite_by simp` returns `⟨5, _ : 5 + 0 = 5⟩`

To only produce the value, use `rewrite_by`

WARRNING: It is using some dubious hackary inside. Should be easily fixable by someone with better metaprogramming skills!
-/
syntax term:max "rewrite_by'" convSeq : term

-- TODO: Return correct proof!
def rewriteBy (e : Expr) (conv : TSyntax ``convSeq) : TermElabM (Expr × Expr) := do

  let autoImpl ← mkAppM ``AutoImpl #[e]
  let autoImplStx ← `((by (conv => enter[1]; ($conv)); (apply AutoImpl.finish)))
  let autoImplVal ← Term.elabTermAndSynthesize autoImplStx autoImpl

  let proof ← mkAppM ``AutoImpl.injectivity_axiom #[autoImplVal.getArg! 2]
  let e' := proof.getArg! 2

  return (e',proof)
  
elab_rules : term
  | `($x rewrite_by $rw:convSeq) => do

    let x ← Term.elabTermAndSynthesize x none
    let (x', _) ← rewriteBy x rw

    return x'
  | `($x rewrite_by' $rw:convSeq) => do

    let x ← Term.elabTermAndSynthesize x none
    let (x', proof) ← rewriteBy x rw

    mkAppM ``PProd.mk #[x',proof]


#check ((1 + 10 + 0 + 1 + 5 + 0 + 10) rewrite_by simp)
#check ((1 + 10 + 0 + 1 + 5 + 0 + 10) rewrite_by' simp)
#check 
  let ⟨v,p⟩ := ((id 100) rewrite_by' simp)
  p
