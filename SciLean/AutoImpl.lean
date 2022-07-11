
namespace SciLean

inductive AutoExactSolution {α : Type _} : (α → Prop) → Type _ where
| exact {spec : α → Prop} (a : α) (h : spec a) : AutoExactSolution spec

def AutoImpl {α} (a : α) := AutoExactSolution λ x => x = a

def AutoImpl.val {α} {a : α} (x : AutoImpl a) : α :=
match x with
| .exact val _ => val

def AutoImpl.finish {α} {a : α} : AutoImpl a := .exact a rfl

theorem AutoImpl.impl_eq_spec (x : AutoImpl a) : a = x.val :=
by
  cases x; rename_i a' h; 
  simp[AutoImpl.val, val, h]
  done

-- I don't think think this can be proven. Can it lead to contradiction?
axiom AutoImpl.injectivity_axiom {α} (a b : α) : (AutoImpl a = AutoImpl b) → (a = b)

-- Do we really need AutoImpl.injectivity_axiom?
set_option pp.all true in
@[simp] theorem AutoImpl.normalize_val {α : Type u} (a b : α) (h : (AutoImpl a = AutoImpl b)) 
  : AutoImpl.val (Eq.mpr h (AutoImpl.finish (a:=b))) = b := 
by
  have h' : a = b := by apply AutoImpl.injectivity_axiom; apply h
  revert h; rw[h']
  simp[val,finish,Eq.mpr]
  done

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

syntax term "rewrite_by" convSeq : term

macro_rules
  | `($x rewrite_by $rw:conv) =>
    `((by (conv => enter[1]; $rw) (apply AutoImpl.finish) : AutoImpl $x).val)
