import SciLean
import Qq

open SciLean

variable {X Y W : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert W]
         {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
         {ι κ : Type} [Enumtype ι] [Enumtype κ]


example {n : Nat} : (∇ (x : ℝ^{n}), ‖x‖²) = λ x : ℝ^{n} => (2:ℝ)*x := by symdiff; done
example {n : Nat} (m : ℝ) : (∇ (x : ℝ^{n}), 1/2 * m * ‖x‖²) = λ x : ℝ^{n} => m*x := by symdiff; done


@[diff]
theorem adjoint_sum_eval_rank1 (f : ι → X → Y) [∀ i, HasAdjointT (f i)]
  : (λ (x : ι → X) => ∑ i, f i (x i))†
    =
    λ y i => (f i)† y := by symdiff; sorry_proof




@[diff]
theorem adjDiff_sum_eval_rank1 (f : ι → X → Y) [hf : ∀ i, HasAdjDiffT (f i)]
  : ∂† (λ (x : ι → X) => ∑ i, f i (x i))
    =
    λ x dy' i => ∂† (f i) (x i) dy' := 
by 
  unfold adjointDifferential
  have := λ i => (hf i).1.1
  have := λ i => (hf i).1.2
  symdiff; symdiff; done

@[diff]
theorem revDiff_sum_eval_rank1 (f : ι → X → Y) [hf : ∀ i, HasAdjDiffT (f i)]
  : ℛ (λ (x : ι → X) => ∑ i, f i (x i))
    =
    λ x => (∑ i, f i (x i), λ dy' i => ∂† (f i) (x i) dy') := 
by 
  unfold reverseDifferential
  symdiff; done


unif_hint adjoint_sum_eval_rank1.unif_hint_0
  (f? : ι → X → Y) 
  (f : ι → W → Y) (h : X → W)
where
  f? =?= λ i x => f i (h x)
  |-
  (λ (x : ι → X) => ∑ i, (f? i) (x i))† 
  =?= 
  (λ (x : ι → X) => ∑ i, f i (h (x i)))†



unif_hint adjoint_sum_eval_rank1.unif_hint_1 
  (f? : ι → X → Y) 
  (f : ι → X → α → Y) (g : ι → α)
where
  f? =?= λ i x => f i x (g i)
  |-
  (λ (x : ι → X) => ∑ i, (f? i) (x i))† 
  =?= 
  (λ (x : ι → X) => ∑ i, f i (x i) (g i))†


unif_hint adjDiff_sum_eval_rank1.unif_hint_1
  (f? : ι → X → Y) 
  (f : ι → X → W) (h : ι → W → Y)
where
  f? =?= λ i x => h i (f i x)
  |-
  ∂† (λ (x : ι → X) => ∑ i, (f? i) (x i))
  =?= 
  ∂† (λ (x : ι → X) => ∑ i, h i (f i (x i)))

unif_hint adjDiff_sum_eval_rank1.unif_hint_2
  (f? : ι → X → Y) 
  (op : Y₁ → Y₂ → Y)
  (f₁ : ι → X → Y₁) (f₂ : ι → X → Y₂)-- (h : ι → W → Y)
where
  f? =?= λ i x => op (f₁ i x) (f₂ i x)
  |-
  ∂† (λ (x : ι → X) => ∑ i, (f? i) (x i))
  =?= 
  ∂† (λ (x : ι → X) => ∑ i, (op (f₁ i (x i)) (f₂ i (x i))))


unif_hint adjDiff_sum_eval_rank1.unif_hint_3
  (f? : ι → ℝ → ℝ) 
  -- (op : Y₁ → Y₂ → Y)
  -- (f₁ : ι → X → Y₁) (f₂ : ι → X → Y₂)-- (h : ι → W → Y)
where
  f? =?= λ i x => x * x
  |-
  ∂† (λ (x : ι → ℝ) => ∑ i, (f? i) (x i))
  =?= 
  ∂† (λ (x : ι → ℝ) => ∑ i, x i * x i)




example {n : Nat} : ∇ (x : Fin n → ℝ), ∑ i, x i = λ x i => 1 := by symdiff; done
example {n : Nat} : ∇ (x : Fin n → ℝ), ∑ i, ‖x i‖² = λ x i => (2:ℝ) * x i := by symdiff; done
example {n : Nat} (c : ℝ) : ∇ (x : Fin n → ℝ), ∑ i, c * ‖x i‖² = λ x i => 2 * c * x i := by symdiff; done 
example {n : Nat} (c : ℝ) : ∇ (x : Fin n → ℝ), ∑ i, (c + i) * ‖x i‖² = λ x (i : Fin n) => 2 * (c + i) * x i := by symdiff; done 
set_option trace.Meta.Tactic.simp.unify true in
example {n : Nat} : ∇ (x : Fin n → ℝ), ∑ i, x i * x i = λ x i => 2 * x i := by unfold gradient; funext x; symdiff; done
example {n : Nat} : ∇ (x : ℝ^{n}), ∑ i, x[i] = λ x => ⊞ i, 1 := by symdiff; done
example {n : Nat} : ∇ (x : ℝ^{n}), ∑ i, x[i]*x[i] = λ x => ⊞ i, (2:ℝ) * x[i] := by symdiff; done


open Lean Qq Meta Elab Term




def unifyTest (lhs rhs : Expr) : MetaM Unit := do
  let ppLhs ← Meta.ppExpr lhs
  let ppRhs ← Meta.ppExpr rhs
  let test ← isDefEq lhs rhs
  if test then
    IO.println s!"Success: {ppLhs} =?= {ppRhs}"
  else
    throwError "Failure: {ppLhs} =?= {ppRhs}"

unif_hint 
  (α β γ : Type) (F : (α→β) → (α→γ)) (g : β → γ)
where
  F =?= λ f x => g (f x)
  |-
  (λ f x => g (f x))
  =?=
  λ f => F f

unif_hint 
  (α β γ : Type) (F : (α→β) → (α→γ)) (g : β → γ)
where
  F =?= λ f x => g (f x)
  |-
  λ f => F f
  =?=
  (λ f x => g (f x))


notation x " =?= " y => unifyTest x y

#eval show MetaM Unit from do
  let f? : Q(Nat→Nat) ← mkFreshExprMVar q(Nat→Nat)

  unifyTest q(λ (x : Nat) => $f? x)
            q(λ (x : Nat) => Nat.succ (Nat.succ x))


#eval show MetaM Unit from do
  let n? : Q(Nat) ← mkFreshExprMVarQ q(Nat)
  let f? : Q(Nat→Nat) ← mkFreshExprMVarQ q(Nat→Nat)

  unifyTest q(λ (x : Fin $n? → Nat) i => $f? (x i))
            q(λ (x : Fin $n? → Nat) i => Nat.succ (x i))


#eval show MetaM Unit from do
  let n? : Q(Nat) ← mkFreshExprMVarQ q(Nat)
  let f? : Q(Nat→Nat) ← mkFreshExprMVarQ q(Nat→Nat)
  let g? : Q(Nat→Nat) ← mkFreshExprMVarQ q(Nat→Nat)

  unifyTest q(λ (x : Fin $n? → Nat) i => $f? (x i))
            q(λ (x : Fin $n? → Nat) i => $g? (x i))


#eval show MetaM Unit from do
  let n? : Q(Nat) ← mkFreshExprMVarQ q(Nat)
  let F? : Q((Fin $n?→Nat)→(Fin $n?→Nat)) ← mkFreshExprMVarQ q((Fin $n?→Nat)→(Fin $n?→Nat))
  let g? : Q(Nat→Nat) ← mkFreshExprMVarQ q(Nat→Nat)

  unifyTest q(λ (x : Fin $n? → Nat) => $F? x)
            q(λ (x : Fin $n? → Nat) i => $g? (x i))


#eval show MetaM Unit from do
  let X? : Q(Type) ← mkFreshExprMVarQ q(Type)
  let Y? : Q(Type) ← mkFreshExprMVarQ q(Type)
  let Z? : Q(Type) ← mkFreshExprMVarQ q(Type)
  let g? : Q($Y?→$Z?) ← mkFreshExprMVarQ q($Y?→$Z?)
  let h? : Q($Y?→$Z?) ← mkFreshExprMVarQ q($Y?→$Z?)

  q(λ (f : $X? → $Y?) x => $g? (f x))
  =?= 
  q(λ (f : $X? → $Y?) x => $h? (f x))


#eval show MetaM Unit from do
  let X? : Q(Type) ← mkFreshExprMVarQ q(Type)
  let Y? : Q(Type) ← mkFreshExprMVarQ q(Type)
  let F? : Q(($X?→$Y?)→($X?→$Y?)) ← mkFreshExprMVarQ q(($X?→$Y?)→($X?→$Y?))
  let G? : Q(($X?→$Y?)→($X?→$Y?)) ← mkFreshExprMVarQ q(($X?→$Y?)→($X?→$Y?))
  let g? : Q($Y?→$Y?) ← mkFreshExprMVarQ q($Y?→$Y?)

  q(λ (f : $X? → $Y?) => $F? f)
  =?=
  q(λ (f : $X? → $Y?) x => $g? (f x))


#eval show MetaM Unit from do
  let n? : Q(Nat) ← mkFreshExprMVarQ q(Nat)
  let f? : Q(Nat→Nat) ← mkFreshExprMVarQ q(Nat→Nat)

  unifyTest q(id $ λ (x : Fin $n? → Nat) i => $f? (x i))
            q(id $ λ (x : Fin $n? → Nat) i => Nat.succ (x i))


#eval show MetaM Unit from do
  let n? : Q(Nat) ← mkFreshExprMVarQ q(Nat)
  let op? : Q(ℝ → ℝ → ℝ) ← mkFreshExprMVarQ q(ℝ → ℝ → ℝ)

  unifyTest q(λ (x : Fin $n? → ℝ) i => $op? (x i) (x i))
            q(λ (x : Fin $n? → ℝ) i => x i * x i)


#eval show MetaM Unit from do
  let n? : Q(Nat) ← mkFreshExprMVarQ q(Nat)
  let f? : Q(Fin $n? → ℝ → ℝ) ← mkFreshExprMVarQ q(Fin $n? → ℝ → ℝ)

  unifyTest q(λ (x : Fin $n? → ℝ) i => $f? i (x i))
            q(λ (x : Fin $n? → ℝ) i => x i * x i)



def n := q(10)


-- works fine
def FinExpr := 
  let n := q(10)
  q(Fin $n)

def FinExpr' : Q(Type) := 
  let n := q(10)
  q(Fin $n) -- unknown identifier '«$n»'


-- Construct an expression
def a : Expr := q([42 + 1])

-- Construct a typed expression
def b : Q(List Nat) := q([42 + 1])

def b' : Q(Nat) := q(42 + 1)

-- Antiquotations
def c := 
  let n : Q(Nat) := q(10)
  q([42 + $n + $b'])

-- Dependently-typed antiquotations
def d (u : Level) (n : Q(Nat)) (x : Q(Type u × Fin ($n + 1))) : Q(Fin ($n + 3)) :=
  q(⟨$x.2, Nat.lt_of_lt_of_le $x.2.2 (Nat.le_add_right _ 2)⟩)


#eval show MetaM Unit from do
  let a? ← mkFreshExprMVar q(Nat)
  let b? ← mkFreshExprMVar q(Nat)
  pure ()

#eval show MetaM Unit from do
  let a? ← mkFreshExprMVarQ q(Nat)
  let b? ← mkFreshExprMVarQ q(Nat) -- incompatible metavariable _uniq.146616
  pure ()
