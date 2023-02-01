import SciLean.Core
import SciLean.Mechanics
import SciLean.Operators.ODE
import SciLean.Solver.Solver
import SciLean.Data.DataArray
import SciLean.Core.Extra
import SciLean.Functions.Trigonometric

import SciLean.Data.FunRec

-- set_option synthInstance.maxHeartbeats 50000
set_option synthInstance.maxSize 10000

def g : ℝ := 9.81

open SciLean

variable (f : Fin n → ℝ × ℝ)

#check λ [i] => f i

example : IsSmooth λ (θ : ℝ) => (⟨Math.sin θ, Math.cos θ⟩ : ℝ^{2}) := by infer_instance

example : IsSmooth λ (x : ℝ) => (λ [i] => x : ℝ^{2}) := by infer_instance

#check ((λ (x : ℝ) => (λ [i] => x : ℝ^{2}))† rewrite_by (simp; trace_state))

example : IsSmooth λ (θ : ℝ) => ((Math.sin θ) : ℝ) := by infer_instance

def ParticleLagrangian {n} (ϕ : ℝ^{d} → ℝ) (m : ℝ^{n}) (x v : ℝ^{d}^{n}) : ℝ :=
  ∑ i, (0.5:ℝ) * m[i] * ∥v[i]∥² - ∑ i, m[i] * ϕ x[i]

def chainConstraint {n} (l : ℝ^{n}) (x : ℝ^{2}^{n+1}) : Prop := ∀ i : Fin n, ∥x[i.succ] - x[⟨i, sorry_proof⟩]∥ = l[i]
def chainConstraintFun {n} (l : ℝ^{n}) (x : ℝ^{2}^{n+1}) : ℝ^{n} := λ [i] => l[i]*l[i] - ∥x[i.succ] - x[⟨i, sorry_proof⟩]∥²
def chainConstraintLhs {n} (l : ℝ^{n}) (x : ℝ^{2}^{n+1}) := λ i : Fin n => ∥x[i.succ] - x[⟨i, sorry_proof⟩]∥
def chainConstraintRhs {n} (l : ℝ^{n}) (x : ℝ^{2}^{n+1}) := λ i : Fin n => l[i]

instance [PowType Cont (Fin n) Elem] : GetElem Cont ℕ Elem (λ _ idx => idx < n) where
  getElem c i h := c[⟨i,h⟩]

instance [PowType Cont (Fin n × Fin m) Elem] : GetElem Cont (ℕ×ℕ) Elem (λ _ idx => idx.1 < n ∧ idx.2 < m) where
  getElem c i h := c[(⟨i.1,h.1⟩,⟨i.2,h.2⟩)]

-- ...

def endPoints {n n' : Nat} (l r : ℝ^{2}) (x : ℝ^{2}^{n+1}) (x' : ℝ^{2}^{n'+1}) : ℝ^{2} × ℝ^{2} × ℝ^{2} × ℝ^{2} := 
  (-- top chain constraints
   x[0] - l,
   x[⟨n,sorry⟩] - r,
   -- bottow chain constraints
   x'[0] - x[⟨(n+1)/4, sorry⟩],
   x'[⟨n',sorry⟩] - x[⟨3*(n+1)/4, sorry⟩])
argument x
  isSmooth, diff, hasAdjDiff, adjDiff
argument x'
  isSmooth, diff, hasAdjDiff, adjDiff



#check ode_solve


#check ReaderM NewtonSettings X

Approx (X → Y → X × Y) (constrained_ode_solve f g)


-- evolve and project, version 1
Approx ({x : X // g x = 0} → {x : X // g x = 0})
  (λ x =>
    let x' := ode_solve f Δt x.1
    let μ  := solve μ', g (x' + ∂† g x' μ') = 0
    x' + ∂† g x' μ)
=>
Approx (X → X) (constrained_ode_solve f g Δt)


-- evolve and project, version 2
Approx (X → X)
  (λ x =>
    let x' := ode_solve f Δt x
    let μ  := solve μ', g (x + (x' - x) + ∂† g x μ') = 0  -- how can I Taylor this and use the fact that `g x = 0`?
    x' + ∂† g x' μ)
=>
Approx (X → X) (constrained_ode_solve f g Δt)



-- This is exact rewrite under some conditions on `f` and `g`
-- The condition on `g` is probably  `(g x ≠ 0) → let J := ∂ g x; IsInv (J ∘ J†)` this is saying that `J` is surjective map
Approx ({x : X // g x = c} → {x : X // g x = c})
  (λ x =>
    let f' := λ x'' =>
      let μ := solve μ', ∂ g x'' (∂† g x'' μ') = - ∂ g x'' (f x'')
      f x + ∂† g x μ
    let x' := ode_solve f' Δt x
    x')
=>
Approx (X → X) (constrained_ode_solve f g Δt)



-- but I want 
-- we can use (f : X → X) => λ x y => (f x, y)
--            (f : X → Y → X × Y) => (λ x => (f x 0).1)
Approx (X → Y → X × Y) (constrained_ode_solve f g Δt)


(settings : IterLinSolverSettings) (A' : Approx (X → Y) (λ x => A x))
=>
Approx ((x₀ : X) → X) (A⁻¹ y)



(x dx : X) → Approx ((x₀ : X) → X) ((∂† f x)⁻¹ dx)

Approx (NewtonSettings → (x₀ : X) → X)
  (solve x, f x = 0)

Approx (X → X)
  (solve x, f x = 0)

-- evolve and reflect  -- inspired by advection reflection sovler
ApproxSolution (ℝ → X×Y → X×Y)
  (λ Δt x₀ μ₀ => 
    let evolve := ode_solve f (Δt/2)
    let x' := evolve x
    let μ  := 2 * solve μ', g (x' + ∂† g x' μ') = 0
    let x'' := evolve (x' + ∂† g x' μ)
    (x'', μ))

-- let u' := ode_solve f t₀ u₀
0 = ∇ u', L u' + ⟪μ, g u'⟫ 
let    := u' + solve μ, g u'


#exit
def L' (m : ℝ×ℝ) (x v : ℝ^{2}×ℝ^{2}) : ℝ :=
    (m.1/2) * ∥v.1∥² + (m.2/2) * ∥v.2∥² - m.1 * g * x.1[1] - m.2 * g * x.2[1]
argument x
  isSmooth, diff, hasAdjDiff, adjDiff
argument v
  isSmooth, diff, hasAdjDiff, adjDiff

def parm (l : ℝ × ℝ) (θ : ℝ^{2}) : ℝ^{2}×ℝ^{2} :=
  let d₁ : ℝ^{2} := ⟨Math.sin θ[0], Math.cos θ[0]⟩
  let d₂ : ℝ^{2} := ⟨Math.sin θ[1], Math.cos θ[1]⟩
  -- (l.1 * d₁, l.1 * d₁ + l.2 * d₂)
  (d₁, d₂)
argument θ 
  isSmooth

def parm' {n} (l : ℝ^{n}) (θ : ℝ^{n}) (x₀ : ℝ^{2}) : (ℝ^{2})^{n+1} := Id.run do
  let mut x : (ℝ^{2})^{n+1} := 0
  let mut y := x₀
  for h : i in [0:n] do
    let i : Fin n := ⟨i, h.2⟩
    let next := i.succ
    let dir : ℝ^{2} := ⟨Math.cos (θ[i]), Math.sin (θ[i])⟩
    y += l[i] * dir
    x[next] := y
  x


-- This impelementation is paying for zero initialization
def parm'' {n} (l : ℝ^{n}) (θ : ℝ^{n}) (x₀ : ℝ^{2}) : (ℝ^{2})^{n+1} := Id.run do
  let mut x : (ℝ^{2})^{n+1} := 0
  let mut y := x₀
  for h : i in [0:n] do
    let i : Fin n := ⟨i, h.2⟩
    let next := i.succ
    let dir : ℝ^{2} := ⟨Math.cos (θ[i]), Math.sin (θ[i])⟩
    y := y + l[i] * dir
    x[next] := y
  x

-- There is no way the index access `θ[⟨n',sorry⟩]` and `l[⟨n', sorry⟩]` can be proven correct
-- Can be fixed by changing the definition of `funRec`
def parm''' {n} (l : ℝ^{n}) (θ : ℝ^{n}) (x₀ : ℝ^{2}) : (ℝ^{2})^{n+1} := funRec (n+1) 0 step (reserveElem (n+1) 0)
  where
    step : (n' : Nat) → ((ℝ^{2})^{n'}) → (ℝ^{2})^{n'+1}
    | 0, x => (λ [i] => x₀)
    | n'+1, x => 
      let dir : ℝ^{2} := ⟨Math.cos (θ[⟨n',sorry_proof⟩]), Math.sin (θ[⟨n',sorry_proof⟩])⟩
      let y := x[⟨n', by simp⟩] + l[⟨n', sorry_proof⟩] * dir
      pushElem 1 y x

example (x₀ : ℝ^{2}) (n' : Nat) : IsSmooth λ (x : (ℝ^{2})^{n'}) => pushElem (Cont:=(ℝ^{2}^{·})) 1 x₀ x := by infer_instance
example (x : (ℝ^{2})^{n'}) (n' : Nat) : IsSmooth λ (x₀ : ℝ^{2}) => pushElem (Cont:=(ℝ^{2}^{·})) 1 x₀ x := by infer_instance

instance {α : Nat → Type} [Vec X] [∀ n, Vec (α n)] 
  (f : X → (n : Nat) → α n → α (n + 1)) [∀ n, IsSmooth (λ x => f x n)] [∀ x n, IsSmooth (f x n)] (n : Nat) 
  : IsSmooth (λ x => funRec n m (f x)) := sorry_proof


@[simp ↓]
theorem funRec.arg_x.diff_simp {α : Nat → Type} [Vec X] [∀ n, Vec (α n)]
  (f : (n : Nat) → α n → α (n + 1)) [∀ n, IsSmooth (f n)] (n m : Nat) 
  : ∂ (λ x => funRec n m f x) 
    = 
    λ x dx => (funRec (α:=λ n' => α n' × α n') n m (λ n' (x',dx') => (f n' x', ∂ (f n') x' dx')) (x,dx)).2 := sorry_proof

@[simp ↓]
theorem funRec.arg_f.diff_simp {α : Nat → Type} [Vec X] [∀ n, Vec (α n)]
  (f : X → (n : Nat) → α n → α (n + 1)) [∀ n, IsSmooth (λ x => f x n)] [∀ x n, IsSmooth (f x n)] (n : Nat) 
  : ∂ (λ x => funRec n m (f x)) 
    = 
    λ x dx y => (∂ (funRec (α:=λ n' => X × α n') n m (λ n' xy' => (xy'.1, f xy'.1 n' xy'.2))) (x,y) (dx,0)).2 := sorry_proof



set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
def parm'''' {n} (l : ℝ^{n}) (θ : ℝ^{n}) (x₀ : ℝ) : ℝ^{n+1} :=
  let step (n' : Nat) (x : ℝ^{n'}) : ℝ^{n'+1} := pushElem (Cont:=(ℝ^{·})) 1 (θ[⟨n',sorry⟩]) x
  funRec (n+1) 0 step 0
argument θ
  -- isSmooth := by simp[parm'''']; infer_instance,
  diff by 
    simp[parm'''']
    enter [θ,x,a]
    simp only [funRec.arg_x.diff_simp (α:= λ n' => ℝ^{n} × ℝ^{n'})]
    simp --  (λ n' y => (y.1, pushElem 1 (y.1[⟨n',sorry⟩]) (y.snd))) (n+1) 0]


def parm'''' {n} (l : ℝ^{n}) (θ : ℝ^{n}) (x₀ : ℝ^{2}) : (ℝ^{2})^{n+1} := step 1 n (λ [i] => x₀)
  where
    step : (n m : Nat) → ((ℝ^{2})^{n+1-m}) → (ℝ^{2})^{n+1}
    | n, 0, x => x
    | n, m+1, x => pushElem 1 sorry (step n m x)
    -- | n'+1, x => 
    --   let dir : ℝ^{2} := ⟨Math.cos (θ[⟨n',sorry_proof⟩]), Math.sin (θ[⟨n',sorry_proof⟩])⟩
    --   let y := x[⟨n', by simp⟩] + l[⟨n', sorry_proof⟩] * dir
    --   pushElem 1 y x




def L (m l : ℝ×ℝ) (θ ω : ℝ^{2}) := 
  (L' m (parm l θ) (ⅆ (t:=0), parm l (θ + (t:ℝ) * ω)))
    rewrite_by 
      simp

def solver (m l : ℝ×ℝ) (steps : Nat) : Impl (ode_solve (LagrangianSystem (L m l))) :=
by
  simp [L, pure_impl, PureImpl]
  conv in (L _ _) =>
    simp [L, L', parm]
    pattern (differential _); rmlamlet; enter [θ, ω]; simp  -- autodiff
  
  simp -- Lagrangian is in a nice form now

  conv => 
    pattern (LagrangianSystem _); whnf
    
  admit

def solver_0 (m k l : ℝ) (steps : Nat) : Impl (λ x v : Q => (L m k l) x v) :=
by
  simp [LagrangianSystem, L, L', parm, gradient]

  conv =>
    pattern (differential _); rmlamlet; enter [x, dx]; simp -- autodiff

  simp

  finish_impl


def solver_1 (m k l : ℝ) (steps : Nat) : Impl (λ x v : Q => ∇(swap (L m k l) v) x) :=
by
  conv in (L _ _ _) =>
    enter [θ, ω]
    simp [L, L', parm]
    rmlamlet
    simp

  simp [gradient]

  conv =>
    pattern (differential _); rmlamlet; enter [x, dx]; simp -- autodiff

  conv in (dual _) => 
    pattern (dual _); rmlamlet; simp  -- autodual

  .

  finish_impl
  
def solver_2 (m k l : ℝ) (steps : Nat) : Impl (λ x v : Q => ∇(∂ (L m k l) x v) v) :=
by

  conv in (L _ _ _) =>
    enter [θ, ω]
    simp [L, L', parm]
    rmlamlet
    simp

  conv => 
    pattern (differential _); enter [x, dx, y]; rmlamlet; simp -- autodiff (we need to introduce all arguments!)

  conv =>                                                     -- autograd - part1
    pattern (gradient _)
    enter [x]
    simp [gradient]
    pattern (differential _); enter [x, dx]; rmlamlet; simp   -- autodiff

  conv =>
    pattern (dual _); rmlamlet; simp                         -- autograd - part2

  .

  finish_impl

  
def solver_3 (m k l : ℝ) (steps : Nat) : Impl (λ x v : Q => ∂(∇((L m k l) x)) v) :=
by

  conv in (L _ _ _) =>
    simp [L, L', parm]
    { pattern (differential _); rmlamlet; enter [θ, ω]; simp }  -- autodiff
  
  simp -- Lagrangian is in a nice form now

  conv =>                                                     -- autograd - part1
    pattern (gradient _)
    enter [x]
    simp [gradient]
    pattern (differential _); enter [x, dx]; rmlamlet; simp   -- autodiff

  conv =>
    pattern (dual _); rmlamlet; simp                         -- autograd - part2

  conv => 
    pattern (differential _); enter [x, dx]; rmlamlet; simp -- autodiff
  
  conv => 
    enter [1,x,v]
    rmlamlet
    
  finish_impl
