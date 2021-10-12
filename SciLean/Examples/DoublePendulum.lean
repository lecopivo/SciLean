import SciLean.Basic
import SciLean.Mechanics

set_option synthInstance.maxHeartbeats 50000
set_option synthInstance.maxSize 10000

abbrev V := (ℝ × ℝ) × (ℝ × ℝ)
abbrev Q := ℝ × ℝ

def g : ℝ := 9.81
def L' (m : ℝ×ℝ) (x v : V) := 
    let x₁ := x.1
    let x₂ := x.2
    let v₁ := v.1
    let v₂ := v.2
    (m.1/2) * ⟨v₁,v₁⟩ + (m.2/2) * ⟨v₂,v₂⟩ - m.1 * g * x₁.2 - m.2 * g * x₂.2

def parm (l : ℝ×ℝ) (θ : Q) : V :=
  let θ₁ := θ.1
  let θ₂ := θ.2
  let x₁ := l.1 * (Math.sin θ₁, Math.cos θ₁)
  let x₂ := x₁ + l.2 * (Math.sin θ₂, Math.cos θ₂)
  (x₁, x₂)


def PureImpl {α} (a : α → Prop) := α
def pure_impl {α} {a : α} : PureImpl (Eq a) := a

def L (m l : ℝ×ℝ) (θ ω : Q) : PureImpl (Eq (L' m (parm l θ) (δ (parm l) θ ω))) :=
by
  conv =>
    enter [1]
    simp [L', parm]
    pattern (differential _); rmlamlet; enter [θ, ω]; simp

  simp
  
  apply pure_impl

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
  
def solver_2 (m k l : ℝ) (steps : Nat) : Impl (λ x v : Q => ∇(δ (L m k l) x v) v) :=
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

  
def solver_3 (m k l : ℝ) (steps : Nat) : Impl (λ x v : Q => δ(∇((L m k l) x)) v) :=
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
