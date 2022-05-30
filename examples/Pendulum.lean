import SciLean
-- import SciLean.Mechanics

-- import Lean.Meta.Tactic

set_option synthInstance.maxHeartbeats 5000000
set_option synthInstance.maxSize 2048

open SciLean

abbrev V := (ℝ^(3:ℕ)) × (ℝ^(3:ℕ))

def ε : ℝ := 0.001
instance : Fact (ε≠0) := Fact.mk (by native_decide)

abbrev parm2 (l₁ l₂ : ℝ) (Ω : V) : V :=
  let e : ℝ^(3:ℕ) := ⟨0,-1,0⟩
  let Δx₁ := rotate3d Ω.1 (l₁ * e)
  let Δx₂ := rotate3d Ω.2 (l₂ * e)
  (Δx₁, Δx₁ + Δx₂)

abbrev parm (l : ℝ) (Ω : ℝ^(3:ℕ)) : ℝ^(3:ℕ) :=
  have e : ℝ^(3:ℕ) := ⟨0,-1,0⟩
  εrotate ε Ω (l * e)


@[simp]
theorem pair_add {X Y} [Add X] [Add Y] (x x' : X) (y y' : Y) : (x, y) + (x', y') = (x + x', y + y') := by simp[HAdd.hAdd, Add.add] done

def L2 (m₁ m₂ : ℝ) (l₁ l₂ : ℝ) (Ω ω : V) := 
  let g : ℝ := 9.81
  let x := parm2 l₁ l₂ Ω
  let v := ω -- δ (λ t : ℝ => parm l₁ l₂ (Ω + t * ω)) 0 1
    -- rewrite_by (simp[parm])
  1/(2*m₁) * ∥v.1∥² - m₁ * g * x.1.y + 
  1/(2*m₂) * ∥v.2∥² - m₂ * g * x.2.y

def g : ℝ := 9.81

-- example (x : Float) : x + 0.1 = 0.1 + x := by simp

def L (m : ℝ) (l : ℝ) (Ω ω : ℝ^(3:ℕ)) : ℝ := 
  -- let g : ℝ := 9.81
  let e : ℝ^(3:ℕ) := ⟨0,-1,0⟩
  let x := parm l Ω
  let v := δ (λ t : ℝ => parm l (Ω + t * ω)) 0 1
    rewrite_by (simp[parm])
  m/2 * ∥v∥² - m * g * x.y
argument Ω
  isSmooth, diff, 
  hasAdjDiff, adjDiff
argument ω
  isSmooth, diff, hasAdjDiff, adjDiff

-- argument ω
--   isSmooth, diff, hasAdjDiff, adjDiff

#check Nat

example : IsSmooth (λ ω dω Ω => εrotate.arg_ω.diff ε ω dω Ω) := by apply εrotate.arg_ω.diff.arg_ω.isSmooth

example (dω Ω) : IsSmooth (λ ω => εrotate.arg_ω.diff ε ω dω Ω) := by infer_instance

#check εrotate.arg_ω.diff.arg_ω.isSmooth

#print L.arg_Ω.adjDiff


def momentum (m : ℝ) (l : ℝ) (Ω ω : ℝ^(3:ℕ)) : ℝ^(3:ℕ) :=
  (δ† (λ ω' => L m l Ω ω') ω 1)
  rewrite_by
    simp

function_properties εrotate.arg_ω.diff (ε : ℝ) [Fact (ε≠0)] (ω dω x : ℝ^(3:ℕ)) : ℝ^(3:ℕ)
argument dω
  inv by simp[εrotate.arg_ω.diff]

  


def velocity (m : ℝ) (l : ℝ) (Ω ω' : ℝ^(3:ℕ)) : ℝ^(3:ℕ) := 
  ((λ ω => momentum m l Ω ω)⁻¹ ω')
  rewrite_by
    simp[momentum]
    simp[L.arg_ω.adjDiff]



def solver (m l : ℝ) (steps : Nat) : Impl (ode_solve (LagrangianSystem (L m l))) :=
by

  

  conv in (L _ _) =>
    simp [L, L', parm]
    { pattern (differential _); rmlamlet; enter [θ, ω]; simp }  -- autodiff
  
  simp -- Lagrangian is in a nice form now

  conv => 
    pattern (LagrangianSystem _); whnf

  simp
  
  --------------------- mass matrix ---------------------------------
  conv =>   -- autograd par1
    repeat' (enter [1]; pattern (gradient _))
    simp [gradient]
    pattern (differential _)
    rmlamlet
    repeat' (ext x);
    simp

  conv =>   -- autograd part2
    pattern (comp dual _)
    ext x; simp
    pattern (dual _)
    rmlamlet
    simp

  conv =>  -- autodiff
    repeat' enter [1]; pattern (differential _)
    rmlamlet
    repeat' (ext x)
    simp

  .
  
  ------- potential forces ----
  conv =>   -- autograd par1
    repeat' (enter [1]; pattern (gradient _))
    simp [gradient]
    pattern (differential _)
    rmlamlet
    repeat' (ext x);
    simp

  conv =>   -- autograd part2
    pattern (comp dual _)
    ext x; simp
    pattern (dual _)
    rmlamlet
    simp

  .

  ------- geometry forces ----
  conv =>  -- autodiff
    repeat' enter [1]; pattern (differential _)
    rmlamlet
    repeat' (ext x)
    simp

  conv =>   -- autograd par1
    repeat' (enter [1]; pattern (gradient _))
    simp [gradient]
    pattern (differential _)
    rmlamlet
    repeat' (ext x);
    simp

  conv =>   -- autograd part2
    pattern (comp dual _)
    ext x; simp
    pattern (dual _)
    rmlamlet
    simp

  .

  ------- TODO: invert ------


  ------- TODO: ode_solve --------

  admit

