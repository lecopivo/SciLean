import SciLean

open SciLean Scalar RealScalar



@[simp ↓ high, simp_core ↓ high]
theorem hihih
  {R : Type} [RCLike R]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [PlainDataType X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {I : Type} [IndexType I]
  (f : DataArrayN X I → Y)  :
  revFDeriv R f
  =
  fun x =>
    let ydf := revFDerivProj R Unit f x
    (ydf.1, ydf.2 ()) := by unfold revFDerivProj revFDeriv; simp


@[fun_trans]
theorem hohoe {n:Nat} (i : Fin n) :
  revFDerivProjUpdate Float Unit (fun (x : Float^[n]) => x[i])
  =
  fun x =>
    (ArrayType.get x i,
     fun _ dxi y => ArrayType.modify y i (· + dxi)) := sorry

#check fun (i : Fin 10 × Unit) =>
            (?inst : (i : Unit) → NormedAddCommGroup ((?EI : Unit → Type) i))
              i.2



set_default_scalar Float
variable (u : Float^[10])
-- set_option trace.Meta.Tactic.fun_trans true in
set_option trace.Meta.Tactic.fun_trans.unify true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
-- set_option pp.funBinderTypes true in
-- set_option pp.mvars.withType true in

set_option trace.Meta.isDefEq true in

#check (∇ (u':=u), ∑ i, u'[i]^2) rewrite_by
  unfold fgradient
  autodiff
  simp
  pattern (revFDerivProjUpdate _ _ _)
  rw[SciLean.revFDerivProjUpdate.pi_rule (K:=Float) (I:=Unit) (f:=fun (x : Float^[10]) i => x[i]^2) (hf:=by fun_prop)]




-- =?= fun (i : Fin 10 × Unit) => NonUnitalNormedRing.toNormedAddCommGroup

#exit
-- __      __       _   _                    _ _   _
-- \ \    / /__ _ _| |_(_)_ _  __ _  __ __ _(_) |_| |_
--  \ \/\/ / _ \ '_| / / | ' \/ _` | \ V  V / |  _| ' \
--   \_/\_/\___/_| |_\_\_|_||_\__, |  \_/\_/|_|\__|_||_|
--                            |___/
--    _
--   /_\  _ _ _ _ __ _ _  _ ___
--  / _ \| '_| '_/ _` | || (_-<
-- /_/ \_\_| |_| \__,_|\_, /__/
--                     |__/
section WorkingWithArrays


--  _    _ _                _     _
-- | |  (_) |_ ___ _ _ __ _| |   /_\  _ _ _ _ __ _ _  _ ___
-- | |__| |  _/ -_) '_/ _` | |  / _ \| '_| '_/ _` | || (_-<
-- |____|_|\__\___|_| \__,_|_| /_/ \_\_| |_| \__,_|\_, /__/
--                                                 |__/

-- List
#check [1.0, 2.0]
-- Array
#check #[1.0, 2.0]

-- Mathlib's vector
#check ![1.0, 2.0]
-- Mathlib's matrix
#check !![1.0, 2.0; 3.0, 4.0]

-- SciLean's vector
#check ⊞[1.0, 2.0]
#eval  ⊞[1.0, 2.0]

-- SciLean's matrix
#check ⊞[1.0, 2.0; 3.0, 4.0]
#eval  ⊞[1.0, 2.0; 3.0, 4.0]


--  ___ _                   _       _
-- | __| |___ _ __  ___ _ _| |_    /_\  __ __ ___ ______
-- | _|| / -_) '  \/ -_) ' \  _|  / _ \/ _/ _/ -_|_-<_-<
-- |___|_\___|_|_|_\___|_||_\__| /_/ \_\__\__\___/__/__/

def u := ⊞[1.0, 2.0]
def A := ⊞[1.0, 2.0; 3.0, 4.0]

-- element access
#eval u[1]
#eval A[0,1]

-- automatic index type inference
#check fun i => u[i]
#check fun i j => A[i,j]
#check fun ij => A[ij]
#check fun (i,j) => A[i,j]

#eval ∑ i, u[i]
#eval ∑ i j, A[i,j]
#eval ∏ ij, A[ij]

-- lambda notation for arrays
#check ⊞ (i : Fin 4) => i.1.toFloat
#eval  ⊞ (i : Fin 4) => i.1.toFloat

-- lambda notation for matrices
#check  ⊞ (i j : Fin 4) => i.1.toFloat + 4 * j.1.toFloat
#eval   ⊞ (i j : Fin 4) => i.1.toFloat + 4 * j.1.toFloat

-- beware nested lambda notation creates vector of vectors
#check ⊞ (i : Fin 4) => ⊞ (j : Fin 4) => i.1.toFloat + 4 * j.1.toFloat


-- imperative code to create vector
def array1 := Id.run do
  let mut x : Float^[4] := 0
  for i in fullRange (Fin 4) do
    x[i] := i.1.toFloat
  return x

#check array1
#eval  array1

-- using standard range notation is cumbersome right now
def array2 := Id.run do
  let mut x : Float^[4] := 0
  for h : i in [0:4] do
    let i : Fin 4 := ⟨i, by simp_all [Membership.mem]⟩
    x[i] := i.1.toFloat
  return x

-- imperative code to create matrix
def matrix1 := Id.run do
  let mut A : Float^[4,4] := 0
  for (i,j) in fullRange (Fin 4 × Fin 4) do
    A[i,j] := i.1.toFloat + 4 * j.1.toFloat
  return A

#check matrix1
#eval  matrix1


-- dot product for vectors
def dot {n : Nat} (x y : Float^[n]) : Float := ∑ i, x[i] * y[i]
def matMul {n m : Nat} (A : Float^[n,m]) (x : Float^[m]) : Float^[n] := ⊞ i => ∑ j, A[i,j] * x[j]

#eval dot u u
#eval matMul A u

-- dimension mismatch
#check_failure dot u A
#check_failure matMul A A

-- not general enough in the index type
#check_failure dot A A


--   ___                       _   ___         _
--  / __|___ _ _  ___ _ _ __ _| | |_ _|_ _  __| |_____ __
-- | (_ / -_) ' \/ -_) '_/ _` | |  | || ' \/ _` / -_) \ /
--  \___\___|_||_\___|_| \__,_|_| |___|_||_\__,_\___/_\_\

-- explain syntactic sugar Float^[n,m]
example : Float^[2] = DataArrayN Float (Fin 2) := by rfl
example : Float^[2] = Float^[Fin 2] := by rfl

#check Float^[Fin 2 × Fin 2]
#check Float^[Fin 2 ⊕ Fin 3]
#check Float^[(Fin 2 ⊕ Fin 3) × Set.Icc (-2:ℤ) (2:ℤ)]

example : IndexType (Fin 2 × Fin 2) := by infer_instance
example : IndexType (Fin 2 ⊕ Fin 3 × Set.Icc (-2:ℤ) (2:ℤ)) := by infer_instance

-- 2 * 5^0 + 3 * 5^1 + 1 * 5^2
#eval IndexType.toFin ((2, 3, 1) : Fin 5 × Fin 5 × Fin 5)

-- example of using more complicated indices
#eval ⊞ (i : Set.Icc (-2:ℤ) (2:ℤ)) => Float.ofInt i.1

#eval ⊞ (i : Fin 2 ⊕ Fin 3) =>
          match i with
          | .inl i => i.1.toFloat
          | .inr j => 100 * j.1.toFloat

#check ⊞ (i : (Fin 2 ⊕ Fin 3) × Set.Icc (-2:ℤ) (2:ℤ) × Fin 2) =>
           (IndexType.toFin i).1.toFloat


-- generalized dot
variable {I J : Type} [IndexType I] [IndexType J]
def dot' (x y : Float^[I]) : Float := ∑ i, x[i] * y[i]

#eval dot' u u
#eval dot' A A

-- eneralized matMul
def matMul' (A : Float^[I,J]) (x : Float^[J]) : Float^[I] := ⊞ i => ∑ j, A[i,j] * x[j]

#eval matMul' A u

-- initialize rank 3 tensor T
def T := ⊞ (i j k : Fin 2) => i.1.toFloat + 2 * j.1.toFloat + 4 * k.1.toFloat

-- test dot on T
#eval dot' T T

-- test matMul on T
-- it works because (T : Float^[Fin 2 × (Fin 2 × Fin 2)]) (A : Float^[Fin 2 × Fin 2])
-- thuse we have (I := Fin 2) (J := Fin 2 × Fin 2)
#eval matMul' T A


-- imprative style implementation of matMul
def matMul'' (A : Float^[I,J]) (x : Float^[J]) : Float^[I] := Id.run do
  let mut y : Float^[I] := 0
  for i in fullRange I do
    for j in fullRange J do
      y[i] += A[i,j] * x[j]
  return y

#eval matMul'' T A


end WorkingWithArrays

--    _       _                  _   _
--   /_\ _  _| |_ ___ _ __  __ _| |_(_)__
--  / _ \ || |  _/ _ \ '  \/ _` |  _| / _|
-- /_/ \_\_,_|\__\___/_|_|_\__,_|\__|_\__|
--  ___  _  __  __                 _   _      _   _
-- |   \(_)/ _|/ _|___ _ _ ___ _ _| |_(_)__ _| |_(_)___ _ _
-- | |) | |  _|  _/ -_) '_/ -_) ' \  _| / _` |  _| / _ \ ' \
-- |___/|_|_| |_| \___|_| \___|_||_\__|_\__,_|\__|_\___/_||_|

section AutomaticDifferentiation


--   __    _         _
--  / _|__| |___ _ _(_)_ __
-- |  _/ _` / -_) '_| \ V /
-- |_| \__,_\___|_| |_|\_/

section FDeriv

variable (x₀ : ℝ)

-- mathlib's fderiv
#check (fderiv ℝ (fun x : ℝ => x*x*x) x₀ 1) rewrite_by autodiff

set_default_scalar ℝ

-- nice notation for derivative
#check (∂ x : ℝ, (x*x*x + x*x)) rewrite_by autodiff

#check (∂ (x:=x₀), (x*x*x + x*x)) rewrite_by autodiff

#check (∂ (x:=x₀), (sin x + exp x + cos x)) rewrite_by autodiff


-- differentiating more complicated expressions
#check (∂ (x:=x₀), ∑ (i : Fin 10), sin (x^i.1)) rewrite_by autodiff

-- differentiating w.r.t to vector or matrix arguments
variable {n : Nat} (i : Fin n)
variable (A dA : Fin n → Fin n → ℝ) (u du v dv : Fin n → ℝ)

#check (∂ (u':=u;du), ∑ j, A i j * u' j) rewrite_by autodiff
#check (∂ (A':=A;dA), ∑ j, A' i j * u j) rewrite_by autodiff
#check (∂ ((A',u'):=(A,u);(dA,du)), ∑ j, A' i j * u' j) rewrite_by autodiff

-- right now this is really slow for some reason :(
-- #check (∂ (A':=A;dA), (fun i => ∑ j, A' i j * ∑ k, A' j k * u k)) rewrite_by autodiff


-- differentiationg w.r.t arrays
set_default_scalar Float
variable (A dA : Float^[n,n]) (u du v dv : Float^[n])

#check (∂ (u':=u;du), (⊞ i => ∑ j, A[i,j] * u'[j] )) rewrite_by autodiff
#check (∂ (A':=A;dA), (⊞ i => ∑ j, A'[i,j] * u[j] )) rewrite_by autodiff

-- right now this is extremely slow for some reason :(
-- #check (∂ ((A',u'):=(A,u);(dA,du)), (⊞ i => ∑ j, A'[i,j] * u'[j] )) rewrite_by autodiff
-- #check (∂ (A':=A;dA), (⊞ i => ∑ j, A'[i,j] * ∑ k, A'[j,k]*u[k] )) rewrite_by autodiff

set_default_scalar ℝ

-- differentiating division, log
set_option trace.Meta.Tactic.fun_trans true in
#check (∂ (x:=x₀), (exp x / x)) rewrite_by autodiff

variable (h : x₀ ≠ 0)
#check (∂ (x:=x₀), (exp x / x)) rewrite_by assuming autodiff

#check (∂ (x:=x₀), (exp x / (x*x))) rewrite_by assuming (h : x₀ ≠ 0) autodiff (disch:=assumption)

#check (∂ (x:=x₀), exp x / (x^2 - 3*x + 1)) rewrite_by assuming (h : ∀ x : ℝ, x≠0) autodiff (disch:=apply h)

#check (∂ (x:=x₀), exp x / (x^2 - 3*x + 1)) rewrite_by assuming (h : x₀ ^ 2 - 3 * x₀ + 1 ≠ 0) autodiff (disch:=apply h)

#check (∂ (x:=x₀), log (x^n)) rewrite_by autodiff (disch:=aesop)


end FDeriv
--                   _ _         _
--  __ _ _ _ __ _ __| (_)___ _ _| |_
-- / _` | '_/ _` / _` | / -_) ' \  _|
-- \__, |_| \__,_\__,_|_\___|_||_\__|
-- |___/

section Gradient
set_default_scalar ℝ
variable (x : ℝ)

#check (∇ (x':=x), x'*x'*x') rewrite_by autodiff

-- Taking gradient w.r.t. to matrix and vector
variable {n : Nat} (A dA : Fin n → Fin n → ℝ) (u du v dv : Fin n → ℝ) (i : Fin n)
-- ∇_u ‖u‖₂² = 2•u
#check (∇ (u':=u), ‖u'‖₂²) rewrite_by autodiff
-- ∇_u ⟪u,v⟫ = v
#check (∇ (u':=u), ⟪u',v⟫) rewrite_by autodiff


-- ∇_u u[i] = [0,...,1,...,0]
#check (∇ (u':=u), u' i) rewrite_by autodiff

-- accessing elements does not work properly yet
-- ∇_u (∑ i, uᵢ²) = ∇_u ‖u‖₂² = 2 • u
#check (∇ (u':=u), ∑ i, u' i^2) rewrite_by autodiff


set_default_scalar Float
variable (A dA : Float^[3,3]) (u du : Float^[3])

-- ∇_u u[i] = [0,...,1,...,0]
#check (∇ (u':=u), u'[1]) rewrite_by autodiff
#eval (∇ (u':=u), u'[1]) rewrite_by autodiff


-- ∇_A trace(A) = I
#check (∇ (A':=A), ∑ i, A'[i,i]) rewrite_by autodiff
#eval  (∇ (A':=A), ∑ i, A'[i,i]) rewrite_by autodiff



end Gradient

--  ___                           _                _
-- | __|__ _ ___ __ ____ _ _ _ __| |  __ _ _ _  __| |
-- | _/ _ \ '_\ V  V / _` | '_/ _` | / _` | ' \/ _` |
-- |_|\___/_|  \_/\_/\__,_|_| \__,_| \__,_|_||_\__,_|
--  ___                           __  __         _
-- | _ \_____ _____ _ _ ___ ___  |  \/  |___  __| |___
-- |   / -_) V / -_) '_(_-</ -_) | |\/| / _ \/ _` / -_)
-- |_|_\___|\_/\___|_| /__/\___| |_|  |_\___/\__,_\___|


set_default_scalar ℝ
variable
  {X : Type _} [NormedAddCommGroup X] [AdjointSpace ℝ X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [AdjointSpace ℝ Y] [CompleteSpace Y]

variable (f : X → Y) (x dx : X)

-- definition of fwdFDeriv, revFDeriv
example : fwdFDeriv ℝ f x dx = (f x, fderiv ℝ f x dx) := by rfl
example : revFDeriv ℝ f x    = (f x, adjoint ℝ (fderiv ℝ f x)) := by rfl

-- notation for fwdFDeriv and revFDeriv
example : fwdFDeriv ℝ f x dx = ∂> (x':=x;dx), f x' := by rfl
example : revFDeriv ℝ f x    = <∂ (x':=x), f x' := by rfl

variable (g : X → ℝ)
-- gradient is just revFDeriv
example : ∇ (x':=x), g x' = (<∂ (x':=x), g x').2 1 := by rfl


#check (∂> (x : ℝ), x^3) rewrite_by autodiff
#check (<∂ (x : Fin 10 → ℝ), ‖x‖₂²) rewrite_by autodiff


#check (∂> (x : ℝ),
           let t1 := x^2
           let t2 := t1^3
           let t3 := t2^4
           let t4 := t3^5
           t4) rewrite_by autodiff

#check (<∂ (x : ℝ),
           let t1 := x^2
           let t2 := t1^3
           let t3 := t2^4
           let t4 := t3^5
           t4) rewrite_by autodiff


set_default_scalar Float

#check (∂> (x : Float^[10]),
           let mean := ∑ i, x[i]
           let var := (1.0/9.0) * ∑ i, (x[i] - mean)^2
           var) rewrite_by autodiff

#check (<∂ (x : Float^[10]),
           let mean := ∑ i, x[i]
           let var := (1.0/9.0) * ∑ i, (x[i] - mean)^2
           var) rewrite_by autodiff

set_default_scalar ℝ


--  _   _               ___       __ _             _
-- | | | |___ ___ _ _  |   \ ___ / _(_)_ _  ___ __| |
-- | |_| (_-</ -_) '_| | |) / -_)  _| | ' \/ -_) _` |
--  \___//__/\___|_|   |___/\___|_| |_|_||_\___\__,_|
--  ___             _   _
-- | __|  _ _ _  __| |_(_)___ _ _  ___
-- | _| || | ' \/ _|  _| / _ \ ' \(_-<
-- |_| \_,_|_||_\__|\__|_\___/_||_/__/

-- define new function foo
noncomputable
def foo (x : ℝ) := x * exp x

-- by default `autodiff` can't see through definitions
#check (∂ x, foo x) rewrite_by
  autodiff -- nothing happens
  unfold foo
  autodiff

-- define new function transformation with `def_fun_trans`
def_fun_trans : fderiv ℝ foo by unfold foo; autodiff

-- check the new definition and theorem
#print foo.arg_x.fderiv
#check foo.arg_x.fderiv_rule

-- define function transformations for forward and reverse mode AD
def_fun_trans : ∂> foo by unfold foo; autodiff
def_fun_trans : <∂ foo by unfold foo; autodiff

-- `∇ foo`, `deriv foo` and `∂ foo` do not work as they are not merked as function transformations
-- def_fun_trans : ∇ foo by unfold foo; autodiff
-- def_fun_trans : deriv foo by unfold foo; autodiff
-- def_fun_trans : ∂ foo by unfold foo; autodiff

-- check that AD works now
#check (∂ x, foo x) rewrite_by autodiff

-- however nesting does not work, why?
set_option trace.Meta.Tactic.fun_trans true in
#check (∂ x, foo (foo x)) rewrite_by autodiff

-- define new function proposition
def_fun_prop with_transitive : Differentiable ℝ foo by unfold foo; fun_prop

-- check new theorem and demonstrate `with_transitive` keyword
#check foo.arg_x.Differentiable_rule



--  ___             _   _
-- | __|  _ _ _  __| |_(_)___ _ _
-- | _| || | ' \/ _|  _| / _ \ ' \
-- |_| \_,_|_||_\__|\__|_\___/_||_|
--  _____                  __                    _   _
-- |_   _| _ __ _ _ _  ___/ _|___ _ _ _ __  __ _| |_(_)___ _ _
--   | || '_/ _` | ' \(_-<  _/ _ \ '_| '  \/ _` |  _| / _ \ ' \
--   |_||_| \__,_|_||_/__/_| \___/_| |_|_|_\__,_|\__|_\___/_||_|


-- SciLean provides general tactic `fun_trans` for function transformation
-- inspired by JAX

-- `autodiff` is just `fun_trans` with custom settings

-- define custom derivative
@[fun_trans]
noncomputable
def myderiv (f : ℝ → ℝ) (x : ℝ) := fderiv ℝ f x 1


-- basic lambda calculus rules

-- identity rule: d/dx x = 1
@[fun_trans]
theorem id_rule : myderiv (fun x : ℝ => x) = fun x => 1 := by unfold myderiv; fun_trans

-- constant rule: d/dx constant = 0
@[fun_trans]
theorem const_rule (y : ℝ) : myderiv (fun x : ℝ => y) = fun x => 0 := by unfold myderiv; fun_trans

-- chain/composition rule: (f(g(x)))' = f'(g(x))*g'(x)
@[fun_trans]
theorem comp_rule (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
  myderiv (fun x => f (g x))
  =
  fun x => myderiv f (g x) * myderiv g x := by unfold myderiv; fun_trans[mul_comm]


-- derivative rules for operations

-- addition rule: (f + g)' = f' + g'
@[fun_trans]
theorem add_rule (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
  myderiv (fun x => f x + g x)
  =
  fun x => myderiv f x + myderiv g x := by unfold myderiv; fun_trans


-- multiplication/Leibnitz rule: (f*g)' = f'*g + f*g'
@[fun_trans]
theorem mul_rule (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
  myderiv (fun x => f x * g x)
  =
  fun x => myderiv f x * g x + f x * myderiv g x := by unfold myderiv; fun_trans[mul_comm,add_comm]


-- test `myderiv` with `fun_trans`
#check (myderiv (fun x : ℝ => x*x*x*x + x*x)) rewrite_by fun_trans






  -- conv =>
  --   pattern revFDerivProjUpdate _ _ _
  --   rw [revFDerivProjUpdate.pi_rule (K:=Float) (ι:=Fin 10) (I:=Unit) (f:=fun (x :Float^[10]) i => x[i]^2) (hf:=by fun_prop)]
  -- autodiff

  -- autodiff
  -- simp
  -- enter [1,dx,i]
  --
  -- autodiff


end AutomaticDifferentiation
