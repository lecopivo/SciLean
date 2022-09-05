-- import SciLean.Basic
import SciLean.Core
import SciLean.Data.PowType
import SciLean.Functions.EpsNorm
import SciLean.Tactic.Basic

set_option synthInstance.maxSize 2048

open SciLean

def Fin.shift {n} (y : Int) (x : Fin n) : Fin n := ⟨(((x.1 + y) % n + n) % n).toNat, sorry⟩

instance Fin.shift.arg_x.isInv (y : Int) : IsInv (λ x : Fin n => x.shift y) := sorry
@[simp]
theorem Fin.shift.arg_x.inv_simp {n} [Nonempty (Fin n)] (y : Int)
  : (λ x : Fin n => x.shift y)⁻¹ = (λ x : Fin n => x.shift (-y)) := by sorry
  

def Fin.scale {n} (x : Fin n) (y : Nat) : Fin (y*n) := ⟨x.1*y, sorry⟩
def Fin.scaleUp {N n : Nat} (x : Fin (N/n)) : Fin N := ⟨x.1*n, sorry⟩

def relu (ε : ℝ) (x : ℝ) : ℝ := 0.5*(x + ∥x∥{ε})
argument x [Fact (ε≠0)]
  isSmooth, diff_simp

/-

  One dimensional convolution as an exmaple

 -/


-- variable {n N} (w : ℝ^{n}) (dx' : ℝ^{N}) [Nonempty (Fin N)] [Nonempty (Fin n)]

--- Dangerous because it applies on itself with `g=id`
-- @[simp]
theorem hihi {ι κ X} [Vec X] [Enumtype ι] [Enumtype κ] [Nonempty ι] [Nonempty κ]
  (g : ι → κ) [IsInv g]
  (h : ι → α)
  (f : κ → α → X) 
  : ∑ i, f (g i) (h i) = ∑ j, f j (h (g⁻¹ j))
  := sorry

#check SciLean.swap.arg_y.adj_simp

set_option trace.Meta.Tactic.simp.discharge true in
@[simp ↓ low+1]
theorem swap.arg_y.adj_simp_specialized {X Y Z} 
  [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] {ι} [Enumtype ι]
  (f : Y → Z) [HasAdjoint f] 
  (g : ι → X → Y) [∀ i, HasAdjoint (g i)]
  : (λ x i => f (g i x))† = λ (f' : ι → Z) => (λ x i => g i x)† (λ i => f† (f' i)) := 
by
  simp
  sorry
  -- TODO: Can I prove this with existing theorems???

example {Y Z ι κ : Type} 
  [SemiHilbert Y] [SemiHilbert Z] [Enumtype ι] [Enumtype κ]
  (f : ι → κ → Y → Z) [∀ i j, HasAdjoint (f i j)]
  : (λ y i j => f i j y)† = λ f' => ∑ i j, (f i j)† (f' i j)
  := 
by 
  conv => lhs; simp
  done

example {Y Z ι κ : Type} 
  [SemiHilbert Y] [SemiHilbert Z] [Enumtype ι] [Enumtype κ]
  (f : ι → κ → Y → Z) [∀ i j, HasAdjoint (f i j)]
  : (λ y i => ∑ j, f i j y )† = λ (y' : ι → Z) => ∑ i j, (f i j)† (y' i)
  := 
by 
  conv => lhs; simp
  done

set_option trace.Meta.Tactic.simp.rewrite true in
@[simp ↓ low+3]
theorem this_fixes_adj_x_of_convolution' {X Y ι κ : Type}
  [SemiHilbert X] [SemiHilbert Y] [Enumtype ι] [Enumtype κ] [Nonempty ι]
  (f : κ → ι → X → Y) [∀ i j, HasAdjoint (f i j)]
  (h : κ → ι → ι) [∀ j, IsInv (h j)]
  : (λ (g : ι → X) (j : κ) (i : ι) => f j i (g (h j i)))† 
    = 
    (λ g' i => ∑ j, (f j ((h j)⁻¹ i))† (g' j ((h j)⁻¹ i))) := 
by 
  conv => lhs; simp [sum_into_lambda]
  done

set_option trace.Meta.Tactic.simp.rewrite true in
@[simp ↓ low+3]
theorem this_fixes_adj_x_of_convolution {X Y ι κ : Type}
  [SemiHilbert X] [SemiHilbert Y] [Enumtype ι] [Enumtype κ] [Nonempty ι]
  (f : κ → ι → X → Y) [∀ i j, HasAdjoint (f i j)]
  (h : κ → ι → ι) [∀ j, IsInv (h j)]
  : (λ (g : ι → X) (i : ι) (j : κ) => f j i (g (h j i)))† 
    = 
    (λ g' i => ∑ j, (f j ((h j)⁻¹ i))† (g' ((h j)⁻¹ i) j)) :=
by 
  simp
  conv => 
    lhs
    simp only [sum_into_lambda]
    enter [g,i]
    rw [sum_swap]
    simp
  done

example {X Y ι κ : Type}
  [SemiHilbert X] [SemiHilbert Y] [Enumtype ι] [Enumtype κ] [Nonempty ι]
  (f : κ → ι → X → Y) [∀ i j, HasAdjoint (f i j)]
  (h : κ → ι → ι) [∀ j, IsInv (h j)]
  : (λ (g : ι → X) (i : ι) => ∑ j, f j i (g (h j i)))† 
    = 
    (λ g' i => ∑ j, (f j ((h j)⁻¹ i))† (g' ((h j)⁻¹ i))) := 
by 
  conv => lhs; simp
  done

set_option trace.Meta.Tactic.simp.discharge true in
@[simp ↓ low+3]
theorem this_fixes_adj_x_of_convolution'' {X Y ι κ : Type}
  [SemiHilbert X] [SemiHilbert Y] [Enumtype ι] [Enumtype κ] [Nonempty ι]
  (f : X → α → Y) [∀ a, HasAdjoint (λ x => f x a)]
  (ϕ : κ → ι → α) 
  (h : κ → ι → ι) [∀ j, IsInv (h j)]
  : (λ (g : ι → X) (i : ι) => ∑ j, f (g (h j i)) (ϕ j i))† 
    = 
    (λ g' i => ∑ j, (λ x => f x (ϕ j ((h j)⁻¹ i)))† (g' ((h j)⁻¹ i))) := by simp; admit

example {n N} [Nonempty (Fin N)] [Nonempty (Fin n)]  (w : Fin n → ℝ) 
  : (λ (x : Fin N → ℝ) (i : Fin N) => ∑ i', w i' * x (i.shift i'))†
    =
    (λ (x' : Fin N → ℝ) (i : Fin N) => ∑ i', w i' * x' (i.shift (-i'))) := 
by
  conv => lhs; simp
  done

example {n N} [Nonempty (Fin N)] [Nonempty (Fin n)]  (w : Fin n → ℝ) 
  : (λ (x : Fin N → ℝ) (i : Fin N) => ∑ (i' : Fin n), x (i.shift i') * w i')†
    =
    (λ (x' : Fin N → ℝ) (i : Fin N) => ∑ (i' : Fin n), x' (i.shift (-i')) * w i') :=
by
  conv => lhs; simp
  done

example {n N} [Nonempty (Fin N)] [Nonempty (Fin n)]  (w : Fin n → ℝ) 
  : (λ (x : Fin N → ℝ) (i : Fin N) => ∑ (i' : Fin n), w i' * x (i.shift i') * w i')†
    =
    (λ (x' : Fin N → ℝ) (i : Fin N) => ∑ (i' : Fin n), w i' * x' (i.shift (-i')) * w i') :=
by
  conv =>
    lhs
    simp[hold]
    enter [x']
    simp only [sum_into_lambda]
    enter [i]
    rw[sum_swap]
    simp
    simp only [kron_smul_assoc,sum_of_kron_2]
    simp
  done


@[simp ↓ low+3]
theorem this_fixes_adj_w_of_conv {X Y ι κ α : Type}
  [SemiHilbert X] [SemiHilbert Y] [Enumtype ι] [Enumtype κ] [Nonempty ι]
  (f : X → α → Y) [∀ a, HasAdjoint (λ x => f x a )]
  (h : ι → κ → α)
  : (λ (g : ι → X) (j : κ) => ∑ i, f (g i) (h i j))† 
    =
    (λ g' i => ∑ j, (λ x => f x (h i j))† (g' j)) := 
by
  conv => lhs; simp [sum_into_lambda]
  done

example {n N} [Nonempty (Fin N)] [Nonempty (Fin n)]  (x : Fin N → ℝ) 
  : (λ (w : Fin n → ℝ) (i : Fin N) => ∑ i', w i' * x (i.shift i'))† 
    = 
    (λ w' i' => ∑ i, w' i * x (i.shift i'))
    := 
by
  simp
  done

#check SciLean.eval.arg_x.parm1.adj_simp


example {N M} (i)
  : (λ (x : Fin N → Fin M → ℝ) => x i)† 
    = 
    λ (x' : Fin M → ℝ) j => kron i j  * x'
:= 
by 
  conv => lhs; simp
  done

example {N M} (j)
  : (λ (x : Fin N → Fin M → ℝ) i => x i j)† 
    = 0
    -- λ (x' : Fin N → ℝ) j' => kron j' j  * x'
:=
by
  conv =>
    lhs
    try { simp; done }  -- this should detect what we do not need the repeat anymore
    repeat' ext
    simp
  done


example {N M} (i j)
  : (λ (x : Fin N → Fin M → ℝ) => x i j)† 
    = 
    λ (x' : ℝ) i' j' => kron i i' * kron j j' * x'
:= 
by 
  conv => 
    lhs
    try { simp; done }  -- this should detect what we do not need the repeat anymore
    repeat' ext
    simp
  done



set_option trace.Meta.Tactic.simp.rewrite true in
example {N M n m} [Nonempty (Fin N)] [Nonempty (Fin M)] [Nonempty (Fin n)] [Nonempty (Fin m)]
  (w : Fin n → Fin m → ℝ) 
  : (λ (x : Fin N → Fin M → ℝ) i j => ∑ i' j',  w i' j' * x i j)†
    =
    (λ (x' : Fin N → Fin M→ ℝ) i j => ∑ i' j', w i' j' * x' (i.shift (-i')) (j.shift (-j'))) :=
    -- (λ (x' : Fin N → ℝ) (i : Fin N) => ∑ (i' : Fin n), x' (i.shift (-i')) * w i') :=
by
  conv => 
    lhs
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
  done



instance {n} [Fact (n≠0)] : Nonempty (Fin n) := sorry

-- def conv1d {N n} (x : ℝ^{N}) (w : ℝ^{n}) : ℝ^{N} := 
--   λ [i] => (∑ i', w[i'] * x[i.shift i'])
-- argument x [Fact (N≠0)] [Fact (n≠0)]
--   adjDiff by simp[conv1d]; rw[sum_swap]; simp; trace_state
-- argument w [Fact (N≠0)] [Fact (n≠0)]
--   adjDiff by simp[conv1d]; trace_state

def conv1d {N n} (x : Fin N → ℝ) (w : Fin n → ℝ) (b : ℝ) : Fin N → ℝ := 
   λ i => ∑ i', w i' * x (i.shift i') + b
argument x [Fact (N≠0)] [Fact (n≠0)]
  hasAdjDiff,
  adjDiff by 
    simp only [adjointDifferential]
    unfold conv1d; simp
argument w [Fact (N≠0)] [Fact (n≠0)]
  hasAdjDiff,
  adjDiff by
    simp only [adjointDifferential]
    unfold conv1d; simp
argument b [Fact (N≠0)] [Fact (n≠0)]
  hasAdjDiff,
  adjDiff by
    simp only [adjointDifferential]
    unfold conv1d; simp
 
set_option trace.Meta.Tactic.simp.rewrite true in   
def conv2d {N M n m} (x : Fin N → Fin M → ℝ) (w : Fin n → Fin m → ℝ) 
  : Fin N → Fin M → ℝ := 
  λ i j => (∑ i' j', w i' j' * x (i.shift i') (j.shift j'))
argument x [Fact (N≠0)] [Fact (M≠0)] [Fact (n≠0)] [Fact (m≠0)]
  adjDiff by
    simp only [adjointDifferential]
    unfold conv2d
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})

    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    simp (config := {singlePass := true})
    -- simp[conv2d] (config := {singlePass := true})
    -- simp[conv2d]
    -- rw[sum_swap]; simp; trace_state

#exit 
#check (∑ i j, setElem (0 : ℝ^{N}) (i.shift j) (w[j] * dx'[i]))
       rewrite_by  
         rw [sum_swap]
         simp



#exit

/-

  Convolutional layer for rank 3 tensors
    - sparse in the first and second dimensions
    - dense in the third dimension

 -/
def conv2d {N M n m l} (x : ℝ^{N, M}) (w : ℝ^{l, n, m}) (b : ℝ^{l}) : ℝ^{l, N, M} := 
  λ [k',i,j] => (∑ i' j', w[k', i', j'] * x[i.shift i', j.shift j']) + b[k']
argument x
  isSmooth, hasAdjDiff, adjDiff?
argument w
  isSmooth, hasAdjDiff, adjDiff?
argument b
  isSmooth, hasAdjDiff, adjDiff?


def fully_connected_rank3 {N M L n} (x : ℝ^{L, N, M}) (w : ℝ^{n, L, N, M}) (b : ℝ^{n}) : ℝ^{n} :=
  λ [i'] => (∑ i j k, w[i',i,j,k] * x[i,j,k]) + b[i']
argument x
  isSmooth, hasAdjDiff, adjDiff?
argument w
  isSmooth, hasAdjDiff, adjDiff?
argument b
  isSmooth, hasAdjDiff, adjDiff?

/-

  Dense layer for vectors - i.e. matrix vector multiply

 -/
def conv_d1 {N M : Nat} (x : ℝ^{M}) (w : ℝ^{N,M}) (b : ℝ^{N}) : ℝ^{N} := (λ [i] => (∑ j, w[i,j] * x[j]) + b[i])



/-

  Avererage pooling over the second and third dimension of rank 3 tensor

 -/
def avgpool2d (x : ℝ^{L, N, M}) : ℝ^{L, N/2, M/2} :=
  λ [k,i,j] => 0.25 * ∑ (di dj : Fin 2), x[k, i |>.scaleUp |>.shift di, j |>.scaleUp |>.shift dj]

def minst_clasifier (ε w) (x : ℝ^{16,16}) :=
    w |> 
    λ (w₁, b₁, w₂, b₂, w₃, b₃) =>
      x 
      |> (conv2d (l:=10) (n:=3) (m:=3) · w₁ b₁) 
      |> (avgpool2d ·)
      |>.map (relu ε)
      |> (conv2d (l:=10) (n:=3) (m:=3) · w₂ b₂) 
      |> (avgpool2d ·)
      |>.map (relu ε)
      |> (fully_connected_rank3 (n:=10) · w₃ b₃)

#check minst_clasifier



#exit 
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 500000
-- set_option maxRecDepth 5000
-- set_option maxHeartbeats 2000000
-- set_option maxCoeSize 500


set_option trace.Meta.synthInstance true in
instance {N} (i) (w : ℝ^{N}) : IsSmooth (λ (x : ℝ) => w[i]) :=
by 
  -- Why does this fail?
  infer_instance
  -- apply const.arg_y.isSmooth
  -- apply (@diag.arg_x.isSmooth _ _ _ _ _ _ _ _ _ _)
  done

#check PowTypeCarrier.intro

def avgpool2d {N M L} (x : ℝ^{N, M, L}) : ℝ^{N/2, M/2, L} := 
  .intro λ ((i,j), k) => 
    let i0 := ⟨2*i.1, sorry⟩
    let j0 := ⟨2*j.1, sorry⟩
    let i1 := ⟨2*i.1 + 1, sorry⟩
    let j1 := ⟨2*j.1 + 1, sorry⟩
    (x[((i0, j0), k)] + x[((i0, j1), k)] + x[((i1, j0), k)] + x[((i1, j1), k)])/4
argument x
  isLin, isSmooth, diff,
  hasAdjoint := sorry,
  adj := .intro λ ((i,j), k) => 
      let i' := ⟨i.1/2, sorry⟩
      let j' := ⟨j.1/2, sorry⟩
      x'[((i',j'),k)]/4 by sorry,
  hasAdjDiff, adjDiff


example : IsLin (λ (f : (Fin N × Fin M) × Fin L → ℝ) => (.intro f : ℝ^{N,M,L})) := by infer_instance
example (x : ℝ^{N,M,L}) (i j k) : IsLin (λ (x : ℝ^{N,M,L}) => x[((i,j), k)]) := by infer_instance
example (x : ℝ^{N,M,L}) (i j k) : IsLin (λ (x : ℝ^{N,M,L}) => x[((i,j), k)] + x[((i,j), k)]) := by infer_instance




def conv2d {n : ℕ} (m : ℕ) (w : ℝ^[3,3,m]) (b : ℝ^m) (x : ℝ^[n+2,n+2]) : ℝ^[n,n] := Id.run do
  let mut y : ℝ^[n,n] := 0
  y.mapIdx λ (i,j) => sorry

def maxpool {n m k : ℕ} (ε : ℝ) (x : ℝ^[2*n,2*m,2*k]) : ℝ^[n,m,k] := sorry

def neural_network 
  (w₁) (x : (ℝ^(28:ℕ))^(28:ℕ)) := x
  x |> 
  (λ x => conv2d 32 w₁ b₁ )

#check Nat

def foo := λ (x,y) => Math.sin x + Math.cos y

#check foo

/-

def conv311 {n m} (k : Nat) (x : NDVector [3,n,m]) (w : NDVector [3,1,1,k]) : NDVector [n,m,k] := sorry
def conv33  {n m} (k : Nat) (l : Nat) (x : NDVector [n,m,k]) (w : NDVector [3,3,k*l]) : NDVector [n,m,k*l] := sorry

def fully_connected {dims} (n : Nat) (x : NDVector dims) (w : NDVector [n, dims.product]) (b : NDVector [n]) : NDVector [n] := NDVector.lmk λ i => ∑ j, w[i,j] * x[j] + b[i]

def relu (ε : ℝ) (x : ℝ) : ℝ := (Math.sqrt (x*x + ε*ε) + x)/2

def my_activation (c : ℝ) (x : ℝ) : ℝ := Math.sin (x + c)

def maxpool {n m k} (ε : ℝ) (v : NDVector [n, m, k]) : NDVector [n/2,m/2,k] := sorry

def soft_max {dims} (β : ℝ) (v : NDVector dims) : NDVector dims := sorry

variable (ε β : ℝ)

def neural_network :=
--  λ w : NDVector [List.product [28, 28], 128] × NDVector [List.product [128], 10] =>
  λ (w1, w2, w3) => 
  λ (x : NDVector [28,28]) =>
  (x
   |>
   (λ x => (fully_connected 128 x w1).map (relu ε))
   |>
   (λ x => (fully_connected 128 x w2).map (relu ε))
   |>
   (λ x => soft_max β (fully_connected 10 x w3))
  )

#check neural_network

def uncurry_match_impl {α β γ} (f : α → β → γ) : (α × β → γ) :=
  λ p => 
    match p with
      | (x, y) => f x y


--- Making this part of `simp` gives later problems to `rmlamlet`
def prod_rec_is_uncurry {α β γ} : (Prod.rec (motive := λ _ => γ) : (α → β → γ) → (α × β → γ)) = uncurry := 
by
  apply Eq.trans (b := uncurry_match_impl)

  . funext f p
    simp [uncurry_match_impl, uncurry_match_impl.match_1]

  . funext f p
    induction p
    simp [uncurry, uncurry_match_impl]

  done

def abs_eps (ε : ℝ) (x : ℝ) : ℝ := Math.sqrt (x*x + ε*ε)
def log_eps (ε : ℝ) (x : ℝ) : ℝ := (1/2) * Math.log (x*x + ε*ε)

def cross_entropy_eps {dims} (ε : ℝ) (p q : NDVector dims) : ℝ := 
  - ∑ i : Fin dims.product, (p.lget! i) * log_eps ε (q.lget! i)
  
def heheho 
    : Impl (λ image label w =>
              let F := λ w => cross_entropy_eps ε ((neural_network ε β) w image) label
              †(∂ F w) 1) 
    := sorry

  
  

#check uncurry

#check Nat


    
def heheh {w dw x} : Impl (∂ (neural_network ε β) w dw x) := 
by
  simp[neural_network,neural_network.match_1]

  repeat rw [prod_rec_is_uncurry]

  rmlamlet
  
  conv =>
    repeat (first | pattern (uncurry _); enter [1] | pattern (uncurry _))
    
    rmlamlet

  finish_impl
  

-- def foo_grad  : bar = (Prod.fst : ℝ×ℝ→ℝ) := 
-- by
--   simp [bar]
--   simp [bar.match_1]
--   funext x
--   simp [Prod]
  


-- #check Prod.rec

-- #check @Prod.rec

-- def foo_grad : Impl (∂ foo) :=
-- by
--   conv =>
--     enter [1,p,dp]
--     simp  [foo]
--     simp  [foo.match_1]
--     enter [1,x,1,a,b]
--     rmlamlet

--     print_main_goal
    
    
-/
