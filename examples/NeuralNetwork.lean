-- import SciLean.Basic
import SciLean.Core
import SciLean.Data.PowType
import SciLean.Functions.EpsNorm
import SciLean.Functions.Convolution
import SciLean.Tactic.Basic

set_option synthInstance.maxSize 2048
-- set_option synthInstance.maxHeartbeats 20000

open SciLean

def relu (ε : ℝ) (x : ℝ) : ℝ := 0.5*(x + ∥x∥{ε})
argument x [Fact (ε≠0)]
  isSmooth, diff_simp, hasAdjDiff, adjDiff_simp

/-

  Convolutional layer for rank 3 tensors
    - sparse in the first and second dimensions
    - dense in the third dimension

 -/
-- def conv2d {N M n m l} (x : ℝ^{N, M}) (w : ℝ^{l, n, m}) (b : ℝ^{l}) : ℝ^{l, N, M} := 
--   λ [k',i,j] => (∑ i' j', w[k', i', j'] * x[i.shift i', j.shift j']) + b[k']

instance comp_with_index_has_adjDiff {X Y Z : Type} 
  [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] {ι : Type} [Enumtype ι]
  (f : Y → Z) [HasAdjDiff f] 
  (g : ι → X → Y) [∀ i, HasAdjDiff (g i)]
  : HasAdjDiff (λ x i => f (g i x)) := by sorry

instance comp_with_index_has_adjDiff' {X Y Z : Type} 
  [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]  {ι : Type} [Enumtype ι]
  (f : Y → α → ι → Z) [HasAdjDiff (λ y => f y a)] 
  (g : ι → X → Y) [∀ i, HasAdjDiff (g i)]
  : HasAdjDiff (λ x i => f (g i x) a i) := by sorry

instance comp_with_index_has_adjDiff'' {X Y Z : Type} 
  [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]  {ι : Type} [Enumtype ι]
  (f : Y → α → β → ι → Z) [HasAdjDiff (λ y => f y a b)] 
  (g : ι → X → Y) [∀ i, HasAdjDiff (g i)]
  : HasAdjDiff (λ x i => f (g i x) a b i) := by sorry

namespace SciLean.Tensor

  -- def transpose {N M} (x : ℝ^{N, M}) : ℝ^{M, N} := 
  --   λ [i,j] => x[j,i]
  -- argument x
  --   adjDiff by simp[transpose]

  -- set_option trace.Meta.synthInstance true in
  -- example {N n : Nat} [Fact (N≠0)] [Fact (n≠0)] (w : Fin n → ℝ) (b : ℝ) 
  --   : IsSmooth fun (x : ℝ^{N}) => SciLean.conv1d (λ i => x[i]) w b
  --   := by infer_instance


  -- set_option trace.Meta.synthInstance true in
  example {N n : Nat} [Fact (N≠0)] [Fact (n≠0)] (w : Fin n → ℝ) (b : ℝ) 
    : HasAdjDiff fun (x : Fin N → ℝ) => SciLean.conv1d x w b
    := by infer_instance -- apply comp_with_index_has_adjDiff

  set_option synthInstance.maxHeartbeats 500 in 
  -- set_option trace.Meta.synthInstance true in
  example {N n : Nat} [Fact (N≠0)] [Fact (n≠0)] (w : Fin n → ℝ) (b : ℝ) 
    : HasAdjDiff fun (x : ℝ^{N}) i => SciLean.conv1d (fun i' => x[i']) w b i
    := by infer_instance

  set_option synthInstance.maxHeartbeats 500 in 
  -- set_option trace.Meta.synthInstance true in
  -- set_option trace.Meta.Tactic.simp.discharge true in
  def conv1d {N n} [Fact (N≠0)] [Fact (n≠0)] (x : ℝ^{N}) (w : ℝ^{n}) (b : ℝ) : ℝ^{N} := 
    λ [i] => SciLean.conv1d (λ i' => x[i']) (λ i' => w[i']) b i 
  argument x
    adjDiff by unfold conv1d; simp; unfold hold; simp
  argument w
    adjDiff by unfold conv1d; simp; unfold hold; simp

  set_option trace.Meta.Tactic.simp.discharge true in
  def conv1d' {N n} [Fact (N≠0)] [Fact (n≠0)] [Fact (l≠0)] 
    (x : Fin N → ℝ) (w : Fin l → Fin n → ℝ) (b : Fin l → ℝ) 
    : Fin l → Fin N → ℝ 
    := 
    λ k' i => SciLean.conv1d x (λ i' => w k' i') (b k') i 
  argument x
    adjDiff by unfold conv1d'; simp
  argument w
    adjDiff by unfold conv1d'; simp; unfold hold; simp[sum_into_lambda]
  
  set_option synthInstance.maxHeartbeats 5000 in 
  def conv1d'' {N n} [Fact (N≠0)] [Fact (n≠0)] (x : ℝ^{N}) (w : ℝ^{l,n}) (b : ℝ^{l}) : ℝ^{l,N} := 
    λ [k',i] => SciLean.conv1d (λ i' => x[i']) (λ i' => w[k',i']) b[k'] i 
  argument x
    adjDiff by unfold conv1d''; simp; unfold hold; simp
  argument w
    adjDiff by unfold conv1d''; simp; unfold hold; simp[sum_into_lambda]

  #exit 

  def conv2d {N M n m l} [Fact (N≠0)] [Fact (M≠0)] [Fact (n≠0)] [Fact (m≠0)]
    (x : ℝ^{N, M}) (w : ℝ^{l, n, m}) (b : ℝ^{l}) : ℝ^{l, N, M} := 
    λ [k',i,j] => SciLean.conv2d (λ i j => x[i,j]) (λ i' j' => w[k',i',j']) b[k'] i j
  argument x
    adjDiff by unfold conv2d; simp; unfold hold; simp
  -- argument w
  --   isSmooth, hasAdjDiff, adjDiff?
  -- argument b
  --   isSmooth, hasAdjDiff, adjDiff?

-- (∑ i' j', w[k', i', j'] * x[i.shift i', j.shift j']) + b[k']
  

  variable (x : ℝ^{n,m})

  #check Tensor.conv2d


end SciLean.Tensor


#check x.set

#check Nat

-- def fully_connected_rank3 {N M L n} (x : ℝ^{L, N, M}) (w : ℝ^{n, L, N, M}) (b : ℝ^{n}) : ℝ^{n} :=
--   λ [i'] => (∑ i j k, w[i',i,j,k] * x[i,j,k]) + b[i']
-- argument x
--   isSmooth, hasAdjDiff, adjDiff?
-- argument w
--   isSmooth, hasAdjDiff, adjDiff?
-- argument b
--   isSmooth, hasAdjDiff, adjDiff?

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
      |> (Tensor.conv2d (l:=10) (n:=3) (m:=3) · w₁ b₁) 
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
