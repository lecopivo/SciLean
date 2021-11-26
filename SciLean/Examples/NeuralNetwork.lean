import SciLean.Basic

namespace SciLean

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
              †(δ F w) 1) 
    := sorry

  
  

#check uncurry

#check Nat


    
def heheh {w dw x} : Impl (δ (neural_network ε β) w dw x) := 
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

-- def foo_grad : Impl (δ foo) :=
-- by
--   conv =>
--     enter [1,p,dp]
--     simp  [foo]
--     simp  [foo.match_1]
--     enter [1,x,1,a,b]
--     rmlamlet

--     print_main_goal
    
    
