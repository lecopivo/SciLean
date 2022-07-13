import SciLean.Basic

def conv311 {n m} (k : Nat) (w : NDVector [3,1,1,k]) (x : NDVector [3,n,m]) : NDVector [n,m,k] := sorry
def conv33  {n m} (k : Nat) (l : Nat) (w : NDVector [3,3,k*l]) (x : NDVector [n,m,k]) : NDVector [n,m,k*l] := sorry
def fully_connected {dims} (n : Nat) (w : NDVector [dims.product, n]) (x : NDVector dims): NDVector [n] := sorry

-- def relu {dims} (ε : ℝ) (v : NDVector dims) : NDVector dims := sorry
def relu (ε : ℝ) (x : ℝ) : ℝ := (Math.sqrt (x*x + ε*ε) + x)/2

def maxpool {n m k} (ε : ℝ) (v : NDVector [n, m, k]) : NDVector [n/2,m/2,k] := sorry

def soft_max {dims} (β : ℝ) (v : NDVector dims) : NDVector dims := sorry

variable (ε β : ℝ)

def VGG :=
    λ (w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16) =>
    λ x : NDVector [3,224,224] =>
    (x
     |>
     (λ x => (conv311 64 w1 x).map (relu ε))
     |>
     (λ x => (conv33 64 1 w2 x).map (relu ε))
     |>
     (λ x => (maxpool ε x))
     |>
     (λ x => (conv33 64 2 w3 x).map (relu ε))
     |>
     (λ x => (conv33 128 1 w4 x).map (relu ε))
     |>
     (λ x => (maxpool ε x))
     |>
     (λ x => (conv33 128 2 w5 x).map (relu ε))
     |>
     (λ x => (conv33 256 1 w6 x).map (relu ε))
     |>
     (λ x => (conv33 256 1 w7 x).map (relu ε))
     |>
     (λ x => (maxpool ε x))
     |>
     (λ x => (conv33 256 2 w8 x).map (relu ε))
     |>
     (λ x => (conv33 512 1 w9 x).map (relu ε))
     |>
     (λ x => (conv33 512 1 w10 x).map (relu ε))
     |>
     (λ x => (maxpool ε x))
     |>
     (λ x => (conv33 512 1 w11 x).map (relu ε))
     |>
     (λ x => (conv33 512 1 w12 x).map (relu ε))
     |>
     (λ x => (conv33 512 1 w13 x).map (relu ε))
     |>
     (λ x => (maxpool ε x))
     |>
     (λ x => (fully_connected 4096 w14 x))
     |>
     (λ x => (fully_connected 4096 w15 x))
     |>
     (λ x => (fully_connected 1000 w16 x))
     |>
     (λ x => (soft_max β x))
    )


def heheh {w dw x} : ∂ (VGG) w dw x = 0 := 
by
  simp[VGG]
  simp[VGG.match_1]
  
  
  
