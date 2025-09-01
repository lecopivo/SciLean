import SciLean.Core
import SciLean.Data.DataArray

namespace SciLean

  def ditfft2 {n} (x : Fin (2^n) × Fin 2 → ℝ) : ℝ^{2^n,2} :=
    match n with
    | 0 => introElem x
    | n'+1 =>
      let x₁ : ℝ^{2^n',2} := ditfft2 (λ ((i,j) : (Fin (2^n') × Fin 2)) => x (⟨2*i, sorry⟩, j))
      let x₂ : ℝ^{2^n',2} := ditfft2 (λ ((i,j) : (Fin (2^n') × Fin 2)) => x (⟨2*i+1, sorry⟩, j))

      let x' : ℝ^{2^(n'+1), 2} := introElem λ (i,j) =>
        let k : Fin (2^n') :=
          if h : i < 2^n' then
            ⟨i,h⟩
          else
            ⟨i-2^n', sorry⟩
        let p := x₁[k,j]

        let θ := - (i.1 * Math.pi) / 2^n'
        let cθ := Math.cos θ
        let sθ := Math.sin θ

        if j = 0 then
          let q₁ := cθ * x₂[k,0] - sθ * x₂[k,1]
          (p + q₁)/2
        else
          let q₂ := cθ * x₂[k,1] + sθ * x₂[k,0]
          (p + q₂)/2

      x'


  def FFT (x : ℝ^{2^n,2}) : ℝ^{2^n,2} := ditfft2 (λ (i,j) => x[i,j])
