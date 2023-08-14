import SciLean.Core
import SciLean.Core.HomDoodle


namespace SciLean

  variable {X Y} {ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] 
    ---[SemiHilbert (X→Y)] [SemiHilbert (X → X → Y)]

  #check smoothDiff†

  #check adjoint
  -- #check (λ f : X → Y => ∂ f)†

  #check differential†
  
  
  noncomputable
  def divergence (f : X → X → Y) : X → Y := 
    λ x => ∑ i, ∂ f x (𝔼 i) (𝔼 i)

  @[simp] 
  theorem diff_adj_is_divergence (f : X → X → Y) [IsSmooth f] [∀ x, IsLin (f x)]
  : (smoothDiff† (λ x ⟿ λ dx ⊸ f x dx)) = λ x ⟿ ∑ i, ∂ f x (𝔼 i) (𝔼 i) := sorry

  @[simp] 
  theorem diff_adj_is_divergence' (f : X → X → Y) [IsSmooth f] [∀ x, IsLin (f x)]
  : (λ (f : X ⟿ Y) => (λ x ⟿ λ dx ⊸ ∂ f.1 x dx))† = λ f' => λ x ⟿ ∑ i : ι, (∂ f'.1 x (𝔼 i)) (𝔼 i) := sorry


  #check @diff_adj_is_divergence

  variable (f : X → Y)

  #check ∂ f


