import SciLean.Operators.Adjoint.Core

namespace SciLean

  variable {α β γ : Type}
  variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
  variable {ι κ} [Enumtype ι] [Enumtype κ]

  -- Negation --
  --------------

  instance has_adjoint_neg
    : HasAdjoint (λ x : X => -x) := sorry
  @[simp]
  theorem adjoint_of_neg
    : (λ x : X => -x)† = λ x : X => -x := sorry
  @[simp]
  theorem adjoint_of_negx 
    (f : X → Y) [HasAdjoint f]
    : f† (-x) = - f† x := sorry

  -- Scalar multiplication --
  ---------------------------

  instance has_adjoint_smul2 (r : ℝ)
    : HasAdjoint (λ x : X => r * x) := sorry
  @[simp]
  theorem adjoint_of_smul2 (r : ℝ)
    : (λ x : X => r * x)† = r * (λ x : X => x) := sorry
  @[simp]
  theorem adjoint_of_smul2x (r : ℝ) 
    (f : X → Y) [HasAdjoint f]
    : f† (r * x) = r * f† x := sorry

  -- These hold only for Hilbert spaces!!!
  -- Maybe can be generalized for `x` that are test functions
  -- For those we can pick the domain on which they are test functions
  instance has_adjoint_smul1 
    {X} [Hilbert X] (x : X)
    : HasAdjoint (λ r : ℝ => r * x) := sorry
  @[simp] 
  theorem adjoint_of_smul1
    {X} [Hilbert X] (x : X)
    : (λ r : ℝ => r * x)† = λ y : X => ⟪x, y⟫ := sorry

  -- Addition --
  --------------

  instance : HasAdjoint (λ ((x,y) : X×X) => x + y) := sorry
  instance : HasAdjoint (λ ((x,y) : X×X) => x - y) := sorry

  @[simp]
  theorem adjoint_of_add 
    : (λ ((x,y) : X×X) => x + y)† = λ x => (x, x) 
  := by
    funext x; apply inner_ext; intro ϕ Ω h
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    simp[SemiInner.semiInner]
    -- split the inner product and use the fact that:
    --   Ω.1 < (fun x => x.1 + x.2)‡ Ω  and  testFunction Ω.1 ϕ.1
    --   Ω.2 < (fun x => x.1 + x.2)‡ Ω  and  testFunction Ω.2 ϕ.2
    admit

  @[simp]
  theorem adjoint_of_sub 
    : (λ ((x,y) : X×X) => x - y)† = λ x : X => (x, -x)
  := by
    funext x; apply inner_ext; intro ϕ Ω h
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    simp[SemiInner.semiInner]
    admit

  @[simp]
  theorem adjoint_of_add_fun 
    (f g : X → Y) [HasAdjoint f] [HasAdjoint g] 
    : (f + g)† = f† + g† 
  := by simp[HAdd.hAdd, Add.add]; done
  @[simp]
  theorem adjoint_of_sub_fun 
    (f g : X → Y) [HasAdjoint f] [HasAdjoint g] 
    : (f - g)† = f† - g† 
  := by simp[HSub.hSub, Sub.sub]; done

  @[simp]
  theorem adjoint_of_add_funparm 
    (f g : X → ι → Y) [HasAdjoint f] [HasAdjoint g] [Nonempty ι]
    : (λ x i => f x i + g x i)† = f† + g† 
  := by funext z; simp [sum_of_linear]; done
  @[simp]
  theorem adjoint_of_sub_funparm 
    (f g : X → ι → Y) [HasAdjoint f] [HasAdjoint g] [Nonempty ι]
    : (λ x i => f x i - g x i)† = f† - g† 
  := by funext z; simp [sum_of_linear]; done

  -- Inner Product --
  -------------------

  -- instance (y : X) Ω : IsLin (λ x y : X => ⟪x, y⟫[Ω]) := sorry
  instance {X} [Hilbert X] (y : X) : HasAdjoint (λ x : X => ⟪x, y⟫) := sorry
  instance {X} [Hilbert X] (x : X) : HasAdjoint (λ y : X => ⟪x, y⟫) := sorry

  @[simp]
  theorem adjoint_of_inner1 
    {X : Type} [Hilbert X] 
    (y : X) 
    : (λ x : X => ⟪x, y⟫)† = (λ (s : ℝ) => s * y) 
  := by
    funext x; apply inner_ext; intro ϕ Ω h
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    simp
    rw[!?(⟪ϕ,y⟫ = ⟪y,ϕ⟫)]
    done

  @[simp]
  theorem adjoint_of_inner2 
    {X : Type} [Hilbert X] 
    (x : X) 
    : (λ y : X => ⟪x, y⟫)† = (λ (s : ℝ) => s * x) := by
    funext y; apply inner_ext; intro ϕ Ω h
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    simp 
    done

  @[simp]
  theorem adjoint_of_inner1_comp 
    {X Y : Type} [Hilbert X] [Hilbert Y] 
    (f : X → Y) [HasAdjoint f] 
    (y : Y) 
    : (λ x : X => ⟪f x, y⟫)† = (λ (s : ℝ) => s * f† y) 
  := by simp; unfold hold; simp; done

  @[simp]
  theorem adjoint_of_inner2_comp 
    {X Y : Type} [Hilbert X] [Hilbert Y] 
    (f : X → Y) [HasAdjoint f] 
    (y : Y) 
    : (λ x : X => ⟪y, f x⟫)† = (λ (s : ℝ) => s * f† y) 
  := by simp; unfold hold; simp; done


  -- Sum --
  ---------

  instance has_adjoint_sum
   : HasAdjoint (sum : (ι → X) → X) := sorry

  @[simp]
  theorem adjoint_of_sum
    : (sum : (ι → X) → X)† = λ x i => x := sorry

  -- Combinators --
  -----------------

  @[simp] 
  theorem adjoint_of_function_id 
    : adjoint (id : X → X) = id := by simp[id]

  @[simp] 
  theorem adjoint_of_function_comp 
    (f : Y → Z) [HasAdjoint f] 
    (g : X → Y) [HasAdjoint g] 
    : (f∘g)† = g† ∘ f† := by simp[Function.comp]

end SciLean
