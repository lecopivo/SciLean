import SciLean.Operators.Adjoint.Basic

namespace SciLean

  variable {α β γ : Type}
  variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
  variable {ι κ : Type} [Enumtype ι] [Enumtype κ]

  -------------------------------------------------------

  -- I combinator
  instance has_adjoint_id
    : HasAdjoint λ x : X => x := sorry

  -- C Combinator
  -- Not true for general ι
  instance (priority := low) has_adjoint_swap
    (f : ι → Y → Z) [∀ i, HasAdjoint (f i)]
    : HasAdjoint (λ y i => f i y) := sorry

  -- K Combinator
  -- Not true for general ι.
  -- Because:
  --   (λ (x : X) (i : ι) => x)† = sum
  -- Thus we would need:
  --   (λ (x : ℝ) (t : ℝ) => x)† = integral
  -- but we do not know over which domain we should integrate!
  instance has_adjoint_const
    : HasAdjoint (λ (x : X) (i : ι) => x)
  := by infer_instance 

  -- B Combinator
  instance has_adjoint_comp
    (f : Y → Z) [HasAdjoint f] 
    (g : X → Y) [HasAdjoint g] 
    : HasAdjoint (λ x => f (g x)) := sorry

  -- variant of S combinator
  instance has_adjoint_diag
    (f : Y₁ → Y₂ → Z) [HasAdjoint (λ yy : Y₁ × Y₂ => f yy.1 yy.2)] 
    (g₁ : X → Y₁) [HasAdjoint g₁] 
    (g₂ : X → Y₂) [HasAdjoint g₂] 
    : HasAdjoint (λ x => f (g₁ x) (g₂ x)) := sorry

  -- What is the role of this one?? in terms of lambda calculus?
  instance has_adjoint_parm
    (i : ι) 
    (f : X → ι → Z) [HasAdjoint f] 
    : HasAdjoint (λ x => f x i) := sorry

  -- constant zero
  instance has_adjoint_const_zero
    : HasAdjoint (λ (x : X) => (0:Y)) := sorry

  -- Product type
  instance has_adjoint_fst
    : HasAdjoint (λ ((x,y) : X×Y) => x) := sorry

  instance has_adjoint_snd
    : HasAdjoint (λ ((x,y) : X×Y) => y) := sorry

  --------------------------------------------------------------------
  -- Variants a of theorems at points --
  -- These are necessary as higher order unification is only approximated

  instance comp_at_point1_has_adjoint
    (a : α)
    (f : Y → α → Z) [HasAdjoint (λ y => f y a)]
    (g : X → Y) [HasAdjoint g] 
    : HasAdjoint (λ x => f (g x) a)
  := by 
    (apply has_adjoint_comp (λ y => f y a) g) done

  instance comp_at_point2_has_adjoint
    (a : α) (b : β)
    (f : Y → α → β → Z) [HasAdjoint (λ y => f y a b)]
    (g : X → Y) [HasAdjoint g] 
    : HasAdjoint (λ x => f (g x) a b)
  := by 
    (apply has_adjoint_comp (λ y => f y a b) g) done

  instance comp_at_point3_has_adjoint
    (a : α) (b : β) (c : γ)
    (f : Y → α → β → γ → Z) [HasAdjoint (λ y => f y a b c)]
    (g : X → Y) [HasAdjoint g] 
    : HasAdjoint (λ x => f (g x) a b c)
  := by 
    (apply has_adjoint_comp (λ y => f y a b c) g) done

  instance diag_at_point1_has_adjoint
    (a : α)
    (f : Y₁ → Y₂ → α → Z) [HasAdjoint (λ (y₁,y₂) => f y₁ y₂ a)] 
    (g₁ : X → Y₁) [HasAdjoint g₁] 
    (g₂ : X → Y₂) [HasAdjoint g₂] 
    : HasAdjoint (λ x => f (g₁ x) (g₂ x) a)
  := by 
    (apply has_adjoint_diag (λ y₁ y₂ => f y₁ y₂ a) g₁ g₂) done

  instance diag_at_point2_has_adjoint
    (a : α) (b : β)
    (f : Y₁ → Y₂ → α → β → Z) [HasAdjoint (λ (y₁,y₂) => f y₁ y₂ a b)] 
    (g₁ : X → Y₁) [HasAdjoint g₁] 
    (g₂ : X → Y₂) [HasAdjoint g₂] 
    : HasAdjoint (λ x => f (g₁ x) (g₂ x) a b)
  := by 
    (apply has_adjoint_diag (λ y₁ y₂ => f y₁ y₂ a b) g₁ g₂) done

  instance diag_at_point3_has_adjoint
    (a : α) (b : β) (c : γ)
    (f : Y₁ → Y₂ → α → β → γ → Z) [HasAdjoint (λ (y₁,y₂) => f y₁ y₂ a b c)] 
    (g₁ : X → Y₁) [HasAdjoint g₁] 
    (g₂ : X → Y₂) [HasAdjoint g₂] 
    : HasAdjoint (λ x => f (g₁ x) (g₂ x) a b c)
  := by 
    (apply has_adjoint_diag (λ y₁ y₂ => f y₁ y₂ a b c) g₁ g₂) done

  --------------------------------------------------------------------

  @[simp]
  theorem adjoint_of_id 
    : (λ x : X => x)† = λ x => x :=
  by 
    funext x; 
    apply inner_ext; 
    intro y Ω h; 
    simp (discharger := assumption); 
    done

  @[simp low]
  theorem adjoint_of_swap 
    (f : ι → Y → Z) [∀ i, HasAdjoint (f i)] 
    : (λ y i => f i y)† = λ g => ∑ i, (f i)† (g i) 
  := by
    funext y; apply inner_ext; intro x Ω h;
    rw[inner_adjoint_fst_right_test]
    . simp[SemiInner.semiInner]
      -- simple linearity
      rw[!?(⟪∑ i, (f i)† (y i), x⟫[Ω] = ∑ i, ⟪(f i)† (y i), x⟫[Ω])]
      conv =>
        rhs; enter [1,i]
        rw[inner_adjoint_fst_right_test _ _ _ _ h]
      done
    . apply h
    done

  @[simp]
  theorem adjoint_of_const 
    : (λ (x : X) (i : ι) => x)† = λ f => ∑ i, f i := by simp

  @[simp low]
  theorem adjoint_of_comp
    (f : Y → Z) [HasAdjoint f] 
    (g : X → Y) [HasAdjoint g] 
    : (λ x => f (g x))† = λ z => g† (f† z)
  := by
    funext x; apply inner_ext; intro ϕ Ω h
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    rw[inner_adjoint_fst_right_test _ _ _ _ _]
    simp
    apply test_function_of_pushforward
    apply h
    done

  @[simp low]
  theorem adjoint_of_diag
    (f : Y₁ → Y₂ → Z) [HasAdjoint (λ yy : Y₁ × Y₂ => f yy.1 yy.2)] 
    (g₁ : X → Y₁) [HasAdjoint g₁] 
    (g₂ : X → Y₂) [HasAdjoint g₂] 
    : (λ x => f (g₁ x) (g₂ x))† 
      = λ z => (λ (y₁,y₂) => (g₁† y₁) + (g₂† y₂)) $
               (λ (y₁,y₂) => f y₁ y₂)† z 
  := by
    funext x; apply inner_ext; intro ϕ Ω h
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    rw[!?(∀ x y z, ⟪x + y, z⟫[Ω] = ⟪x, z⟫[Ω] + ⟪y, z⟫[Ω])]
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    simp
    rw[!?(⟪((fun x : Y₁×Y₂ => f x.1 x.2)† x).1, g₁ ϕ⟫[g₁‡ Ω] + ⟪((fun x : Y₁×Y₂ => f x.1 x.2)† x).2, g₂ ϕ⟫[g₂‡ Ω] 
          = 
          ⟪((fun x => f x.1 x.2)† x), (g₁ ϕ, g₂ ϕ)⟫[(λ x => (g₁ x, g₂ x))‡ Ω])]
    rw[inner_adjoint_fst_right_test _ _ _ _ _]
    simp
    -- almost done
    admit
    admit
    done

  -- This prevents an infinite loop when using `adjoint_of_diag` 
  -- with `g₁ = Prod.fst` and `g₂ = Prod.snd`
  @[simp low+1]
  theorem adjoint_of_diag_safeguard
    (f : X → Y → Z) [HasAdjoint (λ ((x,y) : X×Y) => f x y)]
    : (λ (x,y) => f x y)† = (Function.uncurry f)† := 
  by simp only [Function.uncurry] done

  @[simp low]
  theorem adjoint_of_parm
    (f : X → ι → Z) [HasAdjoint f]
    (i : ι)
    : (λ x => f x i)† = (λ z => f† (λ j => (kron i j) * z))
  := by
    funext x; apply inner_ext; intro ϕ Ω h
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    have h : Nonempty ι := sorry -- The proof should be finishable without this.
    simp[SemiInner.semiInner]
    done

  @[simp]
  theorem adjoint_of_fst
    : (λ ((x, y) : X×Y) => x)† = λ x => (x, (0 : Y)) 
  := by
    funext x; apply inner_ext; intro ϕ Ω h
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    simp[SemiInner.semiInner]
    done

  @[simp]
  theorem adjoint_of_snd
    : (λ ((x, y) : X×Y) => y)† = λ y => ((0 : X), y)
  := by
    funext x; apply inner_ext; intro ϕ Ω h
    rw[inner_adjoint_fst_right_test _ _ _ _ h]
    simp[SemiInner.semiInner]
    done

  --------------------------------------------------------------------
  -- These theorems are problematic when used with simp

  def hold {α} (a : α) := a
  
  @[simp low-1] -- try to avoid using this theorem
  theorem adjoint_of_comp_at_point1
    (a : α) 
    (f : Y → α → Z) [HasAdjoint (λ y => f y a)]
    (g : X → Y) [HasAdjoint g] 
    : 
      (λ x => f (g x) a)† = λ z => g† ((hold λ y => f y a)† z)
  := by 
    (apply adjoint_of_comp (λ y => f y a) g) done

  example
    (a : α) 
    (f : Y → α → Z) [HasAdjoint (λ y => f y a)]
    (g : X → Y) [HasAdjoint g] 
    : 
      (λ x => f (g x) a)† = λ z => g† ((λ y => f y a)† z)
  := by simp

  @[simp low-1] -- try to avoid using this theorem
  theorem adjoint_of_comp_at_point2
    (a : α) (b : β)
    (f : Y → α → β → Z) [HasAdjoint (λ y => f y a b)]
    (g : X → Y) [HasAdjoint g] 
    : 
      (λ x => f (g x) a b)† = λ z => g† ((hold λ y => f y a b)† z)
  := by 
    (apply adjoint_of_comp (λ y => f y a b) g) done

  @[simp low-1] -- try to avoid using this theorem
  theorem adjoint_of_comp_at_point3
    (a : α) (b : β) (c : γ)
    (f : Y → α → β → γ → Z) [HasAdjoint (λ y => f y a b c)]
    (g : X → Y) [HasAdjoint g] 
    : 
      (λ x => f (g x) a b c)† = λ z => g† ((hold λ y => f y a b c)† z)
  := by 
    (apply adjoint_of_comp (λ y => f y a b c) g) done

  -- theorem adjoint_of_comp_at_point4
  -- ...

  @[simp low-1] -- try to avoid using this theorem
  theorem adjoint_of_diag_at_point1
    (a : α)
    (f : Y₁ → Y₂ → α → Z) [HasAdjoint (λ (y₁,y₂) => f y₁ y₂ a)] 
    (g₁ : X → Y₁) [HasAdjoint g₁] 
    (g₂ : X → Y₂) [HasAdjoint g₂] 
    : (λ x => f (g₁ x) (g₂ x) a)† 
      = λ z => (λ (y₁,y₂) => (g₁† y₁) + (g₂† y₂)) $
               (hold λ (y₁,y₂) => f y₁ y₂ a)† z
  := by 
    (apply adjoint_of_diag (λ y₁ y₂ => f y₁ y₂ a) g₁ g₂) done

  @[simp low-1] -- try to avoid using this theorem
  theorem adjoint_of_diag_at_point2
    (a : α) (b : β)
    (f : Y₁ → Y₂ → α → β → Z) [HasAdjoint (λ (y₁,y₂) => f y₁ y₂ a b)] 
    (g₁ : X → Y₁) [HasAdjoint g₁] 
    (g₂ : X → Y₂) [HasAdjoint g₂] 
    : (λ x => f (g₁ x) (g₂ x) a b)† 
      = λ z => (λ (y₁,y₂) => (g₁† y₁) + (g₂† y₂)) $
               (hold λ (y₁,y₂) => f y₁ y₂ a b)† z
  := by 
    (apply adjoint_of_diag (λ y₁ y₂ => f y₁ y₂ a b) g₁ g₂) done

  -- theorem adjoint_of_diag_at_point3
  -- ...


  --------------------------------------------------------------------------------------------

  macro "autoadjoint" : conv => `(repeat' (conv => 
                                            pattern (adjoint _)
                                            simp
                                            unfold hold
                                            simp))
  macro "autoadjoint" : tactic => `(conv => autoadjoint)

  --------------------------------------------------------------------------------------------
