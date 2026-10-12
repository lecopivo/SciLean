module

public import SciLean.Analysis.AdjointSpace.Adjoint

public import SciLean.Tactic.SimpleProxyType
public import SciLean.Data.Instances.Sigma

@[expose] public section


namespace SciLean

structure ProdMatrixRow (M₁ M₂ : Type*) where
  A₁ : M₁
  A₂ : M₂

instance [Add M₁] [Add M₂] : Add (ProdMatrixRow M₁ M₂) :=
  (Add.ofEquiv (simple_proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixRow.simpleProxyTypeEquiv,Add.ofEquiv]

instance [Sub M₁] [Sub M₂] : Sub (ProdMatrixRow M₁ M₂) :=
  (Sub.ofEquiv (simple_proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixRow.simpleProxyTypeEquiv,Sub.ofEquiv]

instance [Neg M₁] [Neg M₂] : Neg (ProdMatrixRow M₁ M₂) :=
  (Neg.ofEquiv (simple_proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixRow.simpleProxyTypeEquiv,Neg.ofEquiv]

instance [SMul R M₁] [SMul R M₂] : SMul R (ProdMatrixRow M₁ M₂) :=
  (SMul.ofEquiv R (simple_proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixRow.simpleProxyTypeEquiv,SMul.ofEquiv]

instance [Zero M₁] [Zero M₂] : Zero (ProdMatrixRow M₁ M₂) :=
  (Zero.ofEquiv (simple_proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixRow.simpleProxyTypeEquiv,Zero.ofEquiv]

instance [Norm M₁] [Norm M₂] : Norm (ProdMatrixRow M₁ M₂) :=
  (Norm.ofEquiv (simple_proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixRow.simpleProxyTypeEquiv,Norm.ofEquiv]

instance {R} [Ring R] [Inner R M₁] [Inner R M₂] : Inner R (ProdMatrixRow M₁ M₂) :=
  (Inner.ofEquiv (R:=R) (simple_proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    simp[ProdMatrixRow.simpleProxyTypeEquiv,Inner.ofEquiv,Inner.inner]

instance [AddCommGroup M₁] [AddCommGroup M₂] : AddCommGroup (ProdMatrixRow M₁ M₂) :=
  (AddCommGroup.ofEquiv (proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixRow.simpleProxyTypeEquiv,AddCommGroup.ofEquiv]

instance {R} [Ring R] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂] :
    Module R (ProdMatrixRow M₁ M₂) :=
  (Module.ofEquiv (R:=R) (proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixRow.simpleProxyTypeEquiv,Module.ofEquiv]

instance [MetricSpace M₁] [MetricSpace M₂] : MetricSpace (ProdMatrixRow M₁ M₂) :=
  (MetricSpace.ofEquiv (simple_proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixRow.simpleProxyTypeEquiv,MetricSpace.ofEquiv]

instance [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] : NormedAddCommGroup (ProdMatrixRow M₁ M₂) :=
  (NormedAddCommGroup.ofEquiv (simple_proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixRow.simpleProxyTypeEquiv,NormedAddCommGroup.ofEquiv]


instance {R} [RCLike R] [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] [NormedSpace R M₁] [NormedSpace R M₂] :
    NormedSpace R (ProdMatrixRow M₁ M₂) :=
  (NormedSpace.ofEquiv (R:=R) (simple_proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    simp[ProdMatrixRow.simpleProxyTypeEquiv,NormedSpace.ofEquiv]

instance {R} [RCLike R] [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] [AdjointSpace R M₁] [AdjointSpace R M₂] :
    AdjointSpace R (ProdMatrixRow M₁ M₂) :=
  (AdjointSpace.ofEquiv (R:=R) (simple_proxy_equiv% (ProdMatrixRow M₁ M₂)))
  rewrite_by
    simp[ProdMatrixRow.simpleProxyTypeEquiv,AdjointSpace.ofEquiv]


----------------------------------------------------------------------------------------------------
-- Linearity of projections and of the constructor --------------------------------------------------
----------------------------------------------------------------------------------------------------

section Linearity

variable
  {R : Type*} [RCLike R]
  {M₁ : Type*} [NormedAddCommGroup M₁] [NormedSpace R M₁]
  {M₂ : Type*} [NormedAddCommGroup M₂] [NormedSpace R M₂]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]

@[fun_prop]
theorem ProdMatrixRow.A₁.arg_A.IsContinuousLinearMap_rule :
    IsContinuousLinearMap R (fun A : ProdMatrixRow M₁ M₂ => A.A₁) := by
  constructor
  · constructor
    · intro A B; rfl
    · intro c A; rfl
  · have h : LipschitzWith 1 (fun A : ProdMatrixRow M₁ M₂ => A.A₁) := by
      apply LipschitzWith.of_dist_le_mul
      intro A B
      show dist A.A₁ B.A₁ ≤ 1 * (dist A.A₁ B.A₁ ⊔ dist A.A₂ B.A₂)
      rw [one_mul]; exact le_sup_left
    exact h.continuous

@[fun_prop]
theorem ProdMatrixRow.A₂.arg_A.IsContinuousLinearMap_rule :
    IsContinuousLinearMap R (fun A : ProdMatrixRow M₁ M₂ => A.A₂) := by
  constructor
  · constructor
    · intro A B; rfl
    · intro c A; rfl
  · have h : LipschitzWith 1 (fun A : ProdMatrixRow M₁ M₂ => A.A₂) := by
      apply LipschitzWith.of_dist_le_mul
      intro A B
      show dist A.A₂ B.A₂ ≤ 1 * (dist A.A₁ B.A₁ ⊔ dist A.A₂ B.A₂)
      rw [one_mul]; exact le_sup_right
    exact h.continuous

theorem ProdMatrixRow.isometry_mk :
    Isometry (fun p : M₁ × M₂ => (⟨p.1,p.2⟩ : ProdMatrixRow M₁ M₂)) :=
  Isometry.of_dist_eq (fun _ _ => rfl)

@[fun_prop]
theorem ProdMatrixRow.mk.arg_A₁A₂.IsContinuousLinearMap_rule (f : X → M₁) (g : X → M₂)
    (hf : IsContinuousLinearMap R f) (hg : IsContinuousLinearMap R g) :
    IsContinuousLinearMap R (fun x => (⟨f x, g x⟩ : ProdMatrixRow M₁ M₂)) := by
  constructor
  · constructor
    · intro x y; show ProdMatrixRow.mk _ _ = _; rw [hf.1.map_add, hg.1.map_add]; rfl
    · intro c x; show ProdMatrixRow.mk _ _ = _; rw [hf.1.map_smul, hg.1.map_smul]; rfl
  · exact ProdMatrixRow.isometry_mk.continuous.comp (hf.2.prodMk hg.2)

end Linearity
