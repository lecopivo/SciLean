module

public import SciLean.Analysis.AdjointSpace.Adjoint

public import SciLean.Tactic.SimpleProxyType
public import SciLean.Data.Instances.Sigma

@[expose] public section


namespace SciLean

structure ProdMatrixCol (M₁ M₂ : Type*) where
  A₁ : M₁
  A₂ : M₂

instance [Add M₁] [Add M₂] : Add (ProdMatrixCol M₁ M₂) :=
  (Add.ofEquiv (simple_proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixCol.simpleProxyTypeEquiv,Add.ofEquiv]

instance [Sub M₁] [Sub M₂] : Sub (ProdMatrixCol M₁ M₂) :=
  (Sub.ofEquiv (simple_proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixCol.simpleProxyTypeEquiv,Sub.ofEquiv]

instance [Neg M₁] [Neg M₂] : Neg (ProdMatrixCol M₁ M₂) :=
  (Neg.ofEquiv (simple_proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixCol.simpleProxyTypeEquiv,Neg.ofEquiv]

instance [SMul R M₁] [SMul R M₂] : SMul R (ProdMatrixCol M₁ M₂) :=
  (SMul.ofEquiv R (simple_proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixCol.simpleProxyTypeEquiv,SMul.ofEquiv]

instance [Zero M₁] [Zero M₂] : Zero (ProdMatrixCol M₁ M₂) :=
  (Zero.ofEquiv (simple_proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixCol.simpleProxyTypeEquiv,Zero.ofEquiv]

instance [Norm M₁] [Norm M₂] : Norm (ProdMatrixCol M₁ M₂) :=
  (Norm.ofEquiv (simple_proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixCol.simpleProxyTypeEquiv,Norm.ofEquiv]

instance {R} [Ring R] [Inner R M₁] [Inner R M₂] : Inner R (ProdMatrixCol M₁ M₂) :=
  (Inner.ofEquiv (R:=R) (simple_proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    simp[ProdMatrixCol.simpleProxyTypeEquiv,Inner.ofEquiv,Inner.inner]

instance [AddCommGroup M₁] [AddCommGroup M₂] : AddCommGroup (ProdMatrixCol M₁ M₂) :=
  (AddCommGroup.ofEquiv (proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixCol.simpleProxyTypeEquiv,AddCommGroup.ofEquiv]

instance {R} [Ring R] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂] :
    Module R (ProdMatrixCol M₁ M₂) :=
  (Module.ofEquiv (R:=R) (proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixCol.simpleProxyTypeEquiv,Module.ofEquiv]

instance [MetricSpace M₁] [MetricSpace M₂] : MetricSpace (ProdMatrixCol M₁ M₂) :=
  (MetricSpace.ofEquiv (simple_proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixCol.simpleProxyTypeEquiv,MetricSpace.ofEquiv]

instance [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] : NormedAddCommGroup (ProdMatrixCol M₁ M₂) :=
  (NormedAddCommGroup.ofEquiv (simple_proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[ProdMatrixCol.simpleProxyTypeEquiv,NormedAddCommGroup.ofEquiv]


instance {R} [RCLike R] [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] [NormedSpace R M₁] [NormedSpace R M₂] :
    NormedSpace R (ProdMatrixCol M₁ M₂) :=
  (NormedSpace.ofEquiv (R:=R) (simple_proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    simp[ProdMatrixCol.simpleProxyTypeEquiv,NormedSpace.ofEquiv]

instance {R} [RCLike R] [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] [AdjointSpace R M₁] [AdjointSpace R M₂] :
    AdjointSpace R (ProdMatrixCol M₁ M₂) :=
  (AdjointSpace.ofEquiv (R:=R) (simple_proxy_equiv% (ProdMatrixCol M₁ M₂)))
  rewrite_by
    simp[ProdMatrixCol.simpleProxyTypeEquiv,AdjointSpace.ofEquiv]


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
theorem ProdMatrixCol.A₁.arg_A.IsContinuousLinearMap_rule :
    IsContinuousLinearMap R (fun A : ProdMatrixCol M₁ M₂ => A.A₁) := by
  constructor
  · constructor
    · intro A B; rfl
    · intro c A; rfl
  · have h : LipschitzWith 1 (fun A : ProdMatrixCol M₁ M₂ => A.A₁) := by
      apply LipschitzWith.of_dist_le_mul
      intro A B
      show dist A.A₁ B.A₁ ≤ 1 * (dist A.A₁ B.A₁ ⊔ dist A.A₂ B.A₂)
      rw [one_mul]; exact le_sup_left
    exact h.continuous

@[fun_prop]
theorem ProdMatrixCol.A₂.arg_A.IsContinuousLinearMap_rule :
    IsContinuousLinearMap R (fun A : ProdMatrixCol M₁ M₂ => A.A₂) := by
  constructor
  · constructor
    · intro A B; rfl
    · intro c A; rfl
  · have h : LipschitzWith 1 (fun A : ProdMatrixCol M₁ M₂ => A.A₂) := by
      apply LipschitzWith.of_dist_le_mul
      intro A B
      show dist A.A₂ B.A₂ ≤ 1 * (dist A.A₁ B.A₁ ⊔ dist A.A₂ B.A₂)
      rw [one_mul]; exact le_sup_right
    exact h.continuous

theorem ProdMatrixCol.isometry_mk :
    Isometry (fun p : M₁ × M₂ => (⟨p.1,p.2⟩ : ProdMatrixCol M₁ M₂)) :=
  Isometry.of_dist_eq (fun _ _ => rfl)

@[fun_prop]
theorem ProdMatrixCol.mk.arg_A₁A₂.IsContinuousLinearMap_rule (f : X → M₁) (g : X → M₂)
    (hf : IsContinuousLinearMap R f) (hg : IsContinuousLinearMap R g) :
    IsContinuousLinearMap R (fun x => (⟨f x, g x⟩ : ProdMatrixCol M₁ M₂)) := by
  constructor
  · constructor
    · intro x y; show ProdMatrixCol.mk _ _ = _; rw [hf.1.map_add, hg.1.map_add]; rfl
    · intro c x; show ProdMatrixCol.mk _ _ = _; rw [hf.1.map_smul, hg.1.map_smul]; rfl
  · exact ProdMatrixCol.isometry_mk.continuous.comp (hf.2.prodMk hg.2)

end Linearity
