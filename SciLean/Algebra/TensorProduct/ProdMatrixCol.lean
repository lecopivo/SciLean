import SciLean.Analysis.AdjointSpace.Adjoint

import SciLean.Tactic.SimpleProxyType
import SciLean.Data.Instances.Sigma

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
