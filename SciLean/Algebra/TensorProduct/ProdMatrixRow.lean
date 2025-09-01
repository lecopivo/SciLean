import SciLean.Analysis.AdjointSpace.Adjoint

import SciLean.Tactic.SimpleProxyType
import SciLean.Data.Instances.Sigma

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
