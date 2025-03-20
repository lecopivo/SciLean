import SciLean.Analysis.AdjointSpace.Adjoint

import SciLean.Tactic.SimpleProxyType
import SciLean.Data.Instances.Sigma

namespace SciLean

structure ProdMatrix (M₁₁ M₁₂ M₂₁ M₂₂ : Type*) where
  A₁₁ : M₁₁
  A₁₂ : M₁₂
  A₂₁ : M₂₁
  A₂₂ : M₂₂

instance [Add M₁₁] [Add M₁₂] [Add M₂₁] [Add M₂₂] : Add (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (Add.ofEquiv (simple_proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    dsimp[ProdMatrix.simpleProxyTypeEquiv,Add.ofEquiv]

instance [Sub M₁₁] [Sub M₁₂] [Sub M₂₁] [Sub M₂₂] : Sub (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (Sub.ofEquiv (simple_proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    dsimp[ProdMatrix.simpleProxyTypeEquiv,Sub.ofEquiv]

instance [Neg M₁₁] [Neg M₁₂] [Neg M₂₁] [Neg M₂₂] : Neg (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (Neg.ofEquiv (simple_proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    dsimp[ProdMatrix.simpleProxyTypeEquiv,Neg.ofEquiv]

instance [SMul R M₁₁] [SMul R M₁₂] [SMul R M₂₁] [SMul R M₂₂] : SMul R (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (SMul.ofEquiv R (simple_proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    dsimp[ProdMatrix.simpleProxyTypeEquiv,SMul.ofEquiv]

instance [Zero M₁₁] [Zero M₁₂] [Zero M₂₁] [Zero M₂₂] : Zero (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (Zero.ofEquiv (simple_proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    dsimp[ProdMatrix.simpleProxyTypeEquiv,Zero.ofEquiv]

instance [Norm M₁₁] [Norm M₁₂] [Norm M₂₁] [Norm M₂₂] : Norm (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (Norm.ofEquiv (simple_proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    dsimp[ProdMatrix.simpleProxyTypeEquiv,Norm.ofEquiv]

instance {R} [Ring R] [Inner R M₁₁] [Inner R M₁₂] [Inner R M₂₁] [Inner R M₂₂] : Inner R (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (Inner.ofEquiv (R:=R) (simple_proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    simp[ProdMatrix.simpleProxyTypeEquiv,Inner.ofEquiv,Inner.inner]

instance [AddCommGroup M₁₁] [AddCommGroup M₁₂] [AddCommGroup M₂₁] [AddCommGroup M₂₂] : AddCommGroup (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (AddCommGroup.ofEquiv (proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    dsimp[ProdMatrix.simpleProxyTypeEquiv,AddCommGroup.ofEquiv]

instance {R} [Ring R] [AddCommGroup M₁₁] [AddCommGroup M₁₂] [AddCommGroup M₂₁] [AddCommGroup M₂₂] [Module R M₁₁] [Module R M₁₂] [Module R M₂₁] [Module R M₂₂] :
    Module R (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (Module.ofEquiv (R:=R) (proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    dsimp[ProdMatrix.simpleProxyTypeEquiv,Module.ofEquiv]

instance [MetricSpace M₁₁] [MetricSpace M₁₂] [MetricSpace M₂₁] [MetricSpace M₂₂] : MetricSpace (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (MetricSpace.ofEquiv (simple_proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    dsimp[ProdMatrix.simpleProxyTypeEquiv,MetricSpace.ofEquiv]

instance [NormedAddCommGroup M₁₁] [NormedAddCommGroup M₁₂] [NormedAddCommGroup M₂₁] [NormedAddCommGroup M₂₂] : NormedAddCommGroup (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (NormedAddCommGroup.ofEquiv (simple_proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    dsimp[ProdMatrix.simpleProxyTypeEquiv,NormedAddCommGroup.ofEquiv]


instance {R} [RCLike R] [NormedAddCommGroup M₁₁] [NormedAddCommGroup M₁₂] [NormedAddCommGroup M₂₁] [NormedAddCommGroup M₂₂] [NormedSpace R M₁₁] [NormedSpace R M₁₂] [NormedSpace R M₂₁] [NormedSpace R M₂₂] :
    NormedSpace R (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (NormedSpace.ofEquiv (R:=R) (simple_proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    simp[ProdMatrix.simpleProxyTypeEquiv,NormedSpace.ofEquiv]

instance {R} [RCLike R] [NormedAddCommGroup M₁₁] [NormedAddCommGroup M₁₂] [NormedAddCommGroup M₂₁] [NormedAddCommGroup M₂₂] [AdjointSpace R M₁₁] [AdjointSpace R M₁₂] [AdjointSpace R M₂₁] [AdjointSpace R M₂₂] :
    AdjointSpace R (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂) :=
  (AdjointSpace.ofEquiv (R:=R) (simple_proxy_equiv% (ProdMatrix M₁₁ M₁₂ M₂₁ M₂₂)))
  rewrite_by
    simp[ProdMatrix.simpleProxyTypeEquiv,AdjointSpace.ofEquiv]
