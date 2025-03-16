import SciLean.Analysis.AdjointSpace.Adjoint

import SciLean.Tactic.SimpleProxyType
import SciLean.Data.Instances.Sigma

namespace SciLean

structure BlockMatrixRow (M₁ M₂ : Type*) where
  A₁ : M₁
  A₂ : M₂

instance [Add M₁] [Add M₂] : Add (BlockMatrixRow M₁ M₂) :=
  (Add.ofEquiv (simple_proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixRow.simpleProxyTypeEquiv,Add.ofEquiv]

instance [Sub M₁] [Sub M₂] : Sub (BlockMatrixRow M₁ M₂) :=
  (Sub.ofEquiv (simple_proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixRow.simpleProxyTypeEquiv,Sub.ofEquiv]

instance [Neg M₁] [Neg M₂] : Neg (BlockMatrixRow M₁ M₂) :=
  (Neg.ofEquiv (simple_proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixRow.simpleProxyTypeEquiv,Neg.ofEquiv]

instance [SMul R M₁] [SMul R M₂] : SMul R (BlockMatrixRow M₁ M₂) :=
  (SMul.ofEquiv R (simple_proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixRow.simpleProxyTypeEquiv,SMul.ofEquiv]

instance [Zero M₁] [Zero M₂] : Zero (BlockMatrixRow M₁ M₂) :=
  (Zero.ofEquiv (simple_proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixRow.simpleProxyTypeEquiv,Zero.ofEquiv]

instance [Norm M₁] [Norm M₂] : Norm (BlockMatrixRow M₁ M₂) :=
  (Norm.ofEquiv (simple_proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixRow.simpleProxyTypeEquiv,Norm.ofEquiv]

instance {R} [Ring R] [Inner R M₁] [Inner R M₂] : Inner R (BlockMatrixRow M₁ M₂) :=
  (Inner.ofEquiv (R:=R) (simple_proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    simp[BlockMatrixRow.simpleProxyTypeEquiv,Inner.ofEquiv,Inner.inner]

instance [AddCommGroup M₁] [AddCommGroup M₂] : AddCommGroup (BlockMatrixRow M₁ M₂) :=
  (AddCommGroup.ofEquiv (proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixRow.simpleProxyTypeEquiv,AddCommGroup.ofEquiv]

instance {R} [Ring R] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂] :
    Module R (BlockMatrixRow M₁ M₂) :=
  (Module.ofEquiv (R:=R) (proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixRow.simpleProxyTypeEquiv,Module.ofEquiv]

instance [MetricSpace M₁] [MetricSpace M₂] : MetricSpace (BlockMatrixRow M₁ M₂) :=
  (MetricSpace.ofEquiv (simple_proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixRow.simpleProxyTypeEquiv,MetricSpace.ofEquiv]

instance [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] : NormedAddCommGroup (BlockMatrixRow M₁ M₂) :=
  (NormedAddCommGroup.ofEquiv (simple_proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixRow.simpleProxyTypeEquiv,NormedAddCommGroup.ofEquiv]


instance {R} [RCLike R] [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] [NormedSpace R M₁] [NormedSpace R M₂] :
    NormedSpace R (BlockMatrixRow M₁ M₂) :=
  (NormedSpace.ofEquiv (R:=R) (simple_proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    simp[BlockMatrixRow.simpleProxyTypeEquiv,NormedSpace.ofEquiv]

instance {R} [RCLike R] [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] [AdjointSpace R M₁] [AdjointSpace R M₂] :
    AdjointSpace R (BlockMatrixRow M₁ M₂) :=
  (AdjointSpace.ofEquiv (R:=R) (simple_proxy_equiv% (BlockMatrixRow M₁ M₂)))
  rewrite_by
    simp[BlockMatrixRow.simpleProxyTypeEquiv,AdjointSpace.ofEquiv]
