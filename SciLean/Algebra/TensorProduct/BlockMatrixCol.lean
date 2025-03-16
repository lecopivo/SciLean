import SciLean.Analysis.AdjointSpace.Adjoint

import SciLean.Tactic.SimpleProxyType
import SciLean.Data.Instances.Sigma

namespace SciLean

structure BlockMatrixCol (M₁ M₂ : Type*) where
  A₁ : M₁
  A₂ : M₂

instance [Add M₁] [Add M₂] : Add (BlockMatrixCol M₁ M₂) :=
  (Add.ofEquiv (simple_proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixCol.simpleProxyTypeEquiv,Add.ofEquiv]

instance [Sub M₁] [Sub M₂] : Sub (BlockMatrixCol M₁ M₂) :=
  (Sub.ofEquiv (simple_proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixCol.simpleProxyTypeEquiv,Sub.ofEquiv]

instance [Neg M₁] [Neg M₂] : Neg (BlockMatrixCol M₁ M₂) :=
  (Neg.ofEquiv (simple_proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixCol.simpleProxyTypeEquiv,Neg.ofEquiv]

instance [SMul R M₁] [SMul R M₂] : SMul R (BlockMatrixCol M₁ M₂) :=
  (SMul.ofEquiv R (simple_proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixCol.simpleProxyTypeEquiv,SMul.ofEquiv]

instance [Zero M₁] [Zero M₂] : Zero (BlockMatrixCol M₁ M₂) :=
  (Zero.ofEquiv (simple_proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixCol.simpleProxyTypeEquiv,Zero.ofEquiv]

instance [Norm M₁] [Norm M₂] : Norm (BlockMatrixCol M₁ M₂) :=
  (Norm.ofEquiv (simple_proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixCol.simpleProxyTypeEquiv,Norm.ofEquiv]

instance {R} [Ring R] [Inner R M₁] [Inner R M₂] : Inner R (BlockMatrixCol M₁ M₂) :=
  (Inner.ofEquiv (R:=R) (simple_proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    simp[BlockMatrixCol.simpleProxyTypeEquiv,Inner.ofEquiv,Inner.inner]

instance [AddCommGroup M₁] [AddCommGroup M₂] : AddCommGroup (BlockMatrixCol M₁ M₂) :=
  (AddCommGroup.ofEquiv (proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixCol.simpleProxyTypeEquiv,AddCommGroup.ofEquiv]

instance {R} [Ring R] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂] :
    Module R (BlockMatrixCol M₁ M₂) :=
  (Module.ofEquiv (R:=R) (proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixCol.simpleProxyTypeEquiv,Module.ofEquiv]

instance [MetricSpace M₁] [MetricSpace M₂] : MetricSpace (BlockMatrixCol M₁ M₂) :=
  (MetricSpace.ofEquiv (simple_proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixCol.simpleProxyTypeEquiv,MetricSpace.ofEquiv]

instance [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] : NormedAddCommGroup (BlockMatrixCol M₁ M₂) :=
  (NormedAddCommGroup.ofEquiv (simple_proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    dsimp[BlockMatrixCol.simpleProxyTypeEquiv,NormedAddCommGroup.ofEquiv]


instance {R} [RCLike R] [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] [NormedSpace R M₁] [NormedSpace R M₂] :
    NormedSpace R (BlockMatrixCol M₁ M₂) :=
  (NormedSpace.ofEquiv (R:=R) (simple_proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    simp[BlockMatrixCol.simpleProxyTypeEquiv,NormedSpace.ofEquiv]

instance {R} [RCLike R] [NormedAddCommGroup M₁] [NormedAddCommGroup M₂] [AdjointSpace R M₁] [AdjointSpace R M₂] :
    AdjointSpace R (BlockMatrixCol M₁ M₂) :=
  (AdjointSpace.ofEquiv (R:=R) (simple_proxy_equiv% (BlockMatrixCol M₁ M₂)))
  rewrite_by
    simp[BlockMatrixCol.simpleProxyTypeEquiv,AdjointSpace.ofEquiv]
