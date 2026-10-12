module

public import Mathlib.Analysis.Matrix.Normed

public import SciLean.Analysis.AdjointSpace.Adjoint

@[expose] public section


namespace SciLean

-- We make `Matrix m n α` normed space globally
attribute [instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable
    {R I J α : Type*} {nI nJ : ℕ}
    [IndexType I nI] [IndexType J nJ] [Fold I] [Fold J]

instance [AddCommMonoid R] [Inner R α] : Inner R (Matrix I J α) :=
  show Inner R (I → J → α) from inferInstance

instance [RCLike R] [NormedAddCommGroup α] [AdjointSpace R α] : AdjointSpace R (Matrix I J α) :=
  show AdjointSpace R (I → J → α) from inferInstance
