import SciLean.Operators.Calculus
import SciLean.Operators.Adjoint

namespace SciLean

macro "unfold_atomic" : tactic => 
  `(unfold AtomicSmoothFun₂.df₁; 
    unfold AtomicSmoothFun₂.df₂; 
    unfold AtomicSmoothFun.df; 
    unfold AtomicAdjointFun₂.adj₁;
    unfold AtomicAdjointFun₂.adj₂;
    unfold AtomicAdjointFun.adj;
    simp only [])

