import SciLean.Operators
import SciLean.Tactic.Basic

namespace SciLean

macro "autodiff"    : conv => `(repeat' (conv => pattern (δ _); repeat' ext; simp))
-- macro "autoadjoint" : conv => `(repeat' (conv => pattern (adjoint _); repeat' ext; simp))
macro "autograd"    : conv => `(conv => pattern (∇ _); simp[gradient]; autodiff; simp)

macro "autodiff"    : tactic => `(conv => autodiff)
-- macro "autoadjoint" : tactic => `(conv => autoadjoint)
macro "autograd"    : tactic => `(conv => autograd)
