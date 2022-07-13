import SciLean.Operators
import SciLean.Tactic.Basic

namespace SciLean

macro "autodiff"    : conv => `(repeat' (conv => pattern (∂ _); repeat' ext; simp))
macro "autograd"    : conv => `(conv => pattern (∇ _); simp[gradient]; autodiff; simp; autoadjoint; simp)

macro "autodiff"    : tactic => `(conv => autodiff)
macro "autograd"    : tactic => `(conv => autograd)

