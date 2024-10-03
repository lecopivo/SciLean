import SciLean
import SciLean.Data.DataArray
import SciLean.Data.ArrayType
import SciLean.Data.ArrayType.Properties

namespace SciLean.ML


variable
  {R : Type} [RealScalar R] [PlainDataType R]
  {ι : Type} [IndexType ι] [DecidableEq ι]

set_default_scalar K

def dense (n : Nat)
  (weights : R^[n,ι]) (bias : R^[n]) (x : R^[ι]) : R^[n] :=
  ⊞ j => ∑ i, weights[(j,i)] * x[i] + bias[j]


def_fun_prop dense in x : IsAffineMap R
def_fun_prop dense in weights : IsAffineMap R
def_fun_prop dense in bias : IsAffineMap R
def_fun_prop dense in weights bias x
  with_transitive
  : Differentiable R


def_fun_trans dense in weights bias x
  arg_subsets
  [DecidableEq ι] : revFDerivProj R Unit by (unfold dense; autodiff)

def_fun_trans dense in weights bias x
  arg_subsets
  [DecidableEq ι] : revFDerivProjUpdate R Unit by (unfold dense; autodiff)

def_fun_trans dense in weights bias x
  arg_subsets
  [DecidableEq ι] : revFDeriv R  by (rw[revFDeriv_eq_revFDerivProj]; autodiff)
