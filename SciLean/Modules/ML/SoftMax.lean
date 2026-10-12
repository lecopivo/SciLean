module

public import SciLean.Core
public import SciLean.Core.Functions.Exp
public import SciLean.Core.Meta.GenerateRevDeriv
public import SciLean.Data.DataArray
public import SciLean.Data.ArrayType
public import SciLean.Data.Prod
public import Mathlib

@[expose] public section


namespace SciLean.ML

variable
  {R : Type} [RealScalar R] [PlainDataType R] [LT R] [∀ x y : R, Decidable (x < y)]

set_default_scalar R

def softMax [RealScalar R]
  {ι} [Index ι] [Inhabited ι] (r : R) (x : R^ι) : R^ι :=
  let m := ArrayType.max x
  let x := ArrayType.map (fun xi => Scalar.exp (r*(xi-m))) x
  let w := ∑ i, x[i]
  (1/w) • x

#generate_revDeriv softMax x
  prop_by unfold softMax; fprop
  trans_by
    unfold softMax; ftrans
