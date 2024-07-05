import SciLean.Core.LinearAlgebra.GramSchmidt.Basic

import SciLean.Core.FunctionPropositions
import SciLean.Core.FunctionTransformations
import SciLean.Core.Transformations.SurfaceParametrization
import SciLean.Core.Transformations.BoundingBall

namespace SciLean

open IndexType FiniteDimensional

variable
  {R} [RealScalar R] [PlainDataType R]
  {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {κ} [IndexType κ] [LawfulIndexType κ] [DecidableEq κ]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [AdjointSpace R X] [CompleteSpace X] [b : Basis ι R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [AdjointSpace R Y] [CompleteSpace Y] [Basis κ R Y]

set_default_scalar R

@[gtrans]
theorem SurfaceParametrization.setOf_eq_affine {n} (f g : X → R) (hf : IsAffineMap R f) (hg : IsAffineMap R g)
    (hn : n + 1 = card ι := by infer_var) :
    SurfaceParametrization {x | f x = g x} (R^[n])
    ([(Set.univ,
      (fun u =>
        let N := fgradient (fun x => f x - g x) 0
        let dec := hyperplaneDecomposition (R:=R) N hn
        let a := - (f 0 - g 0) / ‖N‖₂
        dec (a,u)))]) := sorry_proof


open IndexType in
@[simp, fun_trans]
theorem hyperplaneDecomposition.arg_a1.jacobian_rule (u : Y)
    {n} (hn : n + 1 = card κ := by first | assumption | infer_var)
    (a : R) (f : X → R^[n]) (hf : Differentiable R f):
    jacobian R (fun x => hyperplaneDecomposition u hn (a, f x))
    =
    fun x => jacobian R f x := sorry_proof


open IndexType in
@[gtrans]
theorem BoundingBall₂.preimage_hyperplaneDecomposition
    (A : Set X) (u : X) {n} (hn : n + 1 = card ι := by first | assumption | infer_var)
    {center radius} (hA : BoundingBall₂ R A center radius) :
    BoundingBall₂ (R:=R) (hyperplaneDecomposition u hn ⁻¹' A)
      (center :=
        let dec := hyperplaneDecomposition (R:=R) u hn
        (dec.symm center))
      (radius := radius) := sorry_proof


-- There seems to be some problem with RefinedDiscrTree and eta reduction and Equiv
open IndexType in
@[gtrans]
theorem planeDecomposition_preimage_bounding_ball'
    (A : Set X) (u : X) (hn : n + 1 = card ι := by first | assumption | infer_var)
    {center radius} (hA : BoundingBall₂ R A center radius) :
    BoundingBall₂ (R:=R) ((fun x => DFunLike.coe (hyperplaneDecomposition u hn) x) ⁻¹' A)
      (center :=
        let dec := hyperplaneDecomposition (R:=R) u hn
        (dec.symm center))
      (radius := radius) := sorry_proof
