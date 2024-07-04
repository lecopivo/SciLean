import SciLean.Data.DataArray
import SciLean.Data.ArrayType
import SciLean.Core.FunctionTransformations
import SciLean.Core.FunctionPropositions
-- import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.SetParametrization
import SciLean.Core.Integral.Jacobian
import SciLean.Core.Integral.BoundingBall
import SciLean.Core.Notation
import SciLean.Tactic.InferVar

import SciLean.Mathlib.Analysis.AdjointSpace.Adjoint

import SciLean.Core.Integral.HasParamDerivWithJumpsCommon

import SciLean.Core.FloatAsReal

namespace SciLean

variable
  {R : Type _} [RealScalar R] [PlainDataType R]

set_default_scalar R


variable (R)
/-- Given collection of `n` vectors return orthonormal set of vectors obtained by Gram-Shcmidt
algorithm.  -/
def gramSchmidtArrayImpl {X} [Sub X] [SMul R X] [Inner R X] (u : Array X) : Array X := Id.run do
  let mut u := u
  for i in [0:u.size] do
    let i : Fin u.size := ⟨i, sorry_proof⟩
    let mut ui := u[i]
    for j in [0:i.1] do
      let j : Fin u.size := ⟨j,sorry_proof⟩
      let uj := u[j]
      ui -= ⟪uj,ui⟫ • uj
    u := u.set i (vecNormalize R ui)
  return u
variable {R}


/-- Given collection of `n` vectors return orthonormal set of vectors obtained by Gram-Shcmidt
algorithm.  -/
def gramSchmidtDataArrayImpl {X} [Sub X] [SMul R X] [Inner R X] [PlainDataType X] (u : X^[n]) : X^[n] :=
  Id.run do
  let mut u := u
  for i in IndexType.univ (Fin n) do
    let mut ui := u[i]
    for j in [0:i.1] do
      let j : Fin n := ⟨j,sorry_proof⟩
      let uj := u[j]
      ui -= ⟪uj,ui⟫ • uj
    u[i] := vecNormalize R ui
  return u



open IndexType
def planeDecomposition
    {ι} [IndexType ι] [LawfulIndexType ι]
    {X} [AddCommGroup X] [Module R X] [Inner R X]
    [Basis ι R X] (u : X)
    (hn : n + 1 = card ι := by first | assumption | infer_var) :
    R×R^[n] ≃ X := Id.run do

  have : Inhabited ι := ⟨fromFin ⟨0, by omega⟩⟩

  -- Find the maximal component of `u`
  let i' := toFin (IndexType.argMax (fun i : ι => |Basis.proj i u|))

  -- Initiali collection of basis vectors
  -- `u` is take as the first basis vector
  -- and we complete it with the canonical bases on `R^[n]` but we omit the basis vector
  -- that corresponds to the largest component of `u`
  let basis : Array X := .ofFn fun (i : Fin (n+1)) =>
    if i.1 = 0 then
      u
    else if i.1 ≤ i'.1 then
      let i'' : ι := fromFin ⟨i.1-1, by omega⟩
      Basis.basis i''
    else
      let i'' : ι := fromFin ⟨i.1, by omega⟩
      Basis.basis i''

  let basis := gramSchmidtArrayImpl R basis

  have : basis.size = n + 1 := sorry_proof

  {
    toFun := fun (t,y) =>
      t • basis[0]
      +
      ∑ i : Fin n, y.get i • basis[i.1+1]
    invFun := fun x =>
      (⟪x,basis[0]⟫, ⊞ (j : Fin n) => ⟪x, basis[j.1+1]⟫)
    left_inv := sorry_proof
    right_inv := sorry_proof
  }


open IndexType in
theorem planeDecomposition_normal_dir
    {n} {ι} [IndexType ι] [LawfulIndexType ι]
    {X} [NormedAddCommGroup X] [AdjointSpace R X]
    [Basis ι R X] (u : X)
    (hn : n + 1 = card ι) :
    planeDecomposition u hn (t,0) = (t • vecNormalize R u) := sorry_proof

open IndexType in
theorem planeDecomposition_orthogonal_dir
    {n} {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
    {X} [NormedAddCommGroup X] [AdjointSpace R X]
    [Basis ι R X] (u : X) (y : R^[n])
    (hn : n + 1 = card ι) :
    ⟪u, planeDecomposition u hn (t,y)⟫ = t * ‖u‖₂ := sorry_proof


variable
  {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {κ} [IndexType κ] [LawfulIndexType κ] [DecidableEq κ]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [AdjointSpace R X] [CompleteSpace X] [b : Basis ι R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [AdjointSpace R Y] [CompleteSpace Y] [Basis κ R Y]


-- variable (f : X → R)
-- @[fun_trans]
-- theorem hoho {K} [RCLike K]
--     {X} [NormedAddCommGroup X] [AdjointSpace K X] [CompleteSpace X]
--     {Y} [NormedAddCommGroup Y] [AdjointSpace K Y] [CompleteSpace Y]
--     (f : X → Y) (hf : IsAffineMap K f) :
--     revFDeriv K f
--     =
--     fun x =>
--       (f x, fun dy => ⟪f 0, dy⟫_K) := by sorry_proof

open IndexType FiniteDimensional in
@[gtrans]
theorem SetParametrization.setOf_eq_affine {n} (f g : X → R) (hf : IsAffineMap R f) (hg : IsAffineMap R g)
    (hn : n + 1 = card ι := by infer_var) :
    SetParametrization {x | f x = g x} (R^[n])
    ([(Set.univ,
      (fun u =>
        let N := fgradient (fun x => f x - g x) 0
        let dec := planeDecomposition (R:=R) N hn
        let a := - (f 0 - g 0) / ‖N‖₂
        dec (a,u)))]) := sorry_proof


open IndexType FiniteDimensional in
@[gtrans]
theorem SurfaceParametrization.setOf_eq_affine {n} (f g : X → R) (hf : IsAffineMap R f) (hg : IsAffineMap R g)
    (hn : n + 1 = card ι := by infer_var) :
    SurfaceParametrization {x | f x = g x} (R^[n])
    ([(Set.univ,
      (fun u =>
        let N := fgradient (fun x => f x - g x) 0
        let dec := planeDecomposition (R:=R) N hn
        let a := - (f 0 - g 0) / ‖N‖₂
        dec (a,u)))]) := sorry_proof




open IndexType in
@[simp, fun_trans]
theorem planeDecomposition.arg_a0.jacobian_rule
    {n}
    (u : Y)
    (hn : n + 1 = card κ := by first | assumption | infer_var) (a : R)
    (f : X → R^[n]) (hf : Differentiable R f):
    jacobian R (fun x => planeDecomposition u hn (a, f x))
    =
    fun x => jacobian R f x := sorry_proof


open IndexType in
@[gtrans]
theorem planeDecomposition_preimage_bounding_ball
    (A : Set X) (u : X) (hn : n + 1 = card ι := by first | assumption | infer_var)
    {center radius} (hA : BoundingBall₂ R A center radius) :
    BoundingBall₂ (R:=R) (planeDecomposition u hn ⁻¹' A)
      (center :=
        let dec := planeDecomposition (R:=R) u hn
        (dec.symm center))
      (radius := radius) := sorry_proof


-- There seems to be some problem with RefinedDiscrTree and eta reduction and Equiv
open IndexType in
@[gtrans]
theorem planeDecomposition_preimage_bounding_ball'
    (A : Set X) (u : X) (hn : n + 1 = card ι := by first | assumption | infer_var)
    {center radius} (hA : BoundingBall₂ R A center radius) :
    BoundingBall₂ (R:=R) ((fun x => DFunLike.coe (planeDecomposition u hn) x) ⁻¹' A)
      (center :=
        let dec := planeDecomposition (R:=R) u hn
        (dec.symm center))
      (radius := radius) := sorry_proof
