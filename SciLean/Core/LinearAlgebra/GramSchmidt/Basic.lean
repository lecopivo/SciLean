import SciLean.Data.DataArray
import SciLean.Data.ArrayType
import SciLean.Core.FunctionTransformations
import SciLean.Core.FunctionPropositions

namespace SciLean

open IndexType

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


/-- Returns orthonormal basis of `X` that where the first vector is normalized `u`. -/
def completeToOrhonormalBasis
    {ι} [IndexType ι] [LawfulIndexType ι]
    {X} [AddCommGroup X] [Module R X] [Inner R X] [Basis ι R X]
    (u : X) : Array X := Id.run do

  let dim := card ι
  if dim = 0 then return #[]

  have : Inhabited ι := ⟨fromFin ⟨0, by sorry_proof⟩⟩

  -- Find the maximal component of `u`
  let i' := toFin (IndexType.argMax (fun i : ι => |Basis.proj i u|))

  -- Initiali collection of basis vectors
  -- `u` is take as the first basis vector
  -- and we complete it with the canonical bases on `R^[n]` but we omit the basis vector
  -- that corresponds to the largest component of `u`
  let basis : Array X := .ofFn fun (i : Fin dim) =>
    if i.1 = 0 then
      u
    else if i.1 ≤ i'.1 then
      let i'' : ι := fromFin ⟨i.1-1, by omega⟩
      Basis.basis i''
    else
      let i'' : ι := fromFin ⟨i.1, by omega⟩
      Basis.basis i''

  return gramSchmidtArrayImpl R basis


/-- Decomposes the space `X` into the line given by `u` and the hyper plane perpendicular to `u`. -/
def hyperplaneDecomposition
    {ι} [IndexType ι] [LawfulIndexType ι]
    {X} [AddCommGroup X] [Module R X] [Inner R X]
    [Basis ι R X] (u : X)
    (hn : n + 1 = card ι := by first | assumption | infer_var) :
    R×R^[n] ≃ X := Id.run do

  let basis := completeToOrhonormalBasis u

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


theorem planeDecomposition_normal_dir
    {n} {ι} [IndexType ι] [LawfulIndexType ι]
    {X} [NormedAddCommGroup X] [AdjointSpace R X]
    [Basis ι R X] (u : X)
    (hn : n + 1 = card ι := by infer_var) :
    hyperplaneDecomposition u hn (t,0) = (t • vecNormalize R u) := sorry_proof


theorem planeDecomposition_orthogonal_dir
    {n} {ι} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
    {X} [NormedAddCommGroup X] [AdjointSpace R X]
    [Basis ι R X] (u : X) (y : R^[n])
    (hn : n + 1 = card ι := by infer_var) :
    ⟪u, hyperplaneDecomposition u hn (t,y)⟫ = t * ‖u‖₂ := sorry_proof
