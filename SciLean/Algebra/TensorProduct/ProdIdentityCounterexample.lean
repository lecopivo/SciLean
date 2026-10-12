module

public import SciLean.Algebra.TensorProduct.Prod

/-!
# The `identityMatrix_spec` field of the product `TensorProductSelf` instance is false

In `SciLean/Algebra/TensorProduct/Prod.lean` the instance
`TensorProductSelf R (X₁ × X₂) (ProdMatrixCol (ProdMatrixRow X₁₁ X₁₂) (ProdMatrixRow X₂₁ X₂₂))`
proves its field `identityMatrix_spec` with `sorry_proof`. The field can't be proved: the
`matVecMulAdd` of the `ProdMatrixRow` instance is

    matVecMulAdd a ⟨A₁,A₂⟩ ⟨x₁,x₂⟩ b y = matVecMulAdd a A₂ x₂ b (matVecMulAdd a A₁ x₁ b y)

so for `b = 0` the contribution `A₁ x₁` of the first block is multiplied by `0` and dropped.

This file makes that precise for `X₁ = X₂ = ℂ`:
* `scalarTP` is an honest `TensorProductType ℂ ℂ ℂ ℂ` (its `equiv` is mathlib's
  `TensorProduct.lid`, no `sorry_proof`) with `matVecMulAdd a A x b y = a*(A*x) + b*y`, and
  `scalarSelf` is the `TensorProductSelf ℂ ℂ ℂ` with identity `1`.
* `rowTP`, `colTP` and `prodSelf` are the instances of `Prod.lean` for these types.
* `prod_identityMatrix_eq`: the identity matrix of `prodSelf` is `⟨⟨1,0⟩,⟨0,1⟩⟩`.
* `prod_matVecMulAdd_identity`: multiplying `(x₁, x₂)` by it gives `(0, x₂)`, not `(x₁, x₂)`.
* `prod_identityMatrix_spec_false`: in particular `𝐈 * (1,1) ≠ (1,1)`.
* `prod_identityMatrix_spec_inconsistent`: the `sorry_proof` field `identityMatrix_spec` of
  `prodSelf` implies `False`.

About axioms: the computation in `prod_matVecMulAdd_identity` is a `show` (checked by definitional
unfolding) followed by `simp` in `ℂ`. Still, `#print axioms` lists `sorryProofAxiom` for these
theorems, because the instances they mention contain `sorry_proof` in proof fields that don't
affect the computed value: `Module (ProdMatrixRow M₁ M₂)` is `Module.ofEquiv` from
`Data/Instances/Sigma.lean`, whose module laws are `sorry_proof`. For
`prod_identityMatrix_spec_inconsistent` the `sorry_proof` field is the point of the theorem.

This file is not imported by `SciLean.lean`.
-/

@[expose] public section

namespace SciLean.ProdIdentityCounterexample

open TensorProductType TensorProductSelf

/-- `ℂ ⊗ ℂ = ℂ`, with the honest identification `ℂ ≃ₗ ℂ ⊗ ℂ` of mathlib. -/
noncomputable instance (priority := high) scalarTP : TensorProductType ℂ ℂ ℂ ℂ where
  equiv := .mk (TensorProduct.lid ℂ ℂ).symm
  tmulAdd a y x A := a * (y * x) + A
  tmulAdd_eq_tmul := by
    intro r x y A
    simp [smul_eq_mul]
  matVecMulAdd a A x b y := a * (A * x) + b * y
  vecMatMulAdd a y A b x := a * (y * A) + b * x

/-- The identity matrix of `ℂ ⊗ ℂ = ℂ` is `1`. -/
noncomputable instance (priority := high) scalarSelf : TensorProductSelf ℂ ℂ ℂ where
  identityMatrix := 1
  identityMatrix_spec := by intro x; simp [TensorProductType.matVecMulAdd]
  addIdentityMatrix r A := r + A
  addIdentityMatrix_spec := by intro r A; simp

/-- The matrix type of `(ℂ × ℂ) ⊗ (ℂ × ℂ)` used by the instance in `Prod.lean`. -/
abbrev M := ProdMatrixCol (ProdMatrixRow ℂ ℂ) (ProdMatrixRow ℂ ℂ)

/-! The instances of `Prod.lean`, specialized to `X₁ = X₂ = ℂ`. They are named explicitly
because instance search would otherwise pick `tpScalarLeft` for `ℂ ⊗ (ℂ × ℂ)` (the tensor product
type is an `outParam`). -/

/-- `ℂ ⊗ (ℂ × ℂ) = ProdMatrixRow ℂ ℂ` (instance of `Prod.lean`). -/
noncomputable instance (priority := high) rowTP : TensorProductType ℂ ℂ (ℂ × ℂ) (ProdMatrixRow ℂ ℂ) :=
  instTensorProductTypeProdProdMatrixRow ℂ (YX₁₁ := ℂ) (YX₁₂ := ℂ)

/-- `(ℂ × ℂ) ⊗ (ℂ × ℂ) = M` (instance of `Prod.lean`). -/
noncomputable instance (priority := high) colTP : TensorProductType ℂ (ℂ × ℂ) (ℂ × ℂ) M :=
  instTensorProductTypeProdProdMatrixCol ℂ (YX₁₁ := ProdMatrixRow ℂ ℂ) (YX₂₁ := ProdMatrixRow ℂ ℂ)

/-- The `TensorProductSelf` instance of `Prod.lean` whose field `identityMatrix_spec` is a
`sorry_proof`. -/
noncomputable instance (priority := high) prodSelf : TensorProductSelf ℂ (ℂ × ℂ) M :=
  instTensorProductSelfProdProdMatrixColProdMatrixRow ℂ (X₁₁ := ℂ) (X₂₂ := ℂ) (X₁₂ := ℂ) (X₂₁ := ℂ)

/-- The product identity matrix `⟨⟨𝐈,0⟩,⟨0,𝐈⟩⟩` for `X₁ = X₂ = ℂ`. -/
noncomputable abbrev idM : M := ⟨⟨1, 0⟩, ⟨0, 1⟩⟩

/-- The instance of `Prod.lean` has `identityMatrix = ⟨⟨𝐈,0⟩,⟨0,𝐈⟩⟩`. -/
theorem prod_identityMatrix_eq :
    (identityMatrix ℂ (ℂ × ℂ) : M) = idM := rfl

/-- Multiplying `(x₁, x₂)` by the product identity matrix gives `(0, x₂)`: the first block is
lost because the `ProdMatrixRow` instance passes `b = 0` to both blocks. -/
theorem prod_matVecMulAdd_identity (x₁ x₂ : ℂ) :
    matVecMulAdd (1:ℂ) idM (x₁, x₂) 0 ((0:ℂ), (0:ℂ)) = ((0:ℂ), x₂) := by
  show ((1:ℂ) * (0 * x₂) + 0 * ((1:ℂ) * (1 * x₁) + 0 * 0),
        (1:ℂ) * (1 * x₂) + 0 * ((1:ℂ) * (0 * x₁) + 0 * 0)) = ((0:ℂ), x₂)
  simp

/-- The product identity matrix does not act as the identity on `(1, 1)`. -/
theorem prod_identityMatrix_spec_false :
    matVecMulAdd (1:ℂ) idM ((1:ℂ), (1:ℂ)) 0 0 ≠ ((1:ℂ), (1:ℂ)) := by
  rw [show ((0 : ℂ × ℂ)) = ((0:ℂ), (0:ℂ)) from rfl, prod_matVecMulAdd_identity]
  simp

/-- The field `identityMatrix_spec` of the `Prod.lean` instance, which is proved there with
`sorry_proof`, implies `False`. (So this theorem uses `sorryProofAxiom`, through that field.) -/
theorem prod_identityMatrix_spec_inconsistent : False :=
  prod_identityMatrix_spec_false (prod_identityMatrix_eq ▸
    TensorProductSelf.identityMatrix_spec (R:=ℂ) (X:=ℂ × ℂ) (XX:=M) ((1:ℂ), (1:ℂ)))

end SciLean.ProdIdentityCounterexample
