import SciLean.Algebra.TensorProduct.Basic


namespace SciLean

-- class TensorProductAssoc
--     (R X Y Z : Type*) {XY YZ XY_Z X_YZ : Type*} [RCLike R]
--     [NormedAddCommGroup X] [AdjointSpace R X]
--     [NormedAddCommGroup Y] [AdjointSpace R Y]
--     [NormedAddCommGroup Z] [AdjointSpace R Z]
--     [NormedAddCommGroup XY] [AdjointSpace R XY]
--     [NormedAddCommGroup YZ] [AdjointSpace R YZ]
--     [NormedAddCommGroup XY_Z] [AdjointSpace R XY_Z]
--     [NormedAddCommGroup X_YZ] [AdjointSpace R X_YZ]
--     [TensorProductType R X Y XY] [TensorProductType R Y Z YZ]
--     [TensorProductType R XY Z XY_Z] [TensorProductType R X YZ X_YZ]
--   where
--     tmulAssoc : XY_Z ≃L[R] X_YZ

--     assoc_tmul_tmul (x : X) (y : Y) (z : Z):
--       tmulAssoc ((x ⊗[R] y) ⊗[R] z)
--       =
--       x ⊗[R] (y ⊗[R] z)


-- variable
--     (R X Y Z XY YZ XY_Z X_YZ : Type*) [RCLike R]
--     [NormedAddCommGroup X] [AdjointSpace R X]
--     [NormedAddCommGroup Y] [AdjointSpace R Y]
--     [NormedAddCommGroup Z] [AdjointSpace R Z]
--     [NormedAddCommGroup XY] [AdjointSpace R XY]
--     [NormedAddCommGroup YZ] [AdjointSpace R YZ]
--     [NormedAddCommGroup XY_Z] [AdjointSpace R XY_Z]
--     [NormedAddCommGroup X_YZ] [AdjointSpace R X_YZ]
--     [TensorProductType R X Y XY] [TensorProductType R Y Z YZ]
--     [TensorProductType R XY Z XY_Z] [TensorProductType R X YZ X_YZ]

--     [TensorProductGetRXY R XY Z XY_Z]
--     [TensorProductGetRXY R X Y XY]

--     [TensorProductAssoc R X Y Z]


-- set_default_scalar R


-- def tmulAssoc {R X Y Z XY YZ XY_Z X_YZ : Type*} [RCLike R]
--     [NormedAddCommGroup X] [AdjointSpace R X]
--     [NormedAddCommGroup Y] [AdjointSpace R Y]
--     [NormedAddCommGroup Z] [AdjointSpace R Z]
--     [NormedAddCommGroup XY] [AdjointSpace R XY]
--     [NormedAddCommGroup YZ] [AdjointSpace R YZ]
--     [NormedAddCommGroup XY_Z] [AdjointSpace R XY_Z]
--     [NormedAddCommGroup X_YZ] [AdjointSpace R X_YZ]
--     [TensorProductType R X Y XY] [TensorProductType R Y Z YZ]
--     [TensorProductType R XY Z XY_Z] [TensorProductType R X YZ X_YZ]

--     [TensorProductGetRXY R XY Z XY_Z]
--     [TensorProductGetRXY R X Y XY]

--     [TensorProductAssoc R X Y Z]:
--     XY_Z ≃L[R] X_YZ :=
--   TensorProductAssoc.tmulAssoc X Y Z XY YZ



-- @[simp, simp_core]
-- theorem tmul_assoc (x : X) (y : Y) (z : Z) :
--    tmulAssoc ((x ⊗ y) ⊗ z) = (x ⊗ (y ⊗ z)) := sorry_proof

-- @[simp, simp_core]
-- theorem tmul_assoc_symm (x : X) (y : Y) (z : Z) :
--    tmulAssoc.symm (x ⊗ (y ⊗ z)) = (x ⊗ y) ⊗ z := sorry_proof
