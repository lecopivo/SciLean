import SciLean

open SciLean

variable (A : Float^[2,3]) (B : Float^[3,4])

-- Matrix multiplication (default output axes: `row col`)
#check (einsum[row shared, shared col] (A, B) : Float^[2,4])
#check (einsum[row shared, shared col -> row col] (A, B) : Float^[2,4])

variable (X : Float^[2,3])

-- Transpose / permutation
#check (einsum[row col -> col row] (X) : Float^[3,2])

-- Reduction (sum over `col`)
#check (einsum[row col -> row] (X) : Float^[2])

-- Full reduction to a scalar (sum over all axes)
#check (einsum[row col ->] (X) : Float)

-- Dot product is a scalar by default (axis appears twice so it is contracted)
variable (x y : Float^[3])
#check (einsum[feature, feature] (x, y) : Float)

-- Diagonals / trace (repeated axis inside one input group)
variable (M : Float^[3,3])
#check (einsum[diag diag ->] (M) : Float)
#check (einsum[diag diag -> diag] (M) : Float^[3])

-- Type annotations for axes (optional, but sometimes helpful)
#check (einsum[(row : Idx 2) (col : Idx 3) -> row] (X) : Float^[2])
