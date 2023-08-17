namespace Eigen

--- Matrix Type ---
-------------------
-- It is just a wrapper around FloatArray storing dimensions

-- TODO: Add map option and stride
-- TODO: Add precision float vs double. Note that Lean's FloatArray is array of doubles
structure Matrix (n m : USize) where
  data : FloatArray 
  property : data.size = n.toNat * m.toNat

instance {n m : USize} : Inhabited (Matrix n m) := 
  ⟨FloatArray.mk (Array.mkArray (n.toNat*m.toNat) (0:Float)), sorry⟩

-- TODO: Proper rectangular printing of matrices
instance {n m : USize} : ToString (Matrix n m) := ⟨λ A => toString A.data⟩

abbrev Vector (n : USize) := Matrix n 1

-- Utiliti Functions used in C API ---
---------------------------------------

-- Curently there is no binary difference between FloatArray and Matrix.
-- These functions are identies at the end. This might change in the 
-- future, so using these function is advised

@[export eigenlean_get_matrix_array]
def Matrix.toArray {n m} (A : Matrix n m) : FloatArray := A.data

@[export eigenlean_array_to_matrix]
def FloatArray.toMatrix (array : FloatArray) (n m : USize) (property : array.size = n.toNat * m.toNat) : Matrix n m := ⟨array, property⟩

--- LDLT ---
------------

constant LDLT.nonemptytype (n : USize) : NonemptyType
def LDLT (n : USize) : Type := LDLT.nonemptytype n |>.type
instance {n : USize} : Nonempty (LDLT n) := LDLT.nonemptytype n |>.property

@[extern "eigenlean_ldlt"]
constant Matrix.ldlt (A : @& Matrix n n) : LDLT n

@[extern "eigenlean_ldlt_solve"]
constant LDLT.solve {n m} (ldlt : @& LDLT n) (rhs : @& Matrix n m) : Matrix n m

end Eigen

