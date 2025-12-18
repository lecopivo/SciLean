/-!
# Float32 Array FFI

Native Float32 (32-bit float) array operations via FFI.
This provides direct memory access without double↔float conversion overhead.
-/

/-- Read a Float32 from ByteArray at byte offset `i`. -/
@[extern "scilean_byte_array_uget_float32"]
opaque ByteArray.ugetFloat32 (a : @& ByteArray) (i : USize) : Float32

/-- Set a Float32 in ByteArray at byte offset `i`. Unsafe: no bounds checking. -/
@[extern "scilean_byte_array_uset_float32"]
unsafe opaque ByteArray.usetFloat32Unsafe (a : ByteArray) (i : USize) (v : Float32) : ByteArray

/-- Safe wrapper for setting Float32 in ByteArray. -/
@[implemented_by ByteArray.usetFloat32Unsafe]
opaque ByteArray.usetFloat32 (a : ByteArray) (i : USize) (v : Float32) : ByteArray := a

/-- Create a ByteArray filled with n copies of a Float32 value. -/
def ByteArray.replicateFloat32 (n : Nat) (v : Float32) : ByteArray := Id.run do
  let mut arr := ByteArray.empty
  -- Pre-allocate by pushing zeros
  for _ in [:n * 4] do
    arr := arr.push 0
  -- Fill with Float32 values
  for i in [:n] do
    arr := arr.usetFloat32 (i * 4).toUSize v
  return arr

/-- Get the number of Float32 elements in a ByteArray. -/
def ByteArray.float32Size (a : ByteArray) : Nat := a.size / 4

/-- Convert ByteArray to list of Float32 values. -/
def ByteArray.toFloat32List (a : ByteArray) : List Float32 := Id.run do
  let mut result : List Float32 := []
  for i in [:a.float32Size] do
    result := result ++ [a.ugetFloat32 (i * 4).toUSize]
  return result
