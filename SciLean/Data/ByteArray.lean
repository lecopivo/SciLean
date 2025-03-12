
/-- Get `i`-th float out of `ByteArray` if interpreted as `FloatArray` -/
@[extern c inline "((double*)(lean_sarray_cptr(#1)))[#2]"]
-- @[extern "scilean_byte_array_uget_float"]
opaque ByteArray.ugetFloat (a : @& ByteArray) (i : USize) (hi : i.toNat*8 + 7 < a.size) : Float


@[extern c inline "(((double*)(lean_sarray_cptr(#1)+#2))[0])"]
-- @[extern "scilean_byte_array_uget_float"]
opaque ByteArray.ugetFloatAtByte (a : @& ByteArray) (i : USize) (hi : i.toNat + 7 < a.size) : Float
