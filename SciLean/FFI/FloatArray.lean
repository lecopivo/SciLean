@[extern "scilean_float_array_to_byte_array"]
opaque FloatArray.toByteArray (x : FloatArray) : ByteArray

@[extern "scilean_byte_array_to_float_array"]
opaque ByteArray.toFloatArray (x : ByteArray) (h : x.size % 8 = 0) : FloatArray
