/-
Copyright (c) 2024 SciLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/

namespace SciLean.Kernel

/-- Data type enum for dtype-parametric kernel operations.
    Mirrors the C enum in kernel.h for FFI interop. -/
inductive DType where
  | f64      -- Float64 (8 bytes)
  | f32      -- Float32 (4 bytes)
  | f16      -- IEEE Float16 (2 bytes)
  | bf16     -- bfloat16 (2 bytes, 8-bit exp, 7-bit mantissa)
  | f8e4m3   -- FP8 E4M3 (1 byte, 4-bit exp, 3-bit mantissa)
  | f8e5m2   -- FP8 E5M2 (1 byte, 5-bit exp, 2-bit mantissa)
  | i32      -- Int32 (4 bytes)
  | i16      -- Int16 (2 bytes)
  | i8       -- Int8 (1 byte, for quantization)
  | u8       -- UInt8 (1 byte)
  deriving DecidableEq, Repr, Inhabited

namespace DType

/-- Byte size of each dtype. -/
def bytes : DType → Nat
  | .f64     => 8
  | .f32     => 4
  | .f16     => 2
  | .bf16    => 2
  | .f8e4m3  => 1
  | .f8e5m2  => 1
  | .i32     => 4
  | .i16     => 2
  | .i8      => 1
  | .u8      => 1

/-- Convert to UInt8 for FFI (matches C enum ordering). -/
def toUInt8 : DType → UInt8
  | .f64     => 0
  | .f32     => 1
  | .f16     => 2
  | .bf16    => 3
  | .f8e4m3  => 4
  | .f8e5m2  => 5
  | .i32     => 6
  | .i16     => 7
  | .i8      => 8
  | .u8      => 9

/-- Convert from UInt8 (FFI). Returns none for invalid values. -/
def fromUInt8? : UInt8 → Option DType
  | 0 => some .f64
  | 1 => some .f32
  | 2 => some .f16
  | 3 => some .bf16
  | 4 => some .f8e4m3
  | 5 => some .f8e5m2
  | 6 => some .i32
  | 7 => some .i16
  | 8 => some .i8
  | 9 => some .u8
  | _ => none

/-- Is this a floating-point type? -/
def isFloat : DType → Bool
  | .f64 | .f32 | .f16 | .bf16 | .f8e4m3 | .f8e5m2 => true
  | _ => false

/-- Is this an integer type? -/
def isInt : DType → Bool
  | .i32 | .i16 | .i8 | .u8 => true
  | _ => false

/-- Is this a signed type? -/
def isSigned : DType → Bool
  | .f64 | .f32 | .f16 | .bf16 | .f8e4m3 | .f8e5m2 => true
  | .i32 | .i16 | .i8 => true
  | .u8 => false

/-- Bit width of the type. -/
def bits : DType → Nat := fun dt => dt.bytes * 8

/-- Human-readable name. -/
def name : DType → String
  | .f64     => "float64"
  | .f32     => "float32"
  | .f16     => "float16"
  | .bf16    => "bfloat16"
  | .f8e4m3  => "fp8_e4m3"
  | .f8e5m2  => "fp8_e5m2"
  | .i32     => "int32"
  | .i16     => "int16"
  | .i8      => "int8"
  | .u8      => "uint8"

instance : ToString DType := ⟨DType.name⟩

/-- Total bytes needed for n elements of this dtype. -/
def totalBytes (dt : DType) (n : Nat) : Nat := dt.bytes * n

/-- Number of elements that fit in a given byte count. -/
def elemCount (dt : DType) (byteCount : Nat) : Nat := byteCount / dt.bytes

end DType

end SciLean.Kernel
