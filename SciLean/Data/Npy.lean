/-
NumPy .npy File Format Support for SciLean

Adapted from TensorLib (Apache 2.0 License)
https://github.com/leanprover/TensorLib

Provides loading/saving of tensors in NumPy's binary format for data interchange.
-/
import SciLean.Data.DataArray.DataArray
import SciLean.Data.DataArray.TensorOperations
import SciLean.FFI.FloatArray

namespace SciLean.Npy

/-! ## Error Handling -/

abbrev Err := Except String

/-! ## Numpy Dtype -/

inductive Dtype where
  | bool
  | int8 | int16 | int32 | int64
  | uint8 | uint16 | uint32 | uint64
  | float32 | float64
  deriving BEq, Repr, Inhabited

namespace Dtype

def itemsize : Dtype → Nat
  | bool | int8 | uint8 => 1
  | int16 | uint16 => 2
  | int32 | uint32 | float32 => 4
  | int64 | uint64 | float64 => 8

def fromNpyString (s : String) : Err Dtype := match s with
  | "b1" => .ok .bool
  | "i1" => .ok .int8
  | "i2" => .ok .int16
  | "i4" => .ok .int32
  | "i8" => .ok .int64
  | "u1" => .ok .uint8
  | "u2" => .ok .uint16
  | "u4" => .ok .uint32
  | "u8" => .ok .uint64
  | "f4" => .ok .float32
  | "f8" => .ok .float64
  | _ => .error s!"Unknown dtype: {s}"

def toNpyString : Dtype → String
  | .bool => "b1"
  | .int8 => "i1" | .int16 => "i2" | .int32 => "i4" | .int64 => "i8"
  | .uint8 => "u1" | .uint16 => "u2" | .uint32 => "u4" | .uint64 => "u8"
  | .float32 => "f4" | .float64 => "f8"

end Dtype

/-! ## Byte Order -/

inductive ByteOrder where
  | native        -- '='
  | littleEndian  -- '<'
  | bigEndian     -- '>'
  | notApplicable -- '|'
  deriving BEq, Repr, Inhabited

namespace ByteOrder

def fromChar (c : Char) : Err ByteOrder := match c with
  | '=' => .ok .native
  | '<' => .ok .littleEndian
  | '>' => .ok .bigEndian
  | '|' => .ok .notApplicable
  | _ => .error s!"Unknown byte order: {c}"

def toChar : ByteOrder → Char
  | .native => '='
  | .littleEndian => '<'
  | .bigEndian => '>'
  | .notApplicable => '|'

end ByteOrder

/-! ## Shape -/

structure Shape where
  dims : List Nat
  deriving BEq, Repr, Inhabited

namespace Shape

def count (s : Shape) : Nat := s.dims.foldl (· * ·) 1

def ndim (s : Shape) : Nat := s.dims.length

end Shape

/-! ## Npy Header and Array -/

structure Header where
  major : UInt8 := 1
  minor : UInt8 := 0
  dtype : Dtype
  order : ByteOrder
  shape : Shape
  deriving Repr, Inhabited

structure NpyArray where
  header : Header
  data : ByteArray
  startIndex : Nat  -- First byte of actual data
  deriving Inhabited

namespace NpyArray

def nbytes (arr : NpyArray) : Nat := arr.header.dtype.itemsize * arr.header.shape.count

def dtype (arr : NpyArray) : Dtype := arr.header.dtype

def shape (arr : NpyArray) : Shape := arr.header.shape

end NpyArray

/-! ## Parsing -/

section Parse

private structure ParseState where
  source : ByteArray
  index : Nat
  headerEnd : Nat
  dtype : Option (Dtype × ByteOrder)
  fortranOrder : Option Bool
  shape : Option Shape

private abbrev PState (T : Type) := EStateM String ParseState T

private instance : MonadLiftT Err PState where
  monadLift x := match x with
    | .ok x => .ok x
    | .error x => .error x

private def resultExcept (x : EStateM.Result String ParseState a) : Err a := match x with
  | .ok x _ => .ok x
  | .error x _ => .error x

private def npyBool (s : String) : Err Bool := match s with
  | "True" => .ok true
  | "False" => .ok false
  | _ => .error s!"Invalid bool: {s}"

private def whitespace : PState Unit := do
  let s ← get
  let mut count := 0
  for i in [s.index : s.headerEnd] do
    let c := Char.ofUInt8 s.source[i]!
    if c.isWhitespace then count := count + 1 else break
  set { s with index := s.index + count }

private def tryParse (p : PState T) : PState (Option T) := fun s =>
  match p s with
  | .error _ s => .ok none s
  | .ok x s => .ok (some x) s

private def ignore (p : PState T) : PState Unit := do
  let _ ← tryParse p

private def parseToken : PState String := do
  whitespace
  let s ← get
  let mut token := ""
  for i in [s.index : s.headerEnd] do
    let c := Char.ofUInt8 s.source[i]!
    if c.isAlphanum || c = '_' || c = '<' || c = '>' || c = '|' || c = '=' then
      token := token.push c
    else break
  if token.length != 0 then
    set { s with index := s.index + token.length }
    return token
  else
    .error "Can't parse token"

private def consume (c : Char) : PState Unit := do
  whitespace
  let s ← get
  if s.source[s.index]! == c.toUInt8 then
    set { s with index := s.index + 1 }
  else
    .error s!"Expected '{c}' at index {s.index}"

private def quote : PState Unit := consume '\''
private def colon : PState Unit := consume ':'
private def comma : PState Unit := consume ','

private def quoted (p : PState T) : PState T := do
  quote; let x ← p; quote; return x

private partial def parseCommaListAux (p : PState T) (acc : List T) : PState (List T) := do
  let v ← tryParse p
  match v with
  | none => return acc.reverse
  | some x =>
    ignore comma
    parseCommaListAux p (x :: acc)

private def parseCommaList (start : Char) (end_ : Char) (p : PState T) : PState (List T) := do
  consume start
  let xs ← parseCommaListAux p []
  consume end_
  return xs

private def parseShape : PState Shape := do
  let xs ← parseCommaList '(' ')' parseToken
  return Shape.mk (xs.map (·.toNat!))

private def parseNpyHeader : PState (UInt8 × UInt8) := do
  let s ← get
  let b := s.source
  if s.index != 0 then .error "Invalid start index"
  if b.size < 10 then .error s!"Buffer too small: {b.size}"
  if b[0]! != 0x93 then .error "Invalid magic byte"
  if b[1]! != 'N'.toUInt8 then .error "Expected 'N'"
  if b[2]! != 'U'.toUInt8 then .error "Expected 'U'"
  if b[3]! != 'M'.toUInt8 then .error "Expected 'M'"
  if b[4]! != 'P'.toUInt8 then .error "Expected 'P'"
  if b[5]! != 'Y'.toUInt8 then .error "Expected 'Y'"
  let major := b[6]!
  let minor := b[7]!
  let headerLength := b[8]!.toNat + b[9]!.toNat * 256
  set { s with index := 10, headerEnd := 10 + headerLength }
  return (major, minor)

private def parseOneMetadata : PState Unit := do
  let id ← quoted parseToken
  colon
  if id == "descr" then
    let v ← quoted parseToken
    if v.length < 2 then .error s!"Invalid dtype string: {v}"
    let firstChar := v.data[0]!
    let order ← ByteOrder.fromChar firstChar
    let dtype ← Dtype.fromNpyString (v.drop 1)
    modify fun s => { s with dtype := some (dtype, order) }
  else if id == "fortran_order" then
    let v ← parseToken
    let b ← liftM (npyBool v)
    modify fun s => { s with fortranOrder := some b }
  else if id == "shape" then
    let shape ← parseShape
    modify fun s => { s with shape := some shape }
  else .error s!"Unknown metadata: {id}"

private def parseMetadata : PState Unit := do
  consume '{'
  parseOneMetadata; comma
  parseOneMetadata; comma
  parseOneMetadata
  ignore comma
  consume '}'

private def parseNpyRepr : PState NpyArray := do
  let (major, minor) ← parseNpyHeader
  parseMetadata
  let s ← get
  match s.dtype, s.shape with
  | some (dtype, order), some shape =>
    match s.fortranOrder with
    | .none | .some false => pure ()
    | .some true => .error "Fortran order not supported (transpose in Python first)"
    let header := Header.mk major minor dtype order shape
    return NpyArray.mk header s.source s.headerEnd
  | _, _ => .error "Missing dtype or shape in header"

end Parse

/-! ## Public API -/

/-- Parse a .npy file from a ByteArray -/
def parse (buffer : ByteArray) : Err NpyArray := do
  let init := ParseState.mk buffer 0 0 none none none
  resultExcept (parseNpyRepr.run init)

/-- Load a .npy file from disk -/
def loadFile (path : System.FilePath) : IO NpyArray := do
  let buffer ← IO.FS.readBinFile path
  IO.ofExcept (parse buffer)

/-! ## Conversion to SciLean Types -/

/-- Extract float64 data as FloatArray -/
def NpyArray.toFloatArray (arr : NpyArray) : Err FloatArray := do
  if arr.dtype != .float64 then
    .error s!"Expected float64, got {repr arr.dtype}"
  let dataBytes := arr.data.copySlice arr.startIndex ByteArray.empty 0 arr.nbytes
  -- Reinterpret bytes as floats (assumes little-endian, 8 bytes per float)
  return dataBytes.toFloatArray sorry_proof

/-- Convert float32 IEEE 754 bits to float64 -/
private def float32BitsToFloat64 (bits : UInt32) : Float :=
  -- IEEE 754 float32: 1 sign, 8 exponent, 23 mantissa
  let sign := if bits &&& 0x80000000 != 0 then -1.0 else 1.0
  let exp := ((bits >>> 23) &&& 0xFF).toNat
  let mant := bits &&& 0x7FFFFF
  if exp == 0 then
    -- Subnormal or zero
    if mant == 0 then sign * 0.0
    else sign * (mant.toFloat / (2^23).toFloat) * Float.pow 2.0 (-126.0)
  else if exp == 255 then
    -- Infinity or NaN
    if mant == 0 then sign * Float.inf else Float.nan
  else
    -- Normal number
    let e := exp.toFloat - 127.0
    let m := 1.0 + mant.toFloat / (2^23).toFloat
    sign * m * Float.pow 2.0 e

/-- Extract float32 data, converting to Float (float64) -/
def NpyArray.toFloatArrayFromFloat32 (arr : NpyArray) : Err FloatArray := do
  if arr.dtype != .float32 then
    .error s!"Expected float32, got {repr arr.dtype}"
  let n := arr.header.shape.count
  let mut result : FloatArray := .emptyWithCapacity n
  for i in [0:n] do
    let offset := arr.startIndex + i * 4
    -- Read 4 bytes as float32 bits (little-endian)
    let b0 := arr.data[offset]!.toUInt32
    let b1 := arr.data[offset + 1]!.toUInt32
    let b2 := arr.data[offset + 2]!.toUInt32
    let b3 := arr.data[offset + 3]!.toUInt32
    let bits := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
    result := result.push (float32BitsToFloat64 bits)
  return result

/-- Load a .npy file as DataArrayN Float with static shape -/
def loadFloat64 {ι : Type} {n : Nat} [IndexType ι n]
    (path : System.FilePath) : IO (DataArrayN Float ι) := do
  let arr ← loadFile path
  let floats ← IO.ofExcept arr.toFloatArray
  if floats.size != n then
    throw (IO.userError s!"Shape mismatch: file has {floats.size} elements, expected {n}")
  return DataArrayN.fromFloatArray floats

/-- Load a .npy file as DataArrayN Float from float32 data -/
def loadFloat32 {ι : Type} {n : Nat} [IndexType ι n]
    (path : System.FilePath) : IO (DataArrayN Float ι) := do
  let arr ← loadFile path
  let floats ← IO.ofExcept arr.toFloatArrayFromFloat32
  if floats.size != n then
    throw (IO.userError s!"Shape mismatch: file has {floats.size} elements, expected {n}")
  return DataArrayN.fromFloatArray floats

/-! ## Saving -/

private def pushString (a : ByteArray) (s : String) : ByteArray := a.append s.toUTF8

/-- Save a FloatArray to .npy format -/
def saveFloatArray (arr : FloatArray) (shape : List Nat) (path : System.FilePath) : IO Unit := do
  -- Build header
  let mut header := ByteArray.empty
  header := header.push 0x93
  header := pushString header "NUMPY"
  header := header.push 1  -- major version
  header := header.push 0  -- minor version
  header := header.push 0  -- placeholder for header length
  header := header.push 0

  -- Metadata dict
  let shapeStr := "(" ++ String.intercalate ", " (shape.map toString) ++ ",)"
  let dictStr := "{'descr': '<f8', 'fortran_order': False, 'shape': " ++ shapeStr ++ ", }"

  header := pushString header dictStr

  -- Pad to 64-byte alignment
  let padding := 64 - ((header.size + 1) % 64)
  for _ in [0:padding] do
    header := header.push 0x20
  header := header.push 0x0a  -- newline

  -- Write header length (little-endian, at bytes 8-9)
  let headerLen := header.size - 10
  header := header.set! 8 headerLen.toUInt8
  header := header.set! 9 (headerLen / 256).toUInt8

  -- Append data
  let data := arr.toByteArray
  let result := header.append data

  IO.FS.writeBinFile path result

/-- Save DataArrayN to .npy file -/
def save {ι : Type} {n : Nat} [IndexType ι n]
    (arr : DataArrayN Float ι) (shape : List Nat) (path : System.FilePath) : IO Unit := do
  let floatArr := DataArrayN.toFloatArray arr
  saveFloatArray floatArr shape path

end SciLean.Npy
