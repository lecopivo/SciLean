

-- This file provides utilities for splitting strings into byte chunks
-- The API was updated for Lean 4.26 which deprecated Substring.mk and String.Pos

/-- Split a string into substrings that have maximum size in bytes
-/
partial def String.splitToByteChunks (str : String) (chunkByteSize : Nat) : Array Substring := Id.run do
  let mut chunks := #[]
  let mut s : String.Pos := ⟨0⟩
  let e : String.Pos := ⟨str.utf8ByteSize⟩
  while s < e do
    let mut s' := s
    while (str.next s').byteIdx - s.byteIdx ≤ chunkByteSize && s' < e do
      s' := str.next s'
    chunks := chunks.push ⟨str, s, s'⟩
    s := s'
  chunks
