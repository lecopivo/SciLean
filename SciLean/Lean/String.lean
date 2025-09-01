

/-- Split a string into substrings that have maximum size in bytes
-/
partial def String.splitToByteChunks (str : String) (chunkByteSize : Nat) : Array Substring := Id.run do
  let mut chunks := #[]
  let mut s : String.Pos := 0
  let e : String.Pos := str.endPos
  while s < e do
    let mut s' := s
    while (str.next s' - s).byteIdx ≤ chunkByteSize && s' < e do
      s' := str.next s'
    chunks := chunks.push (Substring.mk str s s')
    s := s'
  chunks
