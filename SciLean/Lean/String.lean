

/-- Split a string into substrings that have maximum size in bytes -/
partial def String.splitToByteChunks (str : String) (chunkByteSize : Nat) : Array Substring.Raw := Id.run do
  let mut chunks : Array Substring.Raw := #[]
  let mut s : Nat := 0
  let e : Nat := str.endPos.offset.byteIdx
  while s < e do
    let mut s' := s
    while (str.next ⟨s'⟩).byteIdx - s ≤ chunkByteSize && s' < e do
      s' := (str.next ⟨s'⟩).byteIdx
    chunks := chunks.push ⟨str, ⟨s⟩, ⟨s'⟩⟩
    s := s'
  chunks
