import Lean

open Lean Meta
initialize toAnyPointAttr : TagAttribute ← registerTagAttribute `to_any_point "Derive theorem to any point."
