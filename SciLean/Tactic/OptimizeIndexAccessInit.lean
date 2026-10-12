module

public import Lean

public meta import Lean

@[expose] public meta section


namespace SciLean

-- simp attribute for optimizing index access
register_simp_attr optimize_index_access
