
  instance : Hilbert ℝ :=
  {
    uniqueDomain := sorry
  }

  instance (X Y) [Hilbert X] [Hilbert Y] 
    : Hilbert (X × Y) := 
  {
    uniqueDomain := sorry
  }

  instance (X) [Hilbert X] (ι) [Enumtype ι] 
    : Hilbert (ι → X) := 
  {
    uniqueDomain := sorry
  }
