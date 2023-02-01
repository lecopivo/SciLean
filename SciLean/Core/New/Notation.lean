namespace SciLean




class Dagger (α : Type) (β : outParam Type) where
  dagger : α → β

postfix:max "†" => Dagger.dagger


class Integral (α : Type) (β : outParam Type) where
  integral : α → β 

prefix:max "∫" => Integral.integral


