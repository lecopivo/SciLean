import SciLean

open SciLean


def main : IO Unit := do

  IO.println (Float.tgamma 3.1415)
  IO.println (Float.lgamma 3.1415)

  IO.println (FloatArray.mk #[1.0,2.0,3.0,4.0,3.0])
  IO.println (FloatArray.mk #[1.0,2.0,3.0,4.0,3.0] |>.toByteArray)
  IO.println (FloatArray.mk #[1.0,2.0,3.0,4.0,3.0] |>.toByteArray |>.toFloatArray sorry_proof)
  IO.println (FloatArray.mk #[2.0,2.0,3.0,4.0,3.0] |>.toByteArray |>.toFloatArray sorry_proof)
