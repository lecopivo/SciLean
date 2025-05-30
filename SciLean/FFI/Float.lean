namespace Float
/-- The gamma function. -/
@[extern "scilean_float_tgamma"]
opaque tgamma (x : Float) : Float

/-- The natural logarithm of the absolute value of the gamma function. -/
@[extern "scilean_float_lgamma"]
opaque lgamma (x : Float) : Float
