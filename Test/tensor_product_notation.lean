import SciLean

open SciLean

set_default_scalar Float


#eval ⊞[1.0,2,3]

#eval ByteArray.replicate 10 1


/-- info: 𝐈 : Float^[2, 2] -/
#guard_msgs in
#check 𝐈[Float, 2]


/-- info: 𝐈 : Float^[[3, 3], 3, 3] -/
#guard_msgs in
#check 𝐈[Float, Float^[3,3]]


/-- info: 𝐈 : Float^[3, 3] -/
#guard_msgs in
#check (𝐈[_, _] : Float^[3,3])


/-- info: 𝐈 : Float^[3, 3] -/
#guard_msgs in
#check (𝐈 : Float^[3,3])


/-- info: 𝐈 : Float^[3, 3] -/
#guard_msgs in
#check (𝐈[Float, _] : Float^[3,3])


/-- info: ⊞[1.000000, 0.000000, 0.000000, 1.000000] -/
#guard_msgs in
#eval 𝐈[Float, 2]
