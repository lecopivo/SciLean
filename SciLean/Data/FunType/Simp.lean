import SciLean.Data.FunType.Basic
import SciLean.Data.FunType.Properties

namespace SciLean


variable {T X Y} [FunType T X Y] 

namespace FunType

  variable [HasSet T] [HasIntro T] [Enumtype X] [Inhabited Y]

  example [Add Y] : Add T := by infer_instance

  @[simp]
  theorem sum_intro [Enumtype ι] [Vec Y]
    (f : ι → X → Y) 
    : (∑ i, intro (f i)) = (intro (∑ i, f i) : T)
    := 
  by
    rw [sum_of_linear intro f]
    done

  @[simp]
  theorem add_intro 
    (f g : X → Y) [Add Y]
    : 
      (intro f : T) + (intro g : T)
      = 
      (intro λ x => f x + g x)
    := 
  by
    ext; intro x
    simp[Add.add, HAdd.hAdd]; done

  @[simp]
  theorem sub_intro 
    (f g : X → Y) [Sub Y]
    : 
      (intro f : T) - (intro g : T)
      = 
      (intro λ x => f x - g x)
    := 
  by
    ext; intro x
    simp[Sub.sub, HSub.hSub]; done

  @[simp]
  theorem hmul_intro 
    (r : R) (f : X → Y) [HMul R Y Y]
    :
      r * (intro f : T) = intro (λ x => r * f x)
    := 
  by 
    ext; intro x
    simp[HMul.hMul] done

