import SciLean.Data.FunType.Properties

namespace SciLean

namespace FunType

  variable {T X Y : Type} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X]

  @[simp]
  theorem sum_intro [Enumtype ι] [Vec Y]
    (f : ι → X → Y) 
    : (∑ i, intro T (f i)) = (intro T (∑ i, f i) : T)
    := 
  by
    rw [sum_of_linear]
    done

  @[simp]
  theorem add_intro 
    (f g : X → Y) [Add Y]
    : 
      (intro T f : T) + (intro T g : T)
      = 
      (intro T λ x => f x + g x)
    := 
  by
    ext; simp[Add.add, HAdd.hAdd]; done

  @[simp]
  theorem sub_intro 
    (f g : X → Y) [Sub Y]
    : 
      (intro T f : T) - (intro T g : T)
      = 
      (intro T λ x => f x - g x)
    := 
  by
    ext; simp[Sub.sub, HSub.hSub]; done

  @[simp]
  theorem hmul_intro 
    (r : R) (f : X → Y) [HMul R Y Y]
    :
      r * (intro T f : T) = intro T (λ x => r * f x)
    := 
  by 
    ext; simp[HMul.hMul] done

  @[simp] 
  theorem getElem_sum {ι : Type} [Enumtype ι] [Vec Y] (f : ι → T) (x : X)
    : (∑ i, f i)[x] = ∑ i, (f i)[x] :=
  by 
    simp[← sum_of_linear (λ (t : T) => getElem t x True.intro)]; done

  @[simp]
  theorem sum_setElem_zero [Vec Y] (f : X → Y)
    : (∑ i, setElem 0 i (f i)) = intro T λ i : X => f i :=
  by 
    ext; simp; admit

  @[simp]
  theorem intro_map (f : Y → Y) (x : T)
    : intro _ (λ i => f x[i]) = map f x :=
  by 
    ext; simp
