import Mathlib.Algebra.Group.Basic

section ProductOperations

  variable {α : Type u} {β : Type v} {γ : Type w}

  instance [Add α] [Add β] : Add (α × β) := ⟨λ p q => (p.1 + q.1, p.2 + q.2)⟩
  instance [Sub α] [Sub β] : Sub (α × β) := ⟨λ p q => (p.1 - q.1, p.2 - q.2)⟩
  instance [Mul α] [Mul β] : Mul (α × β) := ⟨λ p q => (p.1 * q.1, p.2 * q.2)⟩
  instance [Div α] [Div β] : Div (α × β) := ⟨λ p q => (p.1 / q.1, p.2 / q.2)⟩

  -- instance {α β γ} [HAdd α γ α] [HAdd β γ β] : HAdd (α×β) γ (α×β) := ⟨λ p c => (p.1+c, p.2+c)⟩
  -- instance {α β γ} [HAdd γ α α] [HAdd γ β β] : HAdd γ (α×β) (α×β) := ⟨λ c p => (c+p.1, c+p.2)⟩
  -- instance {α β γ} [HSub α γ α] [HSub β γ β] : HSub (α×β) γ (α×β) := ⟨λ p c => (p.1-c, p.2-c)⟩
  -- instance {α β γ} [HMul α γ α] [HMul β γ β] : HMul (α×β) γ (α×β) := ⟨λ p c => (p.1*c, p.2*c)⟩
  instance {α β γ} [HMul γ α α] [HMul γ β β] : HMul γ (α×β) (α×β) := ⟨λ c p => (c*p.1, c*p.2)⟩
  -- instance {α β γ} [HDiv α γ α] [HDiv β γ β] : HDiv (α×β) γ (α×β) := ⟨λ p c => (p.1/c, p.2/c)⟩

  instance [Neg α] [Neg β] : Neg (α × β) := ⟨λ p => (-p.1, -p.2)⟩

  instance [Zero α] [Zero β] : Zero (α × β) := ⟨(0, 0)⟩
  instance [One α] [One β] : One (α × β) := ⟨(1, 1)⟩

  theorem prod_neg_elemwise [Neg X] [Neg Y] (xy : X × Y) : - xy = (- xy.1, - xy.2) := by simp[Neg.neg] done
  theorem prod_add_elemwise [Add X] [Add Y] (xy xy' : X × Y) : xy + xy' = (xy.1 + xy'.1, xy.2 + xy'.2) := by simp[HAdd.hAdd,Add.add] done
  theorem prod_sub_elemwise [Sub X] [Sub Y] (xy xy' : X × Y) : xy - xy' = (xy.1 - xy'.1, xy.2 - xy'.2) := by simp[HSub.hSub,Sub.sub] done
  theorem prod_mul_elemwise [Mul X] [Mul Y] (xy xy' : X × Y) : xy * xy' = (xy.1 * xy'.1, xy.2 * xy'.2) := by simp[HMul.hMul,Mul.mul] done
  theorem prod_div_elemwise [Div X] [Div Y] (xy xy' : X × Y) : xy / xy' = (xy.1 / xy'.1, xy.2 / xy'.2) := by simp[HDiv.hDiv,Div.div] done

  theorem prod_hmul_elemwise [HMul α X X] [HMul α Y Y] (xy : X × Y) (a : α) : a * xy = (a * xy.1, a * xy.2) := by simp[HMul.hMul] done

  theorem prod_one_elemwise [One X] [One Y] : (1 : X×Y) = (1,1) := by simp[One.one, OfNat.ofNat] done
  theorem prod_zero_elemwise [Zero X] [Zero Y] : (0 : X×Y) = (0,0) := by simp[OfNat.ofNat, Zero.zero] done

end ProductOperations
