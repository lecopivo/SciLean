
noncomputable 
def Quot.repr {S : α → α → Prop} (a : Quot S) : α := Classical.choose a.exists_rep

namespace SciLean

  abbrev Rel (α : Type u) := α → α → Prop

  class IsQHom (S : Rel α) (R : Rel β) (f : α → β) where
    is_hom : ∀ a a', S a a' → R (f a) (f a')

  class IsQHom₂ (S : Rel α) (R : Rel β) (T : Rel γ) (f : α → β → γ) where
    is_hom : ∀ a a' b b', S a a' → R b b' → T (f a b) (f a' b')

  notation "⟦" x "⟧" => Quot.mk _ x
  notation "⟦" x ", " S "⟧" => Quot.mk S x

  def IsQHom.sound {S : Rel α} {R : Rel β} (f : α → β) [IsQHom S R f] 
    : ∀ a a', S a a' → ⟦f a⟧ = ⟦f a', R⟧
    := 
  by
    intros a a' h;
    apply Quot.sound;
    apply IsQHom.is_hom a a' h
    done

  def IsQHom₂.sound {S : Rel α} {R : Rel β} {T : Rel γ} (f : α → β → γ) [IsQHom₂ S R T f] 
    : ∀ a a' b b', S a a' → R b b' → ⟦f a b⟧ = ⟦f a' b', T⟧
    :=
  by
    intros a a' b b' h h';
    apply Quot.sound;
    apply IsQHom₂.is_hom a a' b b' h h'
    done

  notation "⟦" f "⟧" => Quot.lift (λ x => Quot.mk _ (f x)) (IsQHom.sound f)
  notation "⟦" f ", " S ", " R"⟧" => Quot.lift (r := S) (λ x => Quot.mk R (f x)) (IsQHom.sound f)

  instance : Coe α (Quot (Eq : α → α → Prop)) := 
  ⟨ λ a => Quot.mk _ a ⟩

  -- This one seem to be dangerous :(
  -- instance : Coe (Quot (Eq : α → α → Prop)) α := 
  -- ⟨ λ a => Quot.lift id (by intro a b h; apply h; done) a ⟩

  ---------------------

  instance (f : α → β) : IsQHom Eq Eq f := sorry

  instance (S : Rel α) : IsQHom S S (λ x => x) := sorry

  instance (S : Rel α) (R : Rel β) (T : Rel γ) 
    (f : β → γ) (g : α → β)
    [IsQHom R T f] [IsQHom S R g]
    : IsQHom S T (f ∘ g)
    := sorry

  ---------------------

  @[simp]
  theorem quot_comp
    (S : Rel α) (R : Rel β) (T : Rel γ) 
    (f : β → γ) (g : α → β) [IsQHom R T f] [IsQHom S R g]
    :
    ⟦f, R, T⟧ ∘ ⟦g, S, R⟧ = ⟦f ∘ g, S, T⟧
    := 
    sorry

  @[simp]
  theorem quot_apply {S : Rel α} {R : Rel β} (f : α → β) [IsQHom S R f] (a : Quot S)
    : ⟦f a.repr, R⟧ = ⟦f⟧ a
    := sorry

  ---------------------
 
  variable {f : α → β} {S : Rel α} {R : Rel β} {a : α} [IsQHom S R f]

  #check Eq

  #check ⟦f, Eq, Eq⟧ ⟦a, Eq⟧
  #check ⟦f, Eq, Eq⟧ ⟦a⟧
  #check ⟦f, Eq, Eq⟧ a

  #check ⟦f, S, R⟧ ⟦a, S⟧
  #check ⟦f, S, R⟧ ⟦a⟧

  #check ⟦f, S, R⟧
  #check (⟦f⟧ ⟦a⟧ : Quot R)

  -- ⟦f⟧ ∘ ⟦g⟧ = ⟦f ∘ g⟧
  -- ⟦f x.repr⟧ = ⟦f⟧ x
  -- ⟦f⟧ ⟦x⟧ = ⟦f x⟧

end SciLean








