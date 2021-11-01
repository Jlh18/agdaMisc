module HLevel.Hedberg where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sum renaming (_⊎_ to _⊔_ ; rec to ⊔Rec)
open import Cubical.Data.Empty renaming (rec to ⊥Rec)

private
  variable
    v u : Level

-- isDecidable : {A : Type u} (P : A → Type v) → A → Type v
-- isDecidable {A} P a = P a ⊔ (P a → ⊥)

¬ : Type u → Type u
¬ P = P → ⊥

isProp¬¬ : {A : Type} → isProp (¬ (¬ A))
isProp¬¬ = isProp→ isProp⊥

dec≡ : Type u → Type u
dec≡ A = (x y : A) → (x ≡ y) ⊔ ¬ (x ≡ y)

¬¬≡→≡ : Type u → Type u
¬¬≡→≡ A = (x y : A) → (¬ (¬ (x ≡ y))) → x ≡ y

dec≡→¬¬≡→≡ : {A : Type u} → dec≡ A → ¬¬≡→≡ A
dec≡→¬¬≡→≡ h x y = ⊔Rec
  (λ h≡ _ → h≡)
  (λ h¬≡ h⊥ → ⊥Rec (h⊥ h¬≡))
  (h x y)


loopsTrivial : Type u → Type u
loopsTrivial A = (x : A) (p : x ≡ x) → p ≡ refl

loopsTrivial→isSet : {A : Type u} → loopsTrivial A → isSet A
loopsTrivial→isSet h x _ = J (λ y p → (q : x ≡ y) → p ≡ q) λ q → sym (h x q)

fiberCong : {A : Type u} {B : A → Type v} (f : (a : A) → B a) {x y : A} (p : x ≡ y)
  → subst B p (f x) ≡ f y
fiberCong f {x} {y} p = Iso.fun (PathPIsoPath _ (f x) (f y)) (cong f p)

PathLeftCancel : {A : Type} {x y : A} (p : x ≡ y) {z : A} (q r : y ≡ z) → p ∙ q ≡ p ∙ r → q ≡ r
PathLeftCancel {A} = J (λ y p → {z : A} → (q r : y ≡ z) → p ∙ q ≡ p ∙ r → q ≡ r)
  λ q r h → q ≡⟨ lUnit q ⟩ refl ∙ q ≡⟨ h ⟩ refl ∙ r ≡⟨ sym (lUnit r) ⟩ r ∎

substPathFibration : {A : Type u} {x y z : A} (q : x ≡ y) (p : y ≡ z) →
  subst (_≡_ x) p q ≡ q ∙ p
substPathFibration {u} {A} {x} {y} {z} q p = J (λ z p → subst (_≡_ x) p q ≡ q ∙ p)
                                (
                                  subst (_≡_ x) refl q
                                ≡⟨ transportRefl q ⟩
                                  q
                                ≡⟨ rUnit q ⟩
                                  q ∙ refl ∎''
                                )
                                p

substFunExt-fun : {A : Type u} (Bs Bt : A → Type v)
  {x y : A} (p : x ≡ y) (f : Bs x → Bt x) (g : Bs y → Bt y) →
  subst (λ a → Bs a → Bt a) p f ≡ g →
  (s : Bs x) → subst Bt p (f s) ≡ g (subst Bs p s)
substFunExt-fun {A} Bs Bt {x} = J
  (
    λ y p → (f : Bs x → Bt x) (g : Bs y → Bt y) →
    subst (λ a → Bs a → Bt a) p f ≡ g →
    (s : Bs x) → subst Bt p (f s) ≡ g (subst Bs p s)
  )
  λ f g h s →

  let f≡g : f ≡ g
      f≡g =
          f
        ≡⟨ sym (substRefl {B = λ a → Bs a → Bt a} f) ⟩
          subst (λ a → Bs a → Bt a) refl f
        ≡⟨ h ⟩
          g ∎ in

    subst Bt refl (f s)
  ≡⟨ substRefl {B = Bt} (f s) ⟩
    f s
  ≡⟨ (λ i → (f≡g i) s) ⟩
    g s
  ≡⟨ cong g (sym (substRefl {B = Bs} s )) ⟩
    g (subst Bs refl s) ∎

dec≡→loopsTrivial : {A : Type} → dec≡ A → loopsTrivial A
dec≡→loopsTrivial {A} h x p = PathLeftCancel (hLoops r) p refl h'xr∙p≡h'xr∙refl

  where

  Bs : A → Type
  Bs = λ y → ¬ (¬ (x ≡ y))

  Bt : A → Type
  Bt = λ y → x ≡ y

  hLoops : Bs x → Bt x
  hLoops = dec≡→¬¬≡→≡ h x x

  -- lemma to be used in substFunExt-fun
  lem : subst (λ y → ¬ (¬ (x ≡ y)) → x ≡ y) p hLoops ≡ hLoops
  lem = fiberCong (dec≡→¬¬≡→≡ h x) p

  r : ¬ (¬ ( x ≡ x ))
  r = λ h → ⊥Rec (h p)

  h'xr∙p≡h'xr∙refl : (hLoops r) ∙ p ≡ hLoops r ∙ refl
  h'xr∙p≡h'xr∙refl =
      hLoops r ∙ p
    ≡⟨ sym (substPathFibration _ _) ⟩
      subst (_≡_ x) p (hLoops r)
    ≡⟨ substFunExt-fun Bs Bt p hLoops hLoops lem r ⟩
     hLoops (subst Bs p r)
    ≡⟨ cong hLoops (isProp¬¬ _ _) ⟩
     hLoops r
    ≡⟨ rUnit _ ⟩
     hLoops r ∙ refl ∎

Hedberg : {A : Type} → dec≡ A → isSet A
Hedberg h = loopsTrivial→isSet (dec≡→loopsTrivial h)
