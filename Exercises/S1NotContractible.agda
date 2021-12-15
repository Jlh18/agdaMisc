module Exercises.S1NotContractible where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

data S¹ : Type where
  base : S¹
  loop : base ≡ base

-- is general and has nothing to do with S¹
moveCentreToBase : {A : Type} (x : A) → isContr A → isContr A
moveCentreToBase x (c , hc) = x , (λ y → sym (hc x) ∙ hc y)

postulate
  h : isContr S¹

ToBase : (y : S¹) → base ≡ y
ToBase = snd (moveCentreToBase base h)

wallP : base ≡ base
wallP = ToBase base

fillWallP : PathP (λ i → wallP i ≡ wallP i) refl loop
fillWallP = λ i j → ToBase (loop j) i

-- general
inf : {A : Type} (x : A) (p : x ≡ x) →
  PathP (λ i → p i ≡ x) p refl
inf x p = λ i j → sym p (~ i ∧ ~ j)

refl≡loopAux : ((sym wallP) ∙ refl ∙ wallP) ≡ (sym refl) ∙ loop ∙ refl
refl≡loopAux = λ j → sym (inf base wallP j)
                 ∙ (fillWallP j)
                 ∙ inf base wallP j

refl≡loop : refl ≡ loop
refl≡loop =
    refl
  ≡⟨ sym (lCancel _) ⟩
    sym wallP ∙ wallP
  ≡⟨ cong (λ p → sym wallP ∙ p) (lUnit _) ⟩
    ((sym wallP) ∙ (refl ∙ wallP))
  ≡⟨ refl≡loopAux ⟩
    ((sym refl) ∙ loop ∙ refl)
  ≡⟨ cong (λ p → sym refl ∙ p) (sym (rUnit _)) ⟩
    sym refl ∙ loop
  ≡⟨ cong (λ p → p ∙ loop) symRefl ⟩
    refl ∙ loop
  ≡⟨ sym (lUnit _) ⟩
    loop ∎

-- refl≡loop : PathP (λ i → base ≡ loop i) refl refl → refl ≡ loop
-- refl≡loop h = λ i j → h j i
