module HLevel.SetLoopSpaceUnit where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)


private
  variable
    A : Type

isSet→LoopSpace≡⊤ : (x : A) → isSet A → (x ≡ x) ≡ ⊤
isSet→LoopSpace≡⊤ x h = isoToPath (iso (λ p → tt) inv rightInv leftInv) where

  inv : ⊤ → x ≡ x
  inv tt = refl

  rightInv : section (λ p → tt) inv
  rightInv tt = refl

  leftInv : retract (λ p → tt) inv
  leftInv p = h x x refl p
