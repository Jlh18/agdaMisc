module PathSpace.PiTypes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.HITs.S1
open import Cubical.Data.Empty
open import Sn.ReflNotLoop

pathPiIso : {A B : Type} {f g : A → B} → (f ≡ g) ≅ ((a : A) → (f a ≡ g a))
pathPiIso {A} {B} {f} {g} = iso fun funExt rightInv leftInv where

  fun : f ≡ g → ((a : A) → (f a ≡ g a))
  fun p a = cong (λ h → h a) p

  rightInv : section fun funExt
  rightInv h = refl

  leftInv : retract fun funExt
  leftInv h = refl

pathPi : {A B : Type} {f g : A → B} → (f ≡ g) ≡ ((a : A) → (f a ≡ g a))
pathPi = isoToPath pathPiIso
