module Sn.ReflNotLoop where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.HITs.S1
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

Flip : Bool → Bool
Flip false = true
Flip true = false

-- notice we used `refl` instead of `λ i → false`,
-- more on `refl` in Quest1
flipIso : Bool ≅ Bool
flipIso = iso Flip Flip rightInv leftInv where
  rightInv : section Flip Flip
  rightInv false = refl
  rightInv true = refl

  leftInv : retract Flip Flip
  leftInv false = refl
  leftInv true = refl

flipPath : Bool ≡ Bool
flipPath = isoToPath flipIso

doubleCover : S¹ → Type
doubleCover base = Bool
doubleCover (loop i) = flipPath i

substTrue : (p : base ≡ base) → doubleCover base
substTrue p = subst doubleCover p true

refl≢loop : refl ≡ loop → ⊥
refl≢loop p = true≢false (cong substTrue p)
