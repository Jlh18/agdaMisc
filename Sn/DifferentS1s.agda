module Sn.DifferentS1s where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.HITs.S1
open import Cubical.Foundations.Isomorphism renaming ( Iso to _≅_ )
open import Cubical.Foundations.GroupoidLaws

data S1 : Type where
  base0 base1 : S1
  path0 : base0 ≡ base1
  path1 : base1 ≡ base0


thing = compPath-filler

S¹≅S1 : S¹ ≅ S1
S¹≅S1 = iso fun inv sec ret where
  fun : S¹ → S1
  fun base = base0
  fun (loop i) = (path0 ∙ path1) i

  inv : S1 → S¹
  inv base0 = base
  inv base1 = base
  inv (path0 i) = loop i
  inv (path1 i) = base

  sec : section fun inv
  sec base0 = refl
  sec base1 = sym path1
  sec (path0 i) j = compPath-filler path0 path1 (~ j) i
  sec (path1 i) = sym (λ j → path1 (j ∨ i))

  ret : retract fun inv
  ret base = refl
  ret (loop i) j = sym (rUnit loop) j i

S¹≡S1 : S¹ ≡ S1
S¹≡S1 = isoToPath S¹≅S1
