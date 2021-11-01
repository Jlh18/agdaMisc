{-# OPTIONS --cubical #-}
module HLevel.S1 where

open import Cubical.Foundations.Everything
open import Cubical.HITs.S1.Base
open import Cubical.Relation.Nullary
open import UnivalenceExamples.DoubleCover
open import Cubical.Data.Bool

private
  variable
    u v : Level

S¹NotHLevel2 : ¬ isOfHLevel 2 S¹
S¹NotHLevel2 h⊥ =
  let BaseToLoop = h⊥ base base refl loop
  in true≢false
    (cong (λ p → transport (λ i → Double.Cover (p i)) true) BaseToLoop)




-- SufficesBase : isProp (base ≡ base) → isOfHLevel 3 S¹


S¹HLevel3 : isOfHLevel 3 S¹
S¹HLevel3 x y = {!!}

Prop→Set : (A : Type u) → isProp A → isSet A
Prop→Set A H = λ x y p q i j → {!!}
