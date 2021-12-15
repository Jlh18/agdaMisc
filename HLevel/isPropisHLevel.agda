module HLevel.isPropisHLevel where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws

private
  variable
    u : Level

isHLevel : ℕ → Type u → Type u
isHLevel zero A = isContr A
isHLevel (suc n) A = (x y : A) → isHLevel n (x ≡ y)

thing = isPropIsContr

isPropisContr : {A : Type u} → isProp (isContr A)
isPropisContr (a0 , p0) (a1 , p1) i = (p0 a1 i) , λ y j →
               hcomp (λ k → λ { (i = i0) → p0 (p0 y j) k
                               ; (i = i1) → p0 (p1 y j) k
                               ; (j = i0) → p0 (p0 a1 i) k
                               ; (j = i1) → p0 y k})
               a0

isPropisProp : {A : Type u} → isProp (isProp A)
isPropisProp h0 h1 = funExt (λ x → funExt (λ y → isProp→isSet h0 x y (h0 x y) (h1 x y)))

