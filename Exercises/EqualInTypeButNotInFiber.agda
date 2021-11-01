{-# OPTIONS --cubical #-}
module Exercises.EqualInTypeButNotInFiber where

open import Cubical.Foundations.Everything
open import UnivalenceExamples.DoubleCover
open import UnivalenceExamples.Bool
open import Cubical.HITs.S1.Base
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

-- Equal in type but not as terms in the fiber

-- Mytrue≢false : true ≡ false → ⊥ -- inut \nequiv
-- Mytrue≢false



ExampleOfIt : (
      {u : Level} (A : Type u) (B : A → Type u) →
      (a : A) → (b₀ b₁ : B a) → (Path (Σ A B) (a , b₀) (a , b₁)) → (b₀ ≡ b₁)
  ) → ⊥
ExampleOfIt = λ Hf → true≢false (
      Hf S¹ Double.Cover base true false
      (Iso.fun ΣPathIsoPathΣ (loop , transport-filler Flip.IsPath true))
  )

-- {!Hf S¹ Double.Cover base true false!}
