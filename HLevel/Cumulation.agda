module HLevel.Cumulation where

open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Bool

private
  variable u : Level

MyHLevel = ℕ

isHLevel : ℕ → Type u → Type u
isHLevel zero A = isContr A
isHLevel (suc n) A = (x y : A) → isHLevel n (x ≡ y)

_-Type_ : ℕ → (u : Level) → Type (ℓ-suc u)
n -Type u = Σ (Type u) (isHLevel n)


isHLevelSuc : {A : Type} {n : ℕ} → isHLevel n A → isHLevel (suc n) A
isHLevelSuc {A} {zero} (c , cto) x y =
  (q , square) where
    α = cto x
    β = cto y
    q = (sym α) ∙ β
    square : (p : x ≡ y) → q ≡ p
    square p i j = hcomp (λ k → λ {
      (i = i0) → cto (q j) k ;
      (i = i1) → cto (p j) k ;
      (j = i0) → α k ;
      (j = i1) → β k }) c
isHLevelSuc {A} {suc n} h x y = isHLevelSuc (h x y)

isHLevelSucJ : {A : Type} {n : ℕ} → isHLevel n A → isHLevel (suc n) A
isHLevelSucJ {A} {zero} (c , cto) x y = (q , square) where
    α = cto x
    β = cto y
    q = (sym α) ∙ β
    square : (p : x ≡ y) → (sym (cto x)) ∙ (cto y) ≡ p
    square = J (λ y p → (sym (cto x)) ∙ (cto y) ≡ p) (lCancel (cto x))
isHLevelSucJ {A} {suc n} h x y = isHLevelSuc (h x y)
