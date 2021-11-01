module HITs.Quotient where

open import HLevel.nTypesClosedUnderSigma
open import Cubical.Core.Everything
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation.Base

data _/_
  (A : Type) (R : A → A → 1 -Type ℓ-zero)
  : Type where
  q : A → A / R
  [_] : {a b : A} → (R a b) .fst → q a ≡ q b

QuotSurj : (A : Type) (R : A → A → 1 -Type ℓ-zero)
  → isSurjection (q {A = A} {R = R})
QuotSurj A R (q x) = ∣ x , refl ∣
QuotSurj A R ([_] {a} {b} r i) =
  let
    Bundle : I → Type ℓ-zero
    Bundle = λ i → ∥ fiber (q {A = A} {R = R}) ([ r ] i) ∥
    PathOver : Path ∥ fiber (q {A} {R}) (q b) ∥
      (transport (λ i₁ → Bundle i₁) ∣ (a , (λ _ →  q a)) ∣) ∣ (b , (λ _ → q b)) ∣
    PathOver = squash _ _
    DPath : PathP Bundle ∣ (a , (λ _ →  q a)) ∣ ∣ (b , (λ _ → q b)) ∣
    DPath = Iso.inv
      (PathPIsoPath Bundle ∣ (a , (λ _ →  q a)) ∣ ∣ (b , (λ _ → q b)) ∣)
      PathOver
  in DPath i

QuotUP : (A : Type) (R : A → A → 1 -Type ℓ-zero) (B : Type) →
  isEquiv {A = A / R → B} {B = Σ (A → B) (λ f → (a b : A) → (R a b) .fst → f a ≡ f b)}
    λ f̅ → f̅ ∘ q , λ a b r → cong f̅ [ r ]
QuotUP A R B = isoToIsEquiv (iso _ Inv (λ f → refl) Retract) where
  Inv : Σ (A → B) (λ f → (a b : A) → R a b .fst → f a ≡ f b) → A / R → B
  Inv (f , hf) (q x) = f x
  Inv (f , hf) ([_] {a} {b} r i) = hf a b r i

  Lemma : (f̅ : A / R → B) (x : A / R) → Inv (f̅ ∘ q , (λ a b r → cong f̅ [ r ])) x ≡ f̅ x
  Lemma f̅ (q a) = refl
  Lemma f̅ ([_] {a} {b} r i) = refl

  Retract = λ _ → funExt (Lemma _)
