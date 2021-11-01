{-# OPTIONS --cubical #-}
module Basic.TypeConstructions where

open import Cubical.Foundations.Everything 
open import Agda.Primitive

private
  variable
    u v : Level

PathSigmaIso : {A : Type u} (B : A → Type v) (σ0 σ1 : Σ A B) →
   Iso (σ0 ≡ σ1) (Σ (fst σ0 ≡ fst σ1) (λ p → PathP (λ i → B (p i)) (snd σ0) (snd σ1)))
PathSigmaIso B σ0 σ1 = iso Map Inv (λ b → refl) (λ a → refl)
  where
  Map : σ0 ≡ σ1 → Σ (fst σ0 ≡ fst σ1) (λ p → PathP (λ i → B (p i)) (snd σ0) (snd σ1))
  Map p = cong fst p , λ i → snd (p i)

  Inv : Σ (fst σ0 ≡ fst σ1) (λ p → PathP (λ i → B (p i)) (snd σ0) (snd σ1)) → σ0 ≡ σ1
  Inv (σ , over) = λ i → (σ i) , over i

PathSigma : {A : Type u} (B : A → Type v) (σ0 σ1 : Σ A B) →
  (σ0 ≡ σ1) ≃ Σ (fst σ0 ≡ fst σ1) (λ p → PathP (λ i → B (p i)) (snd σ0) (snd σ1))
PathSigma B σ0 σ1 = isoToEquiv (PathSigmaIso B σ0 σ1)
