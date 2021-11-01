module HLevel.isSetN where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

-- explain this using equality?? since equality on naturals is actually a proposition
ℕoConfusion : ℕ → ℕ → Type
ℕoConfusion zero zero = ⊤
ℕoConfusion zero (suc m) = ⊥
ℕoConfusion (suc n) zero = ⊥
ℕoConfusion (suc n) (suc m) = ℕoConfusion n m

isProp⊤ : isProp ⊤
isProp⊤ tt tt = refl

isProp⊥ : isProp ⊥
isProp⊥ ()

isPropℕoConfusion : (n m : ℕ) → isProp (ℕoConfusion n m)
isPropℕoConfusion zero zero = isProp⊤
isPropℕoConfusion zero (suc m) = isProp⊥
isPropℕoConfusion (suc n) zero = isProp⊥
isPropℕoConfusion (suc n) (suc m) = isPropℕoConfusion n m

zero≢suc : (n : ℕ) → zero ≡ suc n → ⊥
zero≢suc n p = subst Bundle p tt where

  Bundle : ℕ → Type
  Bundle zero = ⊤
  Bundle (suc n) = ⊥

sucInj : {n m : ℕ} → suc n ≡ suc m → n ≡ m
sucInj = cong pred where

  pred : ℕ → ℕ
  pred zero = zero
  pred (suc n) = n

path≅ℕoConfusion : {n m : ℕ} → (n ≡ m) ≅ ℕoConfusion n m
path≅ℕoConfusion {n} {m} = iso (fun _ _) (inv _ _) (rightInv n m) (leftInv n m) where

  -- not obvious imo (I tried J first)
  fun : (n m : ℕ) → (n ≡ m) → ℕoConfusion n m
  fun zero zero = λ x → tt
  fun zero (suc m) = zero≢suc m
  fun (suc n) zero = λ p → zero≢suc n (sym p)
  fun (suc n) (suc m) p = fun n m (sucInj p)

  inv : (n m : ℕ) → ℕoConfusion n m → (n ≡ m)
  inv zero zero tt = refl
  inv zero (suc m) ()
  inv (suc n) zero ()
  inv (suc n) (suc m) h = cong suc (inv _ _ h)

  rightInv : (n m : ℕ) → section (fun n m) (inv n m)
  rightInv zero zero tt = refl
  rightInv (suc n) (suc m) h = rightInv n m h

  -- not obvious
  leftInv : (n m : ℕ) → retract (fun n m) (inv n m)
  leftInv n m = J (λ y p → inv n y (fun n y p) ≡ p) (leftInvSelf n) where

    leftInvSelf : (n : ℕ) → inv n n (fun n n refl) ≡ refl
    leftInvSelf zero = refl
    leftInvSelf (suc n) =
        ((λ i → suc (inv n n (fun n n (sucInj refl)) i)))
      ≡⟨ refl ⟩
        ((λ i → suc (inv n n (fun n n refl) i)))
      ≡⟨ cong (λ p → (λ i → suc (p i))) (leftInvSelf n) ⟩
        ((λ i → suc (refl {x = n} i)))
      ≡⟨ refl ⟩
        refl ∎
      --  {!(λ i → suc (refl) i))!}

    -- funRefl≡refl : (n : ℕ) → fun n n refl ≡ tt
    -- funRefl≡refl n = ?

path≡ℕoConfusion : (n m : ℕ) → (n ≡ m) ≡ ℕoConfusion n m
path≡ℕoConfusion n m = isoToPath path≅ℕoConfusion

isSetℕ : isSet ℕ
isSetℕ n m = transport (cong isProp (sym (path≡ℕoConfusion n m)))
               (isPropℕoConfusion n m)
