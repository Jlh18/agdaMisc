module HLevel.isSetZ where

open import HLevel.isSetN
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

data _⊔_ (A B : Type) : Type where

  inl : A → A ⊔ B
  inr : B → A ⊔ B

infix 30 _⊔_

ℤ≅ℕ⊔ℕ : ℤ ≅ ℕ ⊔ ℕ
ℤ≅ℕ⊔ℕ = iso fun inv rightInv leftInv where

  fun : ℤ → ℕ ⊔ ℕ
  fun (pos n) = inl n
  fun (negsuc n) = inr n

  inv : ℕ ⊔ ℕ → ℤ
  inv (inl n) = pos n
  inv (inr n) = negsuc n

  rightInv : section fun inv
  rightInv (inl n) = refl
  rightInv (inr n) = refl

  leftInv : retract fun inv
  leftInv (pos n) = refl
  leftInv (negsuc n) = refl

ℤ≡ℕ⊔ℕ : ℤ ≡ ℕ ⊔ ℕ
ℤ≡ℕ⊔ℕ = isoToPath ℤ≅ℕ⊔ℕ

private
  variable
    A B : Type

⊔NoConfusion : A ⊔ B → A ⊔ B → Type
⊔NoConfusion (inl x) (inl y) = x ≡ y -- Path A x y
⊔NoConfusion (inl x) (inr y) = ⊥
⊔NoConfusion (inr x) (inl y) = ⊥
⊔NoConfusion (inr x) (inr y) = x ≡ y -- Path B x y

isProp⊔NoConfusion : isSet A → isSet B
                     → (x y : A ⊔ B) → isProp (⊔NoConfusion x y)
isProp⊔NoConfusion hA hB (inl x) (inl y) = hA x y
isProp⊔NoConfusion hA hB (inl x) (inr y) = isProp⊥
isProp⊔NoConfusion hA hB (inr x) (inl y) = isProp⊥
isProp⊔NoConfusion hA hB (inr x) (inr y) = hB x y

⊔NoConfusionSelf : (x : A ⊔ B) → ⊔NoConfusion x x
⊔NoConfusionSelf (inl x) = refl
⊔NoConfusionSelf (inr x) = refl

Path≅⊔NoConfusion : (x y : A ⊔ B) → (x ≡ y) ≅ ⊔NoConfusion x y
Path≅⊔NoConfusion x y = iso (fun _ _) (inv _ _) (rightInv _ _) (leftInv _ _) where

  -- if you case on x and y you would have to show that inl and inr are injective
  -- J avoids this, but leads to needing J and JRefl for showing section and retract
  fun : (x y : A ⊔ B) → (x ≡ y) → ⊔NoConfusion x y
  fun x y = J (λ y' p → ⊔NoConfusion x y') (⊔NoConfusionSelf _)

  inv : (x y : A ⊔ B) → ⊔NoConfusion x y → x ≡ y
  inv (inl x) (inl y) p = cong inl p
  inv (inr x) (inr y) p = cong inr p

  rightInv : (x y : A ⊔ B) → section (fun x y) (inv x y)
  rightInv {B = B} (inl x) (inl y) p = leml x y p where

    leml : (x y : A) (p : x ≡ y) → fun {A} {B} (inl x) (inl y) (inv (inl x) (inl y) p) ≡ p
    leml {A} x y = J (λ y' p → fun {A} {B} (inl x) (inl y') (inv (inl x) (inl y') p) ≡ p)
                        (
                          fun {A} {B} (inl x) (inl x) refl
                        ≡⟨ JRefl {x = inl x} ((λ y' p → ⊔NoConfusion {A} {B} (inl x) y')) _ ⟩
                        -- uses how J computes on refl
                          refl ∎
                        )

  rightInv {A = A} (inr x) (inr y) p = lemr x y p where

    lemr : (x y : B) (p : x ≡ y) → fun {A} {B} (inr x) (inr y) (inv (inr x) (inr y) p) ≡ p
    lemr {B} x y = J (λ y' p → fun {A} {B} (inr x) (inr y') (inv (inr x) (inr y') p) ≡ p)
                     (
                       fun {A} {B} (inr x) (inr x) refl
                     ≡⟨ JRefl {x = inr x} ((λ y' p → ⊔NoConfusion {A} {B} (inr x) y')) _ ⟩
                     -- uses how J computes on refl
                       refl ∎
                     )

  leftInv : (x y : A ⊔ B) → retract (fun x y) (inv x y)
  leftInv x y = J (λ y' p → inv x y' (fun x y' p) ≡ p)
                  (
                    (inv x x (fun x x refl))
                  ≡⟨ cong (inv x x) (JRefl ((λ y' p → ⊔NoConfusion x y')) _) ⟩
                    inv x x (⊔NoConfusionSelf x)
                  ≡⟨ lem x ⟩
                    refl ∎
                  ) where

    lem : (x : A ⊔ B) → inv x x (⊔NoConfusionSelf x) ≡ refl
    lem (inl x) = refl
    lem (inr x) = refl

Path≡⊔NoConfusion : (x y : A ⊔ B) → (x ≡ y) ≡ ⊔NoConfusion x y
Path≡⊔NoConfusion x y = isoToPath (Path≅⊔NoConfusion x y)

isSet⊔ : {A B : Type} → isSet A → isSet B → isSet (A ⊔ B)
isSet⊔ hA hB x y = transport (cong isProp (sym (Path≡⊔NoConfusion x y)))
                     (isProp⊔NoConfusion hA hB x y)

isSetℤ : isSet ℤ
isSetℤ = transport (cong isSet (sym ℤ≡ℕ⊔ℕ)) (isSet⊔ isSetℕ isSetℕ)
