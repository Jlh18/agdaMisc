{-# OPTIONS --cubical #-}
module UnivalenceExamples.CoProd where

open import Cubical.Foundations.Id
  hiding ( _≡_ ; _≡⟨_⟩_ ; _∎ )
  renaming ( _≃_           to EquivId
           ; EquivContr    to EquivContrId
           ; J             to JId
           ; ap            to apId
           ; equivFun      to equivFunId
           ; equivCtr      to equivCtrId
           ; fiber         to fiberId
           ; funExt        to funExtId
           ; isContr       to isContrId
           ; isProp        to isPropId
           ; isSet         to isSetId
           ; isEquiv       to isEquivId
           ; equivIsEquiv  to equivIsEquivId
           ; refl          to reflId
           ; ∥_∥           to propTruncId
           ; ∣_∣           to incId
           ; isPropIsContr to isPropIsContrId
           ; isPropIsEquiv to isPropIsEquivId
           ; transport     to transportId
           )
open import Cubical.Foundations.Everything public
open import Cubical.Data.Bool

private
   variable
     u : Level

CoPair : (A B : Type u) → (C : Type u) → Type (ℓ-suc u) → Type (ℓ-suc u)
CoPair A B C property = (A → C) → (B → C) → property

CoProdStruc : (A B : Type u) → Type u → Type (ℓ-suc u)
CoProdStruc {u} A B C = CoPair A B C (
  (D : Type u) → CoPair A B D ({!Σ (C → D) ((f : C → D) → ?)!}))



-- (A → C)
--   → (B → C)
--   → (D : Type u)
--     → (A → D) → (B → D) → {!Σ (C → D) ((f : C → D) → (g : C → D))!}
-- -- Bundle ≃ S¹ as covers of S¹
-- two things equal in space not equal in fiber
-- two ℕs
