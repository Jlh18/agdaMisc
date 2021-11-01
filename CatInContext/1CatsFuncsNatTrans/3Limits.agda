-- Plan
--
-- Limit
-- |- Cone
-- |- Representable
--    |- Yoneda embedding / Category of elements

module CatInContext.1CatsFuncsNatTrans.3Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Notation.HaskellDollar
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import CatInContext.1CatsFuncsNatTrans.2Representable

module _ {uJ vJ uC vC : Level}
         {J : Precategory uJ vJ}
         {C : Precategory uC (ℓ-max (ℓ-max uJ vJ) vC)}
         ⦃ catC : isCategory C ⦄ where

  open Precategory
  open Functor
  open NatTrans

  constDiagram : (c : C .ob) → Functor J C
  F-ob (constDiagram c) = λ _ → c
  F-hom (constDiagram c) = λ _ → C .id c
  F-id (constDiagram c) = refl
  F-seq (constDiagram c) _ _ = sym $ C .⋆IdL _

  _isConeOver_ : (c : C .ob) (D : Functor J C) → Type _
  c isConeOver D = NatTrans (constDiagram c) D

  -- use of SET is useful here for makeNatTransPath
  -- equality on record types is a pain when the path structure is non-trivial
  conesOver : (D : Functor J C) → Functor (C ^op) (SET _)
  F-ob (conesOver D) c = NatTrans (constDiagram c) D , isSetNat
  F-hom (conesOver D) f = λ ν → natTrans (λ j → f ⋆⟨ C ⟩  ν .N-ob j)
    (
      λ g →
        C .id _ ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ ν .N-ob _)
      ≡⟨ C .⋆IdL _ ⟩
        f ⋆⟨ C ⟩ ν .N-ob _
      ≡⟨ cong (λ h → f ⋆⟨ C ⟩ h) (sym (C .⋆IdL _)) ⟩
        f ⋆⟨ C ⟩ (C .id _ ⋆⟨ C ⟩ ν .N-ob _)
      ≡⟨ cong (λ h → f ⋆⟨ C ⟩ h) (ν .N-hom g) ⟩
        f ⋆⟨ C ⟩ (ν .N-ob _ ⋆⟨ C ⟩ D .F-hom g)
      ≡⟨ sym (C .⋆Assoc _ _ _) ⟩
        (f ⋆⟨ C ⟩ ν .N-ob _) ⋆⟨ C ⟩ D .F-hom g ∎
    )
  F-id (conesOver D) =
    funExt $ λ ν → makeNatTransPath $ funExt $ λ j → C .⋆IdL _
  F-seq (conesOver D) f g =
    funExt $ λ ν → makeNatTransPath $ funExt $
      λ j → (f ⋆⟨ C ^op ⟩ g) ⋆⟨ C ⟩ (ν .N-ob j)
           ≡⟨ refl ⟩
             (g ⋆⟨ C ⟩ f) ⋆⟨ C ⟩ (ν .N-ob j)
           ≡⟨ C .⋆Assoc _ _ _ ⟩
             g ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ (ν .N-ob j)) ∎


  _isLimitOver_ : (lim : C .ob) (D : Functor J C) → Type _
  lim isLimitOver D = lim coReps conesOver D
