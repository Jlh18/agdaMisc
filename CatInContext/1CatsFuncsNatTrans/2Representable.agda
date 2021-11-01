module CatInContext.1CatsFuncsNatTrans.2Representable where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Notation.HaskellDollar


{- into TYPE instead of SET
private
  variable
    uC vC : Level

module _ {C : Precategory uC vC} where

  open Precategory
  open Functor

  yoEmb : (c : C .ob) → Functor C (TYPE vC)
  F-ob (yoEmb c) d = C [ c , d ]
  F-hom (yoEmb c) f = λ g → (g ⋆⟨ C ⟩ f)
  F-id (yoEmb c) = funExt λ f →  C .⋆IdR f
  F-seq (yoEmb c) f g = funExt λ h → sym $ C .⋆Assoc h f g

  _represents_ : (c : C .ob) (F : Functor C (TYPE vC)) → Type _
  c represents F = NatIso (yoEmb c) F
-}

private
  variable
    uC uSET : Level

module _ {C : Precategory uC uSET} ⦃ catC : isCategory C ⦄ where

  open Precategory
  open Functor

  yo : (c : C .ob) → Functor C (SET uSET)
  F-ob (yo c) d = C [ c , d ] , catC .isSetHom
  F-hom (yo c) f = λ g → (g ⋆⟨ C ⟩ f)
  F-id (yo c) = funExt λ f →  C .⋆IdR f
  F-seq (yo c) f g = funExt λ h → sym $ C .⋆Assoc h f g

  _reps_ : (c : C .ob) (F : Functor C (SET uSET)) → Type _
  c reps F = NatIso (yo c) F

  coYo : (c : (C ^op) .ob) → Functor (C ^op) (SET uSET)
  F-ob (coYo c) d = C [ d , c ] , catC .isSetHom
  F-hom (coYo c) f = λ g → (f ⋆⟨ C ⟩ g)
  F-id (coYo c) = funExt (λ f → C .⋆IdL f)
  F-seq (coYo c) f g = funExt (λ h → sym $ sym (C .⋆Assoc g f h))

  _coReps_ : (c : (C ^op) .ob) (F : Functor (C ^op) (SET uSET)) → Type _
  c coReps F = NatIso (coYo c) F
