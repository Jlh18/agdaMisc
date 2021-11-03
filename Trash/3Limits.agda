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
open import Cubical.Data.Unit

open Precategory
open Functor
open NatTrans

module _ {uJO uJH uCO uCH : Level}
         {J : Precategory uJO uJH}
         {C : Precategory uCO uCH} where

  constDiagram : (c : C .ob) → Functor J C
  F-ob (constDiagram c) = λ _ → c
  F-hom (constDiagram c) = λ _ → C .id c
  F-id (constDiagram c) = refl
  F-seq (constDiagram c) _ _ = sym $ C .⋆IdL _

  _isConeOver_ : (c : C .ob) (D : Functor J C) → Type _
  c isConeOver D = NatTrans (constDiagram c) D

  -- use of SET is useful here for makeNatTransPath
  -- equality on record types is a pain when the path structure is non-trivial
  conesOver : ⦃ catC : isCategory C ⦄ (D : Functor J C) → Functor (C ^op) (SET _)
  F-ob (conesOver D) c = c isConeOver D , isSetNat
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

-- PROBLEM : the universe levels are not as general

module _ {uJO uJH uCO : Level} where

  private
    uCH = ℓ-max uJO uJH -- condition of C being small with respect to J


  _isLimitOver_ :
         {J : Precategory uJO uJH} {C : Precategory uCO uCH}
         ⦃ catC : isCategory C ⦄
         (lim : C .ob) (D : Functor J C) → Type (ℓ-max uCO (ℓ-suc uCH))
  lim isLimitOver D = lim coReps conesOver D

module _ (uJO uJH : Level) {uCO : Level} where

  private
    uCH = ℓ-max uJO uJH -- condition of C being small with respect to J

  record isComplete (C : Precategory uCO (ℓ-max uJO uJH))
    ⦃ catC : isCategory C ⦄
    : Type (ℓ-max uCO (ℓ-suc uCH)) where
    field
      lim : (J : Precategory uJO uJH) (D : Functor J C) → C .ob
      isLim : (J : Precategory uJO uJH) (D : Functor J C) → (lim J D) isLimitOver D

module _ where

  isSetUnit* : (u : Level) → isSet (Unit* {ℓ = u})
  isSetUnit* u = isProp→isSet isPropUnit*

  SETInitial : (u : Level) → (SET u) .ob
  SETInitial u = Unit* , isSetUnit* u

module _ {uJO uJH : Level}
         (J : Precategory uJO uJH)
        (D : Functor J (SET (ℓ-max uJO uJH))) where

  private
    u = ℓ-max uJO uJH -- condition of SET being small with respect to J

    -- variable
      -- D : Functor J (SET u)

  SETLim : SET u .ob
  SETLim = NatTrans (constDiagram (SETInitial u)) D , isSetNat

  -- ISSUE : Why can't agda figure out that things are sets?
  SETLimIsCone : SETLim isConeOver D
  -- for each object j : J, give map : SETLim → D j by taking NatTrans ν ↦ νⱼ
  N-ob SETLimIsCone j = λ ν → ν .N-ob j tt*
  -- for each map ϕ : j → k, give commuting square
  N-hom SETLimIsCone {j} {k} ϕ =
      -- 𝟙 ⋆ SETLimIsCone k
      seq' (SET u) {SETLim} {SETLim} {D .F-ob k} (SET u .id SETLim) (SETLimIsCone .N-ob k)
    ≡⟨ SET u .⋆IdL {SETLim} {D .F-ob k} (SETLimIsCone .N-ob k) ⟩
      -- SETLimIsCone k
      SETLimIsCone .N-ob k
    ≡⟨ funExt (λ ν → cong (λ f → f tt*) (N-hom ν ϕ)) ⟩
      -- SETLimIsCone j ⋆ D ϕ
      seq' (SET u) {SETLim} {D .F-ob j} {D .F-ob k} (N-ob SETLimIsCone j) (D .F-hom ϕ) ∎

  SETLimIsLimNatTransOb : N-ob-Type (coYo SETLim) (conesOver D)
  -- for each set X, a map SET [ X , SETLim ] → SET^J [ constDiagram X , D ]
  --                    by         f          ↦  j  ↦ f ⋆ (cone map from SETLim → D j)
  N-ob (SETLimIsLimNatTransOb X f) j =
    -- f ⋆ SETLimIsCone .N-ob k
    seq' (SET u) {X} {SETLim} {D .F-ob j} f (SETLimIsCone .N-ob j)
  -- Naturality of above map as a functor J → Set{!!}
  N-hom (SETLimIsLimNatTransOb X f) {j} {k} ϕ =
    -- 𝟙 ⋆ f ⋆ SETLimIsCone .N-ob k
      seq' (SET u) {X} {X} {D .F-ob k}
        (SET u .id X) (seq' (SET u) {X} {SETLim} {D .F-ob k} f (SETLimIsCone .N-ob k))
    ≡⟨ SET u .⋆IdL {X} {D .F-ob k} _ ⟩
      -- f ⋆ (SETLimIsCone .N-ob k)
      seq' (SET u) {X} {SETLim} {D .F-ob k} f (SETLimIsCone .N-ob k)
    ≡⟨
      -- suffices to show (SETLimIsCone .N-ob k) ≡ (SETLimIsCone .N-ob j ⋆ D ϕ)
      cong {x = (SETLimIsCone .N-ob k)} {y = (seq' (SET u) {SETLim} {D .F-ob j} {D .F-ob k}
        (SETLimIsCone .N-ob j) (D .F-hom ϕ))} (λ g → seq' (SET u) {X} {SETLim} {D .F-ob k} f g)
        (funExt λ ν → cong (λ f → f tt*) (N-hom ν ϕ))
     ⟩
      -- f ⋆ (SETLimIsCone .N-ob j ⋆ D ϕ)
      seq' (SET u) {X} {SETLim} {D .F-ob k} f
        (seq' (SET u) {SETLim} {D .F-ob j} {D .F-ob k} (SETLimIsCone .N-ob j) (D .F-hom ϕ))
    ≡⟨ SET u .⋆Assoc {X} {SETLim} {D .F-ob j} {D .F-ob k} f (SETLimIsCone .N-ob j) (D .F-hom ϕ) ⟩
      -- (f ⋆ SETLimIsCone .N-ob j) ⋆ D ϕ
      seq' (SET u) {X} {D .F-ob j} {D .F-ob k}
        (seq' (SET u) {X} {SETLim} {D .F-ob j} f (SETLimIsCone .N-ob j)) (D .F-hom ϕ) ∎

  SETLimIsLimNatTrans : NatTrans (coYo SETLim) (conesOver D)
  N-ob SETLimIsLimNatTrans = {!!}
  N-hom SETLimIsLimNatTrans = {!!}

  SETLimIsLim : SETLim isLimitOver D
  -- for each set X, a map SET [ X , SETLim ] → SET^J [ constDiagram X , D ]
  --                    by         f          ↦  j  ↦ f ⋆ (cone map from SETLim → D j)
  N-ob (N-ob (NatIso.trans SETLimIsLim) X f) j =
    -- f ⋆ SETLimIsCone .N-ob k
    seq' (SET u) {X} {SETLim} {D .F-ob j} f (SETLimIsCone .N-ob j)
  -- Naturality of above map as a functor J → Set
  N-hom (N-ob (NatIso.trans SETLimIsLim) X f) {j} {k} ϕ =
      -- 𝟙 ⋆ f ⋆ SETLimIsCone .N-ob k
      seq' (SET u) {X} {X} {D .F-ob k}
        (SET u .id X) (seq' (SET u) {X} {SETLim} {D .F-ob k} f (SETLimIsCone .N-ob k))
    ≡⟨ SET u .⋆IdL {X} {D .F-ob k} _ ⟩
      -- f ⋆ (SETLimIsCone .N-ob k)
      seq' (SET u) {X} {SETLim} {D .F-ob k} f (SETLimIsCone .N-ob k)
    ≡⟨
      -- suffices to show (SETLimIsCone .N-ob k) ≡ (SETLimIsCone .N-ob j ⋆ D ϕ)
      cong {x = (SETLimIsCone .N-ob k)} {y = (seq' (SET u) {SETLim} {D .F-ob j} {D .F-ob k}
        (SETLimIsCone .N-ob j) (D .F-hom ϕ))} (λ g → seq' (SET u) {X} {SETLim} {D .F-ob k} f g)
        (funExt λ ν → cong (λ f → f tt*) (N-hom ν ϕ))
     ⟩
      -- f ⋆ (SETLimIsCone .N-ob j ⋆ D ϕ)
      seq' (SET u) {X} {SETLim} {D .F-ob k} f
        (seq' (SET u) {SETLim} {D .F-ob j} {D .F-ob k} (SETLimIsCone .N-ob j) (D .F-hom ϕ))
    ≡⟨ SET u .⋆Assoc {X} {SETLim} {D .F-ob j} {D .F-ob k} f (SETLimIsCone .N-ob j) (D .F-hom ϕ) ⟩
      -- (f ⋆ SETLimIsCone .N-ob j) ⋆ D ϕ
      seq' (SET u) {X} {D .F-ob j} {D .F-ob k}
        (seq' (SET u) {X} {SETLim} {D .F-ob j} f (SETLimIsCone .N-ob j)) (D .F-hom ϕ) ∎
  -- Above map is a natural transformation.
  -- For each h : X → Y,
  N-hom (NatIso.trans SETLimIsLim) {X} {Y} h = {!!}
  NatIso.nIso SETLimIsLim = {!!}

  SETLimIsLim' : SETLim isLimitOver D
  -- for each set X, a map SET [ X , SETLim ] → SET^J [ constDiagram X , D ]
  --                    by         f          ↦  j  ↦ f ⋆ (cone map from SETLim → D j)
  NatIso.trans SETLimIsLim' = {!!}
  NatIso.nIso SETLimIsLim' = {!!}

  {-
  -- SET [ - , setLim D ] ≅ SET^J [ constDiagram (-) , D ] as functors SET^op → SET
  N-ob (N-ob (NatIso.trans (isLimSetLim J D)) (X , _) f) j = {!f!}
  N-hom (N-ob (NatIso.trans (isLimSetLim J D)) (X , _) f) = {!!}

  N-hom (NatIso.trans (isLimSetLim J D)) = {!!}
  NatIso.nIso (isLimSetLim J D) = {!!}

  SETIsComplete : isComplete uJO uJH (SET u)
  isComplete.lim SETIsComplete J D = setLim J D , isSetNat
  isComplete.isLim SETIsComplete J D = {!!}
  -}

  -- isComplete : (C : Precategory uCO (ℓ-max uJO uJH)) ⦃ catC : isCategory C ⦄ → Type _
  -- isComplete C = (J : Precategory uCO (ℓ-max uJO uJH)) (D : Functor J C) → {!!}

-- module _ {uJO uJH uCO uCH : Level}
--          {J : Precategory uJO uJH}
--          {C : Precategory uCO uCH}
--          ⦃ catC : isCategory C ⦄ where

--   open Precategory
--   open Functor
--   open NatTrans

--   constDiagram : (c : C .ob) → Functor J C
--   F-ob (constDiagram c) = λ _ → c
--   F-hom (constDiagram c) = λ _ → C .id c
--   F-id (constDiagram c) = refl
--   F-seq (constDiagram c) _ _ = sym $ C .⋆IdL _

--   _isConeOver_ : (c : C .ob) (D : Functor J C) → Type _
--   c isConeOver D = NatTrans (constDiagram c) D

--   thing = _coReps_
