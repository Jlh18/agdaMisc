module CatInContext.1CatsFuncsNatTrans.3Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Morphism
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

  Comp : {A B C : Type u} (f : A → B) (g : B → C) → A → C
  Comp f g a = g (f a)

  SETLim : SET u .ob
  SETLim = NatTrans (constDiagram (SETInitial u)) D , isSetNat

  SETLimIsCone : SETLim isConeOver D
  -- for each object j : J, give map : SETLim → D j by taking NatTrans ν ↦ νⱼ
  N-ob SETLimIsCone j = λ ν → ν .N-ob j tt*
  -- for each map ϕ : j → k, give commuting square
  N-hom SETLimIsCone {j} {k} ϕ =
      -- 𝟙 ⋆ SETLimIsCone k
      Comp (SET u .id SETLim) (SETLimIsCone .N-ob k)
    ≡⟨ SET u .⋆IdL {SETLim} {D .F-ob k} (SETLimIsCone .N-ob k) ⟩
      -- SETLimIsCone k
      SETLimIsCone .N-ob k
    ≡⟨ funExt (λ ν → cong (λ f → f tt*) (N-hom ν ϕ)) ⟩
      -- SETLimIsCone j ⋆ D ϕ
      Comp (N-ob SETLimIsCone j) (D .F-hom ϕ) ∎

  isLimSETLimNatTransOb : (X : SET u .ob) →  SET u [ X , SETLim ] → X isConeOver D
  -- for each set X, a map SET [ X , SETLim ] → SET^J [ constDiagram X , D ]
  --                    by         f          ↦  j  ↦ f ⋆ (cone map from SETLim → D j)
  N-ob (isLimSETLimNatTransOb X f) j =
    -- f ⋆ SETLimIsCone .N-ob k
    Comp f (SETLimIsCone .N-ob j)
  -- Naturality of above map as a functor J → Set{!!}
  N-hom (isLimSETLimNatTransOb X f) {j} {k} ϕ =
      -- 𝟙 ⋆ f ⋆ SETLimIsCone .N-ob k
      Comp (SET u .id X) (Comp f (SETLimIsCone .N-ob k))
    ≡⟨ SET u .⋆IdL {X} {D .F-ob k} _ ⟩
      -- f ⋆ (SETLimIsCone .N-ob k)
      Comp f (SETLimIsCone .N-ob k)
    ≡⟨
      -- suffices to show (SETLimIsCone .N-ob k) ≡ (SETLimIsCone .N-ob j ⋆ D ϕ)
      cong (Comp f) (funExt λ ν → cong (λ f → f tt*) (N-hom ν ϕ))
     ⟩
      -- f ⋆ (SETLimIsCone .N-ob j ⋆ D ϕ)
     Comp f (Comp (SETLimIsCone .N-ob j) (D .F-hom ϕ))
    ≡⟨ SET u .⋆Assoc {X} {SETLim} {D .F-ob j} {D .F-ob k} f (SETLimIsCone .N-ob j) (D .F-hom ϕ) ⟩
      -- (f ⋆ SETLimIsCone .N-ob j) ⋆ D ϕ
      Comp (Comp f (SETLimIsCone .N-ob j)) (D .F-hom ϕ) ∎

  open NatIso
  open isIso

  isLimSETLimNatTrans : NatTrans (coYo SETLim) (conesOver D)
  N-ob isLimSETLimNatTrans = isLimSETLimNatTransOb
  -- Naturality : coYo SETLim h ⋆ isLimSETLimNatTransOb Y
  --            ≡ isLimSETLimNatTransOb X ⋆ ConesOver D X
  N-hom isLimSETLimNatTrans {X} {Y} h =
      -- coYo SETLim h ⋆ isLimSETLimNatTransOb Y
      Comp (coYo SETLim .F-hom {X} {Y} h) (isLimSETLimNatTransOb Y)
    ≡⟨ funExt (λ f →
           -- (coYo SETLim h ⋆ isLimSETLimNatTransOb Y) f
           isLimSETLimNatTransOb Y (Comp h f)
         ≡⟨ makeNatTransPath $ funExt (λ j →
             sym $ SET u .⋆Assoc {Y} {X} {SETLim} {D .F-ob j} h f (SETLimIsCone .N-ob j)) ⟩
           -- (conesOver D h ⋆ isLimSETLimNatTransOb X) f
           conesOver D .F-hom {X} {Y} h (isLimSETLimNatTransOb X f) ∎

    ) ⟩
      -- isLimSETLimNatTransOb X ⋆ ConesOver D X
      Comp (isLimSETLimNatTransOb X) (conesOver D .F-hom {X} {Y} h) ∎

  isLimSETLimInv : (X : SET u .ob) → X isConeOver D → SET u [ X , SETLim ]
  N-ob (isLimSETLimInv X ν x) j tt* = ν .N-ob j x
  N-hom (isLimSETLimInv X ν x) {j} {k} ϕ =
    -- (isLimSETLimInv X ν x) k t ≡ (isLimSETLimInv X ν x) j ⋆ D ϕ t
      (isLimSETLimInv X ν x) .N-ob k
    ≡⟨ cong (Comp λ t → x) (ν .N-hom ϕ) ⟩
      Comp (isLimSETLimInv X ν x .N-ob j) (D .F-hom ϕ) ∎

  isLimSETLim : SETLim isLimitOver D
  NatIso.trans isLimSETLim = isLimSETLimNatTrans
  inv (nIso isLimSETLim X) = isLimSETLimInv X
  sec (nIso isLimSETLim X) = funExt (λ c → makeNatTransPath refl)
  ret (nIso isLimSETLim X) = funExt λ f → funExt λ x → makeNatTransPath refl

isCompleteSET : {uJO uJH : Level} → isComplete uJO uJH (SET (ℓ-max uJO uJH))
isComplete.lim isCompleteSET = SETLim
isComplete.isLim isCompleteSET = isLimSETLim
