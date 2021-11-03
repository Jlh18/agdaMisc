module CatInContext.1CatsFuncsNatTrans.3Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Categories.Morphism
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Limits.Terminal
open import Cubical.Data.Unit

open Precategory
open Functor
open NatTrans
open NatIso
open isIso

private -- Haskell notation (could this be put somewhere in the library?)

   application : {u v : Level} {A : Type u} {B : A → Type v} (f : (a : A) → B a) (a : A) → B a
   application f a = f a

   infixr 3 application
   syntax application f a = f $ a

module _ (u : Level) where -- Final object in SET

  SETFinal : SET u .ob
  SETFinal = Unit* , isProp→isSet isPropUnit*

  isFinalSETFinal : isFinal (SET u) SETFinal
  fst (isFinalSETFinal X) x = tt*
  snd (isFinalSETFinal X) f = funExt (λ x → refl)

module _ {uC uSET : Level} {C : Precategory uC uSET} ⦃ catC : isCategory C ⦄ where

  -- Yoneda embedding, universe level for objects more general than in the library
  yo : (c : (C ^op) .ob) → Functor (C ^op) (SET uSET)
  F-ob (yo c) d = C [ d , c ] , catC .isSetHom
  F-hom (yo c) f = λ g → (f ⋆⟨ C ⟩ g)
  F-id (yo c) = funExt (λ f → C .⋆IdL f)
  F-seq (yo c) f g = funExt (λ h → C .⋆Assoc g f h)

  -- A contravariant functor is representable by c ∈ C^op
  -- when (yo c) is naturally isomorphic to it
  _reps_ : (c : (C ^op) .ob) (F : Functor (C ^op) (SET uSET)) → Type _
  c reps F = NatIso (yo c) F

module _ {uJO uJH uCO uCH : Level}
         {J : Precategory uJO uJH}
         {C : Precategory uCO uCH} where

  -- The summit of a cone is expressed as a constant diagram
  constDiagram : (c : C .ob) → Functor J C
  F-ob (constDiagram c) = λ _ → c
  F-hom (constDiagram c) = λ _ → C .id c
  F-id (constDiagram c) = refl
  F-seq (constDiagram c) _ _ = sym $ C .⋆IdL _

  -- Cones over diagram D with summit c are natural transformations from the summit to D
  Cone[_,_] : (c : C .ob) (D : Functor J C) → Type _
  Cone[ c , D ] = NatTrans (constDiagram c) D

  -- Taking cones over diagram D extends to a functor into SET
  CONE : ⦃ catC : isCategory C ⦄ (D : Functor J C) → Functor (C ^op) (SET _)
  -- Send c ∈ C to set of cones over D with summit c
  F-ob (CONE D) c = Cone[ c , D ] , isSetNat
  F-hom (CONE D) f = λ ν → natTrans (λ j → f ⋆⟨ C ⟩  ν .N-ob j)
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
  F-id (CONE D) =
    funExt $ λ ν → makeNatTransPath $ funExt λ j → C .⋆IdL _
  F-seq (CONE D) f g =
    funExt $ λ ν → makeNatTransPath $ funExt
      λ j → (f ⋆⟨ C ^op ⟩ g) ⋆⟨ C ⟩ (ν .N-ob j)
           ≡⟨ refl ⟩
             (g ⋆⟨ C ⟩ f) ⋆⟨ C ⟩ (ν .N-ob j)
           ≡⟨ C .⋆Assoc _ _ _ ⟩
             g ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ (ν .N-ob j)) ∎

-- lim is the limit of diagram D when it represents the functor (CONE D)
_isLimitOver_ : {uJO uJH uCO : Level} {J : Precategory uJO uJH}
  {C : Precategory uCO (ℓ-max uJO uJH)} -- J is smaller than hom sets of C
  ⦃ catC : isCategory C ⦄
  (lim : C .ob) (D : Functor J C) → Type (ℓ-max uCO (ℓ-suc (ℓ-max uJO uJH)))
lim isLimitOver D = lim reps CONE D

record isComplete (uJO uJH : Level) {uCO : Level}
  (C : Precategory uCO (ℓ-max uJO uJH)) -- J is smaller than hom sets of C
  ⦃ catC : isCategory C ⦄ : Type (ℓ-max uCO (ℓ-suc (ℓ-max uJO uJH))) where
  field
    -- a limit constructed for any small diagram D
    lim : (J : Precategory uJO uJH) (D : Functor J C) → C .ob
    -- a proof that it is the limit
    isLim : (J : Precategory uJO uJH) (D : Functor J C) → (lim J D) isLimitOver D


module _ {uJO uJH : Level}
         (J : Precategory uJO uJH)
        (D : Functor J (SET (ℓ-max uJO uJH))) where

  private
    u = ℓ-max uJO uJH

    Comp : {A B C : Type u} (f : A → B) (g : B → C) → A → C
    Comp f g a = g (f a)

  -- Construction of object which is limit of any diagram D
  -- Idea : lim ≅ SET[ SETFinal , lim ] ≅ Cone[ SETFinal , D ]
  SETLim : SET u .ob
  SETLim = Cone[ SETFinal u , D ] , isSetNat

  -- Promoting SETLim to a cone
  SETLimCone : Cone[ SETLim , D ]
  -- for each object j : J, give map : SETLim → D j by taking NatTrans ν ↦ νⱼ
  N-ob SETLimCone j = λ ν → ν .N-ob j tt*
  -- for each map ϕ : j → k, give commuting square
  N-hom SETLimCone {j} {k} ϕ =
      -- 𝟙 ⋆ SETLimCone k
      Comp (SET u .id SETLim) (SETLimCone .N-ob k)
    ≡⟨ SET u .⋆IdL {SETLim} {D .F-ob k} (SETLimCone .N-ob k) ⟩
      -- SETLimCone k
      SETLimCone .N-ob k
    ≡⟨ funExt (λ ν → cong (λ f → f tt*) (N-hom ν ϕ)) ⟩
      -- SETLimCone j ⋆ D ϕ
      Comp (N-ob SETLimCone j) (D .F-hom ϕ) ∎

  -- Maps forwards and backwards on objects - forwards
  isLimSETLimFun : (X : SET u .ob) →  SET u [ X , SETLim ] → Cone[ X , D ]
  -- for each set X, a map SET [ X , SETLim ] → SET^J [ constDiagram X , D ]
  --                    by         f          ↦  j  ↦ f ⋆ (CONE map from SETLim → D j)
  N-ob (isLimSETLimFun X f) j =
    -- f ⋆ SETLimCone .N-ob k
    Comp f (SETLimCone .N-ob j)
  -- Naturality of above map as a functor J → Set{!!}
  N-hom (isLimSETLimFun X f) {j} {k} ϕ =
      -- 𝟙 ⋆ f ⋆ SETLimCone .N-ob k
      Comp (SET u .id X) (Comp f (SETLimCone .N-ob k))
    ≡⟨ SET u .⋆IdL {X} {D .F-ob k} _ ⟩
      -- f ⋆ (SETLimCone .N-ob k)
      Comp f (SETLimCone .N-ob k)
    ≡⟨
      -- suffices to show (SETLimCone .N-ob k) ≡ (SETLimCone .N-ob j ⋆ D ϕ)
      cong (Comp f) (funExt λ ν → cong (λ f → f tt*) (N-hom ν ϕ))
     ⟩
      -- f ⋆ (SETLimCone .N-ob j ⋆ D ϕ)
     Comp f (Comp (SETLimCone .N-ob j) (D .F-hom ϕ))
    ≡⟨ SET u .⋆Assoc {X} {SETLim} {D .F-ob j} {D .F-ob k} f (SETLimCone .N-ob j) (D .F-hom ϕ) ⟩
      -- (f ⋆ SETLimCone .N-ob j) ⋆ D ϕ
      Comp (Comp f (SETLimCone .N-ob j)) (D .F-hom ϕ) ∎

  -- Maps forwards and backwards on objects - backwards
  isLimSETLimInv : (X : SET u .ob) → Cone[ X , D ] → SET u [ X , SETLim ]
  N-ob (isLimSETLimInv X ν x) j tt* = ν .N-ob j x
  N-hom (isLimSETLimInv X ν x) {j} {k} ϕ =
    -- (isLimSETLimInv X ν x) k ≡ (isLimSETLimInv X ν x) j ⋆ D ϕ
      (isLimSETLimInv X ν x) .N-ob k
    -- follows from precomposition of naturality diagram for ν with x : Unit* → X
    ≡⟨ cong (Comp λ t → x) (ν .N-hom ϕ) ⟩
      Comp (isLimSETLimInv X ν x .N-ob j) (D .F-hom ϕ) ∎

  -- Promotes isLimSETLimFun into a natural transformation
  isLimSETLimNatTrans : NatTrans (yo SETLim) (CONE D)
  N-ob isLimSETLimNatTrans = isLimSETLimFun
  -- Naturality : coYo SETLim h ⋆ isLimSETLimFun Y ≡ isLimSETLimFun X ⋆ ConesOver D X
  N-hom isLimSETLimNatTrans {X} {Y} h =
      -- coYo SETLim h ⋆ isLimSETLimFun Y
      Comp (yo SETLim .F-hom {X} {Y} h) (isLimSETLimFun Y)
    ≡⟨ funExt (λ f →
           -- (coYo SETLim h ⋆ isLimSETLimFun Y) f
           isLimSETLimFun Y (Comp h f)
         ≡⟨ makeNatTransPath $ funExt (λ j →
             sym $ SET u .⋆Assoc {Y} {X} {SETLim} {D .F-ob j} h f (SETLimCone .N-ob j)) ⟩
           -- (CONE D h ⋆ isLimSETLimFun X) f
           CONE D .F-hom {X} {Y} h (isLimSETLimFun X f) ∎
    ) ⟩
      -- isLimSETLimFun X ⋆ ConesOver D X
      Comp (isLimSETLimFun X) (CONE D .F-hom {X} {Y} h) ∎

  -- Promotes SETLim to an isomorphism
  isLimSETLim : SETLim isLimitOver D
  NatIso.trans isLimSETLim = isLimSETLimNatTrans
  inv (nIso isLimSETLim X) = isLimSETLimInv X
  sec (nIso isLimSETLim X) = funExt (λ c → makeNatTransPath refl)
  ret (nIso isLimSETLim X) = funExt λ f → funExt λ x → makeNatTransPath refl

isCompleteSET : {uJO uJH : Level} → isComplete uJO uJH (SET (ℓ-max uJO uJH))
isComplete.lim isCompleteSET = SETLim
isComplete.isLim isCompleteSET = isLimSETLim
