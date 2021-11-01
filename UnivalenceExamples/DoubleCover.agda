{-# OPTIONS --cubical #-}

module UnivalenceExamples.DoubleCover where
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
open import Basic.Everything
open import Cubical.Data.Bool
open import UnivalenceExamples.Bool
open import Cubical.HITs.S1.Base
open import Cubical.Data.Sum
private
  variable
    u : Level

module FiberOfBundle where
  private
    variable
      A : Type u
      F : A → Type u
  Map : {a : A} → F a → fiber (fst {B = F}) a
  Map {a = a} x = (a , x) , refl

  Inv : {a : A} → fiber (fst {B = F}) a → F a
  Inv {F = F} {a = a} (b , p) = subst F p (snd b)

  MapInv : {a : A} (x : fiber (fst {B = F}) a) → Map (Inv x) ≡ x
  MapInv {F = F} (b , p) = symPath (λ i → ((p i) , subst-filler F p (snd b) i) , PathToEnd p i)

  InvMap : {a : A} (x : F a) → Inv (Map {F = F} {a = a} x) ≡ x
  InvMap {F = F} x = substRefl {B = F} x

  Eq : (F : A → Type u) (a : A) → F a ≡ fiber (λ (x : Σ {u} A F) → fst x) a
  Eq F a = isoToPath (iso Map Inv MapInv (InvMap {F = F}))


TrivialCover : S¹ → Type
TrivialCover p = Bool

module TrivialBundle where
  Map : S¹ ⊎ S¹ → Σ S¹ TrivialCover
  Map (inl base) = base , false
  Map (inl (loop i)) = (loop i) , false
  Map (inr base) = base , true
  Map (inr (loop i)) = loop i , true

  Inv : Σ S¹ TrivialCover → S¹ ⊎ S¹
  Inv (base , false) = inl base
  Inv (base , true) = inr base
  Inv (loop i , false) = inl (loop i)
  Inv (loop i , true) = inr (loop i)

  MapInvId : (x : Σ S¹ TrivialCover) → Map (Inv x) ≡ x
  MapInvId (base , false) = refl
  MapInvId (base , true) = refl
  MapInvId (loop i , false) = refl
  MapInvId (loop i , true) = refl

  InvMapId : (x : S¹ ⊎ S¹) → Inv (Map x) ≡ x
  InvMapId (inl base) = refl
  InvMapId (inl (loop i)) = refl
  InvMapId (inr base) = refl
  InvMapId (inr (loop i)) = refl

  PathType : S¹ ⊎ S¹ ≃ Σ S¹ TrivialCover
  PathType =  isoToEquiv (iso Map Inv MapInvId InvMapId)

module Double where
  Cover : S¹ → Type
  Cover base = Bool
  Cover (loop i) = Flip.IsPath i

  Bundle : Type
  Bundle = Σ S¹ Cover

-- Bundle ≃ S¹ as covers of S¹
-- two things equal in space not equal in fiber
-- two ℕs
-- send Flip across Equiv Bool MyBool
