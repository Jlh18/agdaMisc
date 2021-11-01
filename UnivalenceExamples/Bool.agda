{-# OPTIONS --cubical #-}
module UnivalenceExamples.Bool where

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

data MyBool : Type where
  tt : MyBool
  ff : MyBool

-- data Emp : Type where

-- EmpElim : (A : Type u) → Emp → A
-- EmpElim A ()

-- MyBoolDiscrete : ff ≡ tt → Emp
-- MyBoolDiscrete p = {!!}

module BoolMyBool where

  Map : Bool → MyBool
  Map false = ff
  Map true = tt

  Inv : MyBool → Bool
  Inv tt = true
  Inv ff = false

  MapInvId : (y : MyBool) → Map (Inv y) ≡ y
  MapInvId tt = refl
  MapInvId ff = refl

  InvMapId : (y : Bool) → Inv (Map y) ≡ y
  InvMapId false = refl
  InvMapId true = refl

  -- FibContr : (y : MyBool) (fib : fiber Map y) → (Inv y , MapInvId y) ≡ fib
  -- FibContr tt (false , snd₁) i = {!!} , {!!}
  -- FibContr tt (true , snd₁) i = {!!}
  -- FibContr ff fib i = {!!}

  -- BoolMyBool : Bool ≃ MyBool
  -- BoolMyBool = Map , record { equiv-proof = λ y →
  --   --centre
  --   (Inv y , MapInvId y) ,
  --   -- contr
  --   λ fib → {!!} }

  Equiv : Bool ≃ MyBool
  Equiv = isoToEquiv (iso Map Inv MapInvId InvMapId)

  Eq : Bool ≡ MyBool
  Eq = ua Equiv

  CompFromEq : Bool → MyBool
  CompFromEq b = comp (λ i → Eq i) {φ = i0} (λ i → λ {()}) b

  TranspFromEq : Bool → MyBool
  TranspFromEq = transportPath Eq

Flip : Bool → Bool
Flip false = true
Flip true = false

module Flip where
  Inv : (x : Bool) → Flip (Flip x) ≡ x
  Inv false = refl
  Inv true = refl

  IsPath : Bool ≡ Bool
  IsPath = isoToPath (iso Flip Flip Inv Inv)

private

-- send Flip across Equiv Bool MyBool
  BoolToBoolEqMyBoolToMyBool : (Bool → Bool) ≡ (MyBool → MyBool)
  BoolToBoolEqMyBoolToMyBool i = (BoolMyBool.Eq i) → (BoolMyBool.Eq i)

  MyFlip : MyBool → MyBool
  MyFlip = transportPath {A = Bool → Bool} {B = MyBool → MyBool} BoolToBoolEqMyBoolToMyBool Flip

  FlipMyFlipEq : (i : I) → BoolMyBool.Eq i → BoolMyBool.Eq i
  FlipMyFlipEq i = transport-filler BoolToBoolEqMyBoolToMyBool Flip i

  MyFlipInv : (x : MyBool) → MyFlip (MyFlip x) ≡ x
  MyFlipInv = transportPath
    (λ i → (x : BoolMyBool.Eq i) → FlipMyFlipEq i (FlipMyFlipEq i x) ≡ x) Flip.Inv
