{-# OPTIONS --cubical #-}

module UnivalenceExamples.Structures where

open import Cubical.Foundations.Everything

open import Agda.Primitive

data PointedList {u : Level} (A : Type u) : Type u where
  One : A → PointedList A
  Cons : A → PointedList A → PointedList A

record _×_ {u v : Level} (A : Type u) (B : Type v) : Type (v ⊔ u) where
  constructor _,_
  field
    fst : A
    snd : B

PointedListProd : {u : Level} (L : PointedList (Type u)) → Type u
PointedListProd (One A) = A
PointedListProd (Cons A L) = A × PointedListProd L

data Structure (u v : Level) (param : PointedList (Type u)) : Type (lsuc (u ⊔ v)) where
  mk : ((PointedListProd param) → Type v) → (Structure u v param)

data ⊥ : Type₀ where

⊥Elim : {u : Level} {C : Type u} → ⊥ → C
⊥Elim ()

record ⊤ : Type₀ where

data BigNat : SSetω where
  Nil : BigNat
  Suc : BigNat → BigNat

_<_ : BigNat → BigNat → Type
k < Nil = ⊥
Nil < Suc n = ⊤
Suc k < Suc n = k < n

-- data StructureTuple : BigNat → SSetω where
--   Empty : StructureTuple Nil
--   Cons : (n : BigNat) (S : Structure) → StructureTuple n → StructureTuple (Suc n)

-- The structure of a pair of structures.
-- [[[_,_]]] : {u0 u1 v w : Level} {dom0 : Type u0} (dom1 : Type v) (S0 : dom0 → Type u0)
--   (S1 : dom1 → Type u1) → dom0 → Type v
-- [[[ S , S1 ]]] A = S A × S1 A


-- StructureTupleToStruc : {n : BigNat} → (StructureTuple n) → Structure
-- StructureTupleToStruc Empty = mk lzero lzero lzero ⊥  ⊥ ⊥Elim
-- StructureTupleToStruc (Cons n S SS) = mk {!!} {!!} {!!} {!!} {!!} {!!}

-- Coe : {n : BigNat} → (StructureTuple n) → (k : BigNat) → (k < n) → Structure
-- Coe {.(Suc n)} (Cons n S SS) Nil hkn = S
-- Coe {.(Suc n)} (Cons n S SS) (Suc k) hkn = Coe SS k hkn

-- _×_ : {u : Level} (A B : Type u) → Type u
-- A × B = Σ A (λ a → B)

-- S is a structure on terms of a type dom.
-- A is a term in dom with a structure of S. Call these term-with-structure S.
-- crr A returns the "carrier"/"underlying" term of A.
crr : {u v : Level} {dom : Type u} {S : dom → Type v}
  (A : Σ dom S) → dom
crr = fst

-- Extracts the structure on a term-with-structure.
property : {u v : Level} {dom : Type u} {S : dom → Type v}
  (A : Σ dom S) → S (crr A)
property A = snd A

-- We make the structure on types expressing
-- the inhabitedness of a type.
module Inhabited where

  -- the structure
  Str : {u : Level} (A : Type u) → Type u
  Str A = A

  -- effective renames `property` to `Default`, for "default term".
  Default : {u : Level} (A : Σ (Type u) Str) → crr A
  Default = property

  isMor : {u : Level} {A B : Σ (Type u) Str} (f : crr A → crr B) → Type u
  isMor {u} {A} {B} f = f (Default A) ≡ Default B

  -- A morphism of inhabited types A -> B is
  -- a map on the carrier types such that
  -- the default term is mapped to the default term (up to a path).
  Mor : {u : Level} (A B : Σ (Type u) Str) → Type u
  Mor A B = Σ (crr A → crr B) λ f → isMor {_} {A} {B} f

-- The type of inhabited types.
Inhabited : {u : Level} → Type (ℓ-suc u)
Inhabited {u} = Σ (Type u) Str where open Inhabited -- locally opens module

open import Cubical.Data.Unit

InhabitedUnit : Inhabited {ℓ-zero}
InhabitedUnit = Unit , tt

open import Cubical.Data.Bool

InhabitedBool : Inhabited {ℓ-zero}
InhabitedBool = Bool , true

⊤' : Inhabited.Mor InhabitedUnit InhabitedBool
⊤' = (λ x → Inhabited.Default InhabitedBool) , refl

-- `crr ⊤` computes `λ x → true` as desired.

-- Types equipped with an endomorphism
module Evolving where

  -- the structure
  Str : {u : Level} → Type u → Type u
  Str A = A → A

  -- the structure on maps of carrier types to be
  -- "morphisms of evolving types"
  isMor : {u : Level} {A B : Σ (Type u) Str} (f : crr A → crr B) → Type u
  isMor {_} {A} {B} f = (a : crr A) → f (property A a) ≡ property B (f a)

  -- the type of morphisms of evolving types
  Mor : {u : Level} (A B : Σ (Type u) Str) → Type u
  Mor A B = Σ (crr A → crr B) λ f → isMor {_} {A} {B} f

-- The structure of a pair of structures.
[[_,_]] : {u v : Level} {dom : Type u} (S S1 : dom → Type v) → dom → Type v
[[ S , S1 ]] A = Σ (S A) (λ x → S1 A)

-- "Coercions" from terms-with-structure-[[ S , S1 ]] to
-- terms-with-structure-S.
-- There should be better way of doing this,
-- don't see how this generalises to many structures.
lcoe : {u v : Level} {dom : Type u} {S S1 : dom → Type v}
  (A : Σ dom [[ S , S1 ]]) → Σ dom S
lcoe A = (crr A) , (fst (property A))

-- Similar, but for the structure on the right.
rcoe : {u v : Level} {dom : Type u} {S S1 : dom → Type v}
  (A : Σ dom [[ S , S1 ]]) → Σ dom S1
rcoe A = (crr A) , (snd (property A))

-- The type of "Nat algebras".
module Nat where

  -- The structure of a Nat algebra is
  -- an inhabited, evolving type.
  Str : {u : Level} (A : Type u) → Type u
  Str A = [[ Inhabited.Str , Evolving.Str ]] A

  -- zero is the default inhabitant.
  Zero : {u : Level} (A : Σ (Type u) Str) → crr A
  Zero A = fst (property A)

  -- the successor function is the evolution map of the evolving structure.
  Succ : {u : Level} (A : Σ (Type u) Str) → crr A → crr A
  Succ A = snd (property A)

  -- morphisms of Nat algebras is
  -- a map that has both structure of morphism of
  -- inhabited and evolving types.
  Mor : {u : Level} (A B : Σ (Type u) Str) → Type u
  Mor A B = Σ (crr A → crr B)
    [[ Inhabited.isMor {A = lcoe A} {B = lcoe B} ,
    Evolving.isMor {A = rcoe A} {B = rcoe B} ]]

-- The type of Nat algebras
NatAlg : {u : Level} → Type (ℓ-suc u)
NatAlg {u} = Σ (Type u) Nat.Str

-- An initial Nat algebra N is one such that
-- for any Nat algebra A, the type of morphisms N -> A is contractible.
isInit : {u : Level} (N : NatAlg {u}) → Type (ℓ-suc u)
isInit N = (A : NatAlg) → isContr (Nat.Mor N A)

open import Cubical.Data.Nat

-- ℕ is indeed a Nat algebra.
NatAlgℕ : NatAlg {ℓ-zero}
NatAlgℕ = ℕ , (0 , suc)
