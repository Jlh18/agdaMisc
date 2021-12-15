module Trash.Talk where

open import Cubical.Foundations.Prelude

infix 2 ∃-syntax

∃-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃-syntax = Σ

syntax ∃-syntax A (λ x → B) = ∃ x :: A , B

Prop = Type







data Nat : Type where
  zero : Nat
  succ : Nat → Nat

data True : Prop where
  Trivial : True

data False : Prop where

open Nat
open True

isEven : Nat → Prop
isEven zero = True
isEven (succ zero) = False
isEven (succ (succ n)) = isEven n

existsEven0 : ∃ n :: Nat , isEven n
existsEven0 = zero , Trivial

existsEven2 : ∃ n :: Nat , isEven n
existsEven2 = succ zero , {!!}

isAPoint : Prop → Prop
isAPoint P = (x y : P) → x ≡ y

isAPointTrue : isAPoint True
isAPointTrue Trivial Trivial = refl

substitute : {P Q : Prop} → Q ≡ P → isAPoint P → isAPoint Q
substitute hEq = subst isAPoint (sym hEq)

postulate
  hNotOK : (∃ n :: Nat , isEven n) ≡ True

isAPoint∃ : isAPoint (∃ n :: Nat , isEven n)
isAPoint∃ = substitute hNotOK isAPointTrue

existsEven0≡existsEven2 : existsEven0 ≡ existsEven2
existsEven0≡existsEven2 =
  isAPoint∃ existsEven0 existsEven2

giveTheNat : (∃ n :: Nat , isEven n) → Nat
giveTheNat (n , hn) = n

-- 0≡2 : zero ≡ (succ (succ zero))
-- 0≡2 = cong giveTheNat existsEven0≡existsEven2






-- cong fst
--  (≡True→isAPoint (∃ n :: Nat , isEven n) h existsEven0 existsEven2)

-- do C-c C-n ->> giveTheNat existsEven0  -->> works fine
