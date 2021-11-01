module Notation.HaskellDollar where

open import Cubical.Foundations.Prelude

private
  variable
    u v : Level

application : {A : Type u} {B : A → Type v} (f : (a : A) → B a) (a : A) → B a
application f a = f a

infixr 5 application
syntax application f a = f $ a

-- compExample : {A B C : Type} (_*_ : A → A → A) (f : A → B) (g : B → C) (a : A) → C
-- compExample _*_ f g a = g $ f $ a * a
