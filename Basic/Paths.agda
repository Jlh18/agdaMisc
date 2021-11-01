{-# OPTIONS --cubical #-}
module Basic.Paths where 

open import Cubical.Foundations.Everything 

private
  variable
    u : Level

PathToEnd : {A : Type u} {a b : A} (p : a ≡ b) → (i : I) → p i ≡ b
PathToEnd p i j = p (i ∨ j)

