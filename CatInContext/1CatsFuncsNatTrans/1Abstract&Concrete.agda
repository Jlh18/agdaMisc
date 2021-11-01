module CatInContext.1CatsFuncsNatTrans.1Abstract&Concrete where

open import Cubical.Core.Everything
open import Cubical.Categories.Category
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming ( Unit to ⊤ )

{- Precategory and isCategory

In `agda` the definition of `Precategory` looks like
the standard definition of a category,
whilst `isCategory`
requires that the `Precategory` has `Hom` as sets. -- Why?
-- For now use isCategory and realize when we need `Hom` being a set

Agda supports notation `C [ X , Y ]` for `C .Hom [ X , Y ]`
and composition between `f : C [ X , Y ]` and `g : C [ Y , Z]`
as `g ∘⟨ C ⟩ f`.

-}

open Precategory
open isCategory

private
  variable u v : Level

{- Set

We define the `Set`, the category of sets.
We will need this for `Yoneda`,
and in general for taking `Hom`.

We take the objects to be sets of `HLevel u`,
denoted `hSet u`.
Taking function space between sets is still a set
(in fact only the points in the image need to be sets)
(we will need this for isCategory),
so we will just take the function space as `Hom`.

PrecategorySet : (u : Level) → Precategory (ℓ-suc u) u
PrecategorySet u = record
                   { ob = hSet u
                   ; Hom[_,_] = λ X Y → X .fst → Y .fst
                   -- Here `X` and `Y` are 'types with structure'.
                   ; id = λ X x → x
                   ; _⋆_ = λ f g x → g (f x)
                   ; ⋆IdL = λ f → funExt λ x → refl
                   ; ⋆IdR = λ f → funExt λ x → refl
                   ; ⋆Assoc = λ f g h → funExt (λ x → refl)
                   }

isCategorySet : isCategory (PrecategorySet u)
isCategorySet = record { isSetHom = λ {X} {Y} → isSetΠ λ x → Y .snd }

From now on use `SET` from `Cubical.Categories.Sets`

-}

thing = idGroupHom

GRP : (u : Level) → Precategory (ℓ-suc u) u
GRP u = record
                       { ob = Group u
                       ; Hom[_,_] = λ G H → GroupHom G H
                       ; id = λ G → idGroupHom
                       ; _⋆_ = compGroupHom
                       ; ⋆IdL = λ f → GroupHom≡ refl
                       ; ⋆IdR = λ f → GroupHom≡ refl
                       ; ⋆Assoc = λ f g h → GroupHom≡ refl
                       }

isCategoryGRP : isCategory (GRP u)
isCategoryGRP = record { isSetHom = isSetGroupHom }

open GroupStr

B_ : Group u → Precategory _ u
B G = record
        { ob = ⊤
        ; Hom[_,_] = λ _ _ → G .fst
        ; id = λ _ → (G .snd) .1g
        ; _⋆_ = (G .snd)._·_
        ; ⋆IdL = lid (G .snd)
        ; ⋆IdR = rid (G .snd)
        ; ⋆Assoc = λ f g h → sym (assoc (G .snd) f g h)
        }

------------------------------
--Exercises
------------------------------

-- Exercise 1.1.i
-- (i) Consider a morphism f : x → y. Show that if there exists a pair of morphisms
-- g, h : y → x so that g f = id x and f h = id y , then g = h and f is an isomorphism.

-- the isomorphism
zigzag→CatIso : {C : Precategory u v} {x y : C .ob}
  (f : C [ x , y ]) (g h : C [ y , x ])
  → (g ∘⟨ C ⟩ f ≡ C .id x) → (f ∘⟨ C ⟩ h ≡ C .id y)
  → CatIso {C = C} x y
zigzag→CatIso {C = C} f g h sec ret =
  catiso f (g ∘⟨ C ⟩ f ∘⟨ C ⟩ h)
    (
      f ∘⟨ C ⟩ (g ∘⟨ C ⟩ f ∘⟨ C ⟩ h)
    ≡⟨ cong (λ f' → f ∘⟨ C ⟩ f') (C .⋆Assoc _ _ _) ⟩
      f ∘⟨ C ⟩ ((g ∘⟨ C ⟩ f) ∘⟨ C ⟩ h)
    ≡⟨ cong (λ f' → f ∘⟨ C ⟩ (f' ∘⟨ C ⟩ h)) sec ⟩
      f ∘⟨ C ⟩ (C .id _ ∘⟨ C ⟩ h)
    ≡⟨ cong (λ f' → f ∘⟨ C ⟩ f') (C .⋆IdR _) ⟩
      f ∘⟨ C ⟩ h
    ≡⟨ ret ⟩
      _ ∎
    )
    (
       (g ∘⟨ C ⟩ f ∘⟨ C ⟩ h) ∘⟨ C ⟩ f
    ≡⟨ cong (λ f' → (g ∘⟨ C ⟩ f') ∘⟨ C ⟩ f) ret ⟩
       (g ∘⟨ C ⟩ C .id _) ∘⟨ C ⟩ f
    ≡⟨ cong (λ f' → f' ∘⟨ C ⟩ f) (C .⋆IdL _) ⟩
      g ∘⟨ C ⟩ f
    ≡⟨ sec ⟩
      _ ∎
    )

-- inverse is unique in (i)
zigzag→Inverse! : {C : Precategory u v} {x y : C .ob}
  (f : C [ x , y ]) (g h : C [ y , x ])
  → (g ∘⟨ C ⟩ f ≡ C .id x) → (f ∘⟨ C ⟩ h ≡ C .id y)
  → g ≡ h
zigzag→Inverse! {C = C} f g h sec ret =
    g
  ≡⟨ sym (C .⋆IdL _) ⟩
    g ∘⟨ C ⟩ C .id _
  ≡⟨ cong (λ f' → g ∘⟨ C ⟩ f') (sym ret) ⟩
    g ∘⟨ C ⟩ (f ∘⟨ C ⟩ h)
  ≡⟨ C .⋆Assoc _ _ _ ⟩
    ((g ∘⟨ C ⟩ f) ∘⟨ C ⟩ h)
  ≡⟨ cong (λ f' → f' ∘⟨ C ⟩ h) sec ⟩
    C .id _ ∘⟨ C ⟩ h
  ≡⟨ C .⋆IdR _ ⟩
    _ ∎
