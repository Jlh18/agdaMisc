{-# OPTIONS --cubical #-}
module HITs.I where

open import Cubical.Foundations.Everything

private
  variable
    u : Level


data π {u : Level} : Type u where
  πs : π
  πt : π
  πpath : Path π πs πt

-- seg : {u : Level} β πs {u} β‘ πt
-- seg = pathToId πpath

-- πElim : (C : Type v) (cs : C) (ct : C) (cseg : cs β‘ ct) β π {u} β C
-- πElim C cs ct cseg πs = cs
-- πElim C cs ct cseg πt = ct
-- πElim C cs ct cseg (πpath i) = idToPath cseg i

-- IdOver : {A : Type u} (C : A β Type v) {a b : A} (xa : C a) (xb : C b) (p : a β‘ b)
--   β Type v
-- IdOver C xa xb p = transport C p xa β‘ xb

-- πdElim : (C : π β Type v) (cs : C πs) (ct : C πt) (cseg : IdOver C cs ct seg)
--   β (i : π {u}) β C i
-- πdElim C cs ct cseg πs = cs
-- πdElim C cs ct cseg πt = ct
-- πdElim C cs ct cseg (πpath i) = {!!}

--   Ξ£πToπtoA : {A : Type u} β Ξ£π A β π {u} β A
--   Ξ£πToπtoA p = πElim _ (prβ p) (prβ (prβ p)) (prβ (prβ p))

--   πToAToΞ£π : {A : Type u} β (π {u} β A) β Ξ£π A
--   πToAToΞ£π p = (p πs) , ((p πt) ,  ap p seg)


Ξ£π : Type u β Type u
Ξ£π A = Ξ£ A Ξ» x β Ξ£ A (Ξ» y β x β‘ y)


Ξ£πIsoπToA : {A : Type u} β Iso (Ξ£π A) (π {u} β A)
Ξ£πIsoπToA = iso Ξ£πToπtoA πToAToΞ£π
  (Ξ» b β funExt (Ξ» i β Section b i)) (Ξ» a β refl)
  where
  Ξ£πToπtoA : {A : Type u} β Ξ£π A β π {u} β A
  Ξ£πToπtoA (p1 , p2 , p3) πs = p1
  Ξ£πToπtoA (p1 , p2 , p3) πt = p2
  Ξ£πToπtoA (p1 , p2 , p3) (πpath i) = p3 i

  πToAToΞ£π : {A : Type u} β (π {u} β A) β Ξ£π A
  πToAToΞ£π p = (p πs) , ((p πt) ,  cong p πpath)

  Section : {A : Type u} (b : π β A) (i : π) β Ξ£πToπtoA (πToAToΞ£π b) i β‘ b i
  Section b πs = refl
  Section b πt = refl
  Section b (πpath x) = refl
