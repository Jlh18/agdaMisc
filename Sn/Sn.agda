module Sn.Sn where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.HITs.S1
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Prelude
open import Sn.DifferentS1s

Ω¹ : {X : Type} (x : X) → Type
Ω¹ x = x ≡ x

data susp (X : Type) : Type where
  north : susp X
  south : susp X
  merid : (x : X) → north ≡ south

Sphere : (n : ℕ) → Type
Sphere zero = Bool
Sphere (suc n) = susp (Sphere n)

data 𝕀 : Type where
  𝕀0 : 𝕀
  𝕀1 : 𝕀
  𝕀Path : 𝕀0 ≡ 𝕀1

Disk : (n : ℕ) → Type
Disk zero = 𝕀
Disk (suc n) = susp (Disk n)

SphereToDisk : {n : ℕ} → Sphere n → Disk n
SphereToDisk {zero} false = 𝕀0
SphereToDisk {zero} true = 𝕀1
SphereToDisk {suc n} north = north
SphereToDisk {suc n} south = south
SphereToDisk {suc n} (merid x i) = merid (SphereToDisk x) i

hTrivial : (n : ℕ) (X : Type) → Type
hTrivial n X = (boundary : Sphere n → X)
  → Σ[ filler ∈ (Disk n → X) ] ((x : Sphere n) → boundary x ≡ filler (SphereToDisk x))

---------------------------

hTrivial0→isProp : (X : Type) → hTrivial 0 X → isProp X
hTrivial0→isProp X h x y =
    x
  ≡⟨ boundaryCondition false ⟩
    filler 𝕀0
  ≡⟨ (λ i → filler (𝕀Path i)) ⟩
    filler 𝕀1
  ≡⟨ sym (boundaryCondition true) ⟩
    y ∎ where

    boundary : Sphere 0 → X
    boundary false = x
    boundary true = y

    filler = h boundary .fst
    boundaryCondition = h boundary .snd

isProp→hTrivial0 : (X : Type) → isProp X → hTrivial 0 X
isProp→hTrivial0 X h boundary = filler , boundaryCondition where

  filler : 𝕀 → X
  filler 𝕀0 = boundary false
  filler 𝕀1 = boundary true
  filler (𝕀Path i) = h (boundary false) (boundary true) i

  boundaryCondition : (x : Sphere 0) → boundary x ≡ filler (SphereToDisk x)
  boundaryCondition false = refl
  boundaryCondition true = refl

---------------------------
{-
isHLevel : (n : ℕ) (X : Type) → Type
isHLevel zero = isProp
isHLevel (suc n) = λ X → (x y : X) → isHLevel n (x ≡ y)

---------------------------

Sphere→SphereSuc : (n : ℕ) → Sphere n → Sphere (suc n)
Sphere→SphereSuc zero false = north
Sphere→SphereSuc zero true = south
Sphere→SphereSuc (suc n) north = north
Sphere→SphereSuc (suc n) south = south
Sphere→SphereSuc (suc n) (merid x i) = merid (Sphere→SphereSuc n x) i

boundarySuc→boundary : (n : ℕ) {X : Type} (b : Sphere (suc n) → X) → Sphere n → X
boundarySuc→boundary n b s = b (Sphere→SphereSuc n s)

hTrivialSuc→hTrivialPathSpace : {n : ℕ} {X : Type} → hTrivial (suc n) X → (x y : X) → hTrivial n (x ≡ y)
hTrivialSuc→hTrivialPathSpace {zero} {X} h x y boundary = filler , boundaryCondition where

  boundary1 : Sphere 1 → X
  boundary1 north = x
  boundary1 south = y
  boundary1 (merid false i) = boundary false i
  boundary1 (merid true i) = boundary true i

  filler1           = h boundary1 .fst
  boundary1≡filler1 = h boundary1 .snd

  fillerAux : I → x ≡ y
  fillerAux i =
      x
    ≡⟨ boundary1≡filler1 north ⟩
      filler1 (merid (𝕀Path i) i0)
    ≡⟨ (λ j → filler1 (merid (𝕀Path i) j)) ⟩
      filler1 (merid (𝕀Path i) i1)
    ≡⟨ sym (boundary1≡filler1 south) ⟩
      y ∎

  filler : Disk 0 → x ≡ y
  filler 𝕀0 = fillerAux i0
  filler 𝕀1 = fillerAux i1
  filler (𝕀Path i) = fillerAux i

  boundaryCondition : (s : Sphere 0) → boundary s ≡ filler (SphereToDisk s)
  boundaryCondition false = {!!}
  boundaryCondition true = {!!}

-- ({!h boundary1 .snd north!} ∙∙ {!λ j → h boundary1 .fst (merid (𝕀Path i) j)!} ∙∙ {!!})-- {!λ i → (h boundary1 .fst) ?!}

hTrivialSuc→hTrivialPathSpace {suc n} {X} h x y boundary = {!!} , {!!} where

  filler : Disk (suc n) → x ≡ y
  filler = {!!}

hTrivial→isHLevel :
  (n : ℕ) (X : Type) → hTrivial n X → isHLevel n X
hTrivial→isHLevel zero X h x y =
      x
    ≡⟨ h boundary .snd false ⟩
      filler 𝕀0
    ≡⟨ cong filler 𝕀Path ⟩
      filler 𝕀1
    ≡⟨ sym (h boundary .snd true) ⟩
      y ∎
    where

    boundary : Bool → X
    boundary false = x
    boundary true = y

    filler = h boundary .fst

hTrivial→isHLevel (suc n) X h x y = hTrivial→isHLevel n (x ≡ y) (hTrivialSuc→hTrivialPathSpace h x y)


---------------------------
-}

S1≅Sphere1 : S1 ≅ Sphere 1
S1≅Sphere1 = iso fun inv rightInv leftInv where

  fun : S1 → Sphere 1
  fun base0 = north
  fun base1 = south
  fun (path0 i) = merid true i
  fun (path1 i) = sym (merid false) i

  inv : Sphere 1 → S1
  inv north = base0
  inv south = base1
  inv (merid false i) = sym path1 i
  inv (merid true i) = path0 i

  rightInv : section fun inv
  rightInv north = refl
  rightInv south = refl
  rightInv (merid false i) = refl
  rightInv (merid true i) = refl

  leftInv : retract fun inv
  leftInv base0 = refl
  leftInv base1 = refl
  leftInv (path0 i) = refl
  leftInv (path1 i) = refl

S1≡Sphere1 : S1 ≡ Sphere 1
S1≡Sphere1 = isoToPath S1≅Sphere1

S¹≡Sphere1 : S¹ ≡ Sphere 1
S¹≡Sphere1 = S¹≡S1 ∙ S1≡Sphere1
