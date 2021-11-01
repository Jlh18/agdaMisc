{-# OPTIONS --cubical #-}
module HITs.I where

open import Cubical.Foundations.Everything

private
  variable
    u : Level


data 𝕀 {u : Level} : Type u where
  𝕀s : 𝕀
  𝕀t : 𝕀
  𝕀path : Path 𝕀 𝕀s 𝕀t

-- seg : {u : Level} → 𝕀s {u} ≡ 𝕀t
-- seg = pathToId 𝕀path

-- 𝕀Elim : (C : Type v) (cs : C) (ct : C) (cseg : cs ≡ ct) → 𝕀 {u} → C
-- 𝕀Elim C cs ct cseg 𝕀s = cs
-- 𝕀Elim C cs ct cseg 𝕀t = ct
-- 𝕀Elim C cs ct cseg (𝕀path i) = idToPath cseg i

-- IdOver : {A : Type u} (C : A → Type v) {a b : A} (xa : C a) (xb : C b) (p : a ≡ b)
--   → Type v
-- IdOver C xa xb p = transport C p xa ≡ xb

-- 𝕀dElim : (C : 𝕀 → Type v) (cs : C 𝕀s) (ct : C 𝕀t) (cseg : IdOver C cs ct seg)
--   → (i : 𝕀 {u}) → C i
-- 𝕀dElim C cs ct cseg 𝕀s = cs
-- 𝕀dElim C cs ct cseg 𝕀t = ct
-- 𝕀dElim C cs ct cseg (𝕀path i) = {!!}

--   Σ𝕀To𝕀toA : {A : Type u} → Σ𝕀 A → 𝕀 {u} → A
--   Σ𝕀To𝕀toA p = 𝕀Elim _ (pr₁ p) (pr₁ (pr₂ p)) (pr₂ (pr₂ p))

--   𝕀ToAToΣ𝕀 : {A : Type u} → (𝕀 {u} → A) → Σ𝕀 A
--   𝕀ToAToΣ𝕀 p = (p 𝕀s) , ((p 𝕀t) ,  ap p seg)


Σ𝕀 : Type u → Type u
Σ𝕀 A = Σ A λ x → Σ A (λ y → x ≡ y)


Σ𝕀Iso𝕀ToA : {A : Type u} → Iso (Σ𝕀 A) (𝕀 {u} → A)
Σ𝕀Iso𝕀ToA = iso Σ𝕀To𝕀toA 𝕀ToAToΣ𝕀
  (λ b → funExt (λ i → Section b i)) (λ a → refl)
  where
  Σ𝕀To𝕀toA : {A : Type u} → Σ𝕀 A → 𝕀 {u} → A
  Σ𝕀To𝕀toA (p1 , p2 , p3) 𝕀s = p1
  Σ𝕀To𝕀toA (p1 , p2 , p3) 𝕀t = p2
  Σ𝕀To𝕀toA (p1 , p2 , p3) (𝕀path i) = p3 i

  𝕀ToAToΣ𝕀 : {A : Type u} → (𝕀 {u} → A) → Σ𝕀 A
  𝕀ToAToΣ𝕀 p = (p 𝕀s) , ((p 𝕀t) ,  cong p 𝕀path)

  Section : {A : Type u} (b : 𝕀 → A) (i : 𝕀) → Σ𝕀To𝕀toA (𝕀ToAToΣ𝕀 b) i ≡ b i
  Section b 𝕀s = refl
  Section b 𝕀t = refl
  Section b (𝕀path x) = refl
