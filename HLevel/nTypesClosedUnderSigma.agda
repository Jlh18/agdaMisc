{-# OPTIONS --cubical #-}
module HLevel.nTypesClosedUnderSigma where

open import Cubical.Foundations.Everything public
open import Cubical.Data.Nat

private
  variable
    u v : Level

PathOver : (B : I → Type v) (x : B i0) (y : B i1) → Type v
PathOver B x y = transport (λ i → B i) x ≡ y

-- PathOver≃PathP : (B : I → Type v) (x : B i0) (y : B i1) → PathOver B x y ≃ PathP B x y
-- PathOver≃PathP B x y = isoToEquiv (iso Map Inv {!!} {!!}) where
--   Map : PathOver B x y → PathP B x y
--   Map p = λ i → transport-filler (λ j → {!B j!}) {!!} {!!}
--   Inv : PathP B x y → PathOver B x y
--   Inv p = {!!}

-- thing = PathPIsoPath

MyHLevel = ℕ

-- why must A be on the left of pattern match for IsoToHLevel to infer {n = n}
isHLevel : ℕ → Type u → Type u
isHLevel zero A = isContr A
isHLevel (suc n) A = (x y : A) → isHLevel n (x ≡ y)

_-Type_ : ℕ → (u : Level) → Type (ℓ-suc u)
n -Type u = Σ (Type u) (isHLevel n)

PathSigmaIso : {A : Type u} (B : A → Type v) (σ0 σ1 : Σ A B) →
   Iso (σ0 ≡ σ1) (Σ (fst σ0 ≡ fst σ1) (λ p → PathP (λ i → B (p i)) (snd σ0) (snd σ1)))
PathSigmaIso B σ0 σ1 = iso Map Inv (λ b → refl) (λ a → refl)
  where
  Map : σ0 ≡ σ1 → Σ (fst σ0 ≡ fst σ1) (λ p → PathP (λ i → B (p i)) (snd σ0) (snd σ1))
  Map p = cong fst p , λ i → snd (p i)

  Inv : Σ (fst σ0 ≡ fst σ1) (λ p → PathP (λ i → B (p i)) (snd σ0) (snd σ1)) → σ0 ≡ σ1
  Inv (σ , over) = λ i → (σ i) , over i

PathSigma : {A : Type u} (B : A → Type v) (σ0 σ1 : Σ A B) →
  (σ0 ≡ σ1) ≃ Σ (fst σ0 ≡ fst σ1) (λ p → PathP (λ i → B (p i)) (snd σ0) (snd σ1))
PathSigma B σ0 σ1 = isoToEquiv (PathSigmaIso B σ0 σ1)

RevTransport : {A B : Type u} → A ≡ B → B → A
RevTransport p b = transport (λ i → p (~ i)) b

IsoToHLevel : {n : MyHLevel} {A : Type u} {B : Type u} → (Iso A B) → isHLevel n B → isHLevel n A
IsoToHLevel {n = n} f = transport (λ i → isHLevel n (isoToPath f (~ i)))

isHLevelΣ : {n : MyHLevel} {A : Type u} {B : A → Type u} (hA : isHLevel n A)
 (hB : (a : A) → isHLevel n (B a)) → isHLevel n (Σ A B)
isHLevelΣ {n = zero} {A} {B} (a₀ , pa) hB =
  let b₀ = fst (hB a₀)
  in -- centre
  (a₀ , b₀) ,
  -- path to centre
  (λ σ → Iso.inv (PathSigmaIso B _ _)
    let pathA = pa (fst σ)
        b₀IsCentre = snd (hB a₀)
    in
    (-- path in A
      pathA ,
      -- corresponding path over, from transport of (snd σ) to b₀
      symP (
        Iso.inv (
          -- Hard fact that PathP iso PathOver
          PathPIsoPath (λ i → B (pathA (~ i))) (snd σ) b₀)
          -- now just use that b₀ is the centre
          (sym (b₀IsCentre (transport (λ i → B (pa (fst σ) (~ i))) (snd σ) )))
      )
    )
  )
isHLevelΣ {n = suc n} {A} {B} hA hB σx σy = IsoToHLevel
  (PathSigmaIso B σx σy)
  -- suffices now to show the Sigma (using induction hyp) isHLevel
  (
    isHLevelΣ {n = n}  (hA (fst σx) (fst σy))
    (λ pA → IsoToHLevel (PathPIsoPath (λ i → B (pA i)) (snd σx) (snd σy)) (hB (fst σy) _ (snd (σy))))
  )


--  Iso.inv (PathPIsoPath (λ i → B (pathA i)) b₀ (snd σ)) {!!}

-- isSet : (A : Type u) (x y : A) (p q : x ≡ y) → p ≡ q
-- isSet = ?

-- SigmaSet : (A : Type u) (B : A → Type v) → isSet A → ((a : A) → isSet (B a)) → isSet (Σ A B)
-- SigmaSet A B hA hB x y p q =
--   let fstp = cong fst p
--       fstq = cong fst q
--       sndp = snd (Iso.fun (PathSigmaIso B x y) p)
--       sndp = snd (Iso.fun (PathSigmaIso B x y) p)
--   in cong (Iso.inv (PathSigmaIso B x y))
--          (λ i → (λ j → hA (fst x) (fst y) fstp fstq i j) , λ j → {!!})

-- Iso.fun (PathSigmaIso B x y) p

-- module IdSigma where
--   f : {A : Set u} {B : A → Set u} {σ1 σ2 : Σ A B}
--     → σ1 ≡ σ2 → Σ (fst σ1 ≡ fst σ2) (λ p →  snd σ1 ≡ snd σ2 over p)
--   f refl = refl , refl

--   g : {A : Set u} {B : A → Set u} {σ1 σ2 : Σ A B}
--     → Σ (fst σ1 ≡ fst σ2) (λ p →  snd σ1 ≡ snd σ2 over p) → σ1 ≡ σ2
--   g (refl , refl) = refl

--   fg : {A : Set u} {B : A → Set u} {σ1 σ2 : Σ A B}
--     (x : Σ (fst σ1 ≡ fst σ2) (λ p →  snd σ1 ≡ snd σ2 over p)) → f (g x) ≡ x
--   fg (refl , refl) = refl

--   gf : {A : Set u} {B : A → Set u} {σ1 σ2 : Σ A B}
--     (x : σ1 ≡ σ2) → g (f x) ≡ x
--   gf refl = refl

--   Equiv : {A : Set u} {B : A → Set u} {σ1 σ2 : Σ A B}
--     → IsEquiv
--     {A = σ1 ≡ σ2} {B = Σ (fst σ1 ≡ fst σ2) (λ p →  snd σ1 ≡ snd σ2 over p)} f
--   Equiv = (g , fg) , g , gf
