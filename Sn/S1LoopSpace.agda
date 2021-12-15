module Sn.S1LoopSpace where

open import Cubical.Core.Everything
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Int
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.Data.Sigma
open import Cubical.HITs.KleinBottle
open import Cubical.HITs.Truncation.Base
open import Cubical.HITs.Truncation.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

open S¹

private
  variable
    u : Level

subst→Pointwise : {A : Type u} {P : A → Type u} {Q : A → Type u} {x y : A} (p : x ≡ y)
  (fₓ : P x → Q x) → (ŷ : P y) →
  subst (λ (a : A) → P a → Q a) p fₓ ŷ ≡
    subst (λ a → Q a) p (fₓ (subst (λ a → P a) (sym p) ŷ))
subst→Pointwise {u} {A} {P} {Q} {x} {y} =
  J (
    λ y₁ p₁ → (fₓ : P x → Q x) → (ŷ : P y₁) →
    subst (λ (a : A) → P a → Q a) p₁ fₓ ŷ ≡
      subst (λ a → Q a) p₁ (fₓ (subst (λ a → P a) (sym p₁) ŷ))
    )
    (λ fₓ ŷ → refl)

subst→ : {A : Type u} (P : A → Type u) (Q : A → Type u) {x y : A} (p : x ≡ y)
  (fₓ : P x → Q x) →
  subst (λ (a : A) → P a → Q a) p fₓ ≡
    λ ŷ → subst (λ a → Q a) p (fₓ (subst (λ a → P a) (sym p) ŷ))
subst→ P Q p fₓ = funExt (λ ŷ → subst→Pointwise p fₓ ŷ)


--------------------------------------------

-- To map out of S¹ it suffices to give a point above base and a path over loop based there
S¹Rec : {M : S¹ → Type u} (x : M base) (p : PathP (λ i → M (loop i)) x x)
        → (s : S¹) → M s
S¹Rec x p base = x
S¹Rec x p (loop i) = p i

--------------------------------------------

--------------------------------------------
succPath : ℤ ≡ ℤ
succPath = isoToPath (iso sucℤ predℤ (sucPred) predSuc)

bundle : S¹ → Type
bundle base = ℤ
bundle (loop i) = succPath i

fun : (x : S¹) → base ≡ x → bundle x
fun x p = subst bundle p 0

loop^_ : ℤ → base ≡ base
loop^ pos zero = refl
loop^ pos (suc n) = (loop^ pos n) ∙ loop
loop^ negsuc zero = sym loop
loop^ negsuc (suc n) = (loop^ (negsuc n)) ∙ (sym loop)

-- _untilP_ : {u : Level} {B : I → Type u} {b0 : B i0}
--   (p : (i : I) → B i) (j : I) → PathP (λ i → B (i ∧ j)) b0 (transport (λ i → B (i ∧ j)) b0)
-- _untilP_ {B = B} {b0} p j = transport-filler (λ i → B (i ∧ j)) b0

-- _until_ : {u : Level} {B : Type u} (p : (i : I) → B) (j : I) → Path B (p i0) (p j)
-- _until_ {B = B} p j = λ i → p (i ∧ j)

predℤ∙ : (n : ℤ) → (loop^ predℤ n) ∙ loop ≡ loop^ n
predℤ∙ (pos zero) = lCancel loop
predℤ∙ (pos (suc n)) = refl
predℤ∙ (negsuc zero) =
    ((loop ⁻¹ ∙ loop ⁻¹) ∙ loop)
  ≡⟨ sym (assoc (loop ⁻¹) (loop ⁻¹) loop) ⟩
    loop ⁻¹ ∙ (loop ⁻¹ ∙ loop)
  ≡⟨ cong (λ p → loop ⁻¹ ∙ p) (lCancel loop) ⟩
    loop ⁻¹ ∙ refl
  ≡⟨ sym (rUnit _) ⟩
    (loop ⁻¹) ∎
predℤ∙ (negsuc (suc n)) =
    ((((loop^ negsuc n) ∙ (sym loop)) ∙ (sym loop)) ∙ loop)
  ≡⟨ sym (assoc _ _ _) ⟩
    ((loop^ negsuc n) ∙ (sym loop)) ∙ (sym loop) ∙ loop
  ≡⟨ cong (λ p → ((loop^ negsuc n) ∙ (sym loop)) ∙ p) (lCancel loop) ⟩
    ((loop^ negsuc n) ∙ (sym loop)) ∙ refl
  ≡⟨ sym (rUnit _) ⟩
  (loop^ negsuc n) ∙ (sym loop) ∎

onKlein : (p q : point ≡ point) → subst (_≡_ point) p q ≡ q ∙ p
onKlein p q = refl

substPath : {A : Type u} {x y z : A} (q : x ≡ y) (p : y ≡ z) → subst (_≡_ x) p q ≡ q ∙ p
substPath {u} {A} {x} {y} {z} q p = J (λ z p → subst (_≡_ x) p q ≡ q ∙ p)
                                (
                                  subst (_≡_ x) refl q
                                ≡⟨ transportRefl q ⟩
                                  q
                                ≡⟨ rUnit q ⟩
                                  q ∙ refl ∎
                                )
                                p

rwe : (x : S¹) → bundle x → base ≡ x
rwe base = {!!}
rwe (loop i) = {!!}

{-

private
  variable
    ℓ : Level

transport→ : {A B : I → Type ℓ} (f : A i0 → B i0) (x : A i0) →
  transport (λ i → A i → B i) f (transport (λ i → A i) x) ≡ transport (λ i → B i) (f x)
transport→ {A = A} {B = B} f x =
  J
  (λ A1 A →
    transport (λ i → A i → B i) f (transport (λ i → A i) x) ≡ transport (λ i → B i) (f x))
  (J
    (λ B1 B →
      transport (λ i → A i0 → B i) f (transport (λ i → A i0) x) ≡ transport (λ i → B i) (f x))
   (
       transport (λ i → A i0 → B i0) f (transport (λ i → A i0) x)
     ≡⟨ cong (transport (λ i → A i0 → B i0) f) (transportRefl x) ⟩
       transport (λ i → A i0 → B i0) f x
     ≡⟨ cong (λ g → g x) (transportRefl f) ⟩
       f x
     ≡⟨ sym (transportRefl (f x)) ⟩
       transport (λ i → B i0) (f x) ∎
   )
    λ i → B i
  )
  λ i → A i
  -- J (λ A1 A → transport (λ i → A i → B i) f ≡ λ a1 → transport B (f (transport (sym A) a1)))
  -- (funExt (λ a1 → refl)) A
-}

transport→' : {A0 A1 B0 B1 : Type} {A : A0 ≡ A1} {B : B0 ≡ B1} (f : A0 → B0) →
  transport (λ i → A i → B i) f ≡ λ a1 → transport B (f (transport (sym A) a1))
transport→' {A = A} {B = B} f = refl

{-
pathToFun→ : {A0 A1 B0 B1 : Type} {A : A0 ≡ A1} {B : B0 ≡ B1} (f : A0 → B0) →
  pathToFun (λ i → A i → B i) f ≡ λ a1 → pathToFun B (f (pathToFun (sym A) a1))
pathToFun→ {A = A} {B = B} f =
  J (λ A1 A → pathToFun (λ i → A i → B i) f ≡ λ a1 → pathToFun B (f (pathToFun (sym A) a1)))
  refl A

pathToFun→' : {A0 A1 B0 B1 : Type} {A : A0 ≡ A1} {B : B0 ≡ B1} (f : A0 → B0) →
  pathToFun (λ i → A i → B i) f ≡ λ a1 → pathToFun B (f (pathToFun (sym A) a1))
pathToFun→' {A0} {A1} {B0} {B1} {A} {B} f =
  J (λ A1 A → pathToFun (λ i → A i → B i) f ≡ λ a1 → pathToFun B (f (pathToFun (sym A) a1)))
  (
    J (λ B1 B → pathToFun (λ i → A0 → B i) f ≡ λ a → pathToFun B (f (pathToFun refl a)))
    (
      funExt λ a →
        pathToFun refl f a
      ≡⟨ cong (λ g → g a) (pathToFunRefl f) ⟩
        f a
      ≡⟨ sym (pathToFunRefl (f a)) ⟩
        pathToFun refl (f a)
      ≡⟨ cong (λ x → pathToFun refl (f x)) (sym (pathToFunRefl a)) ⟩
        pathToFun refl (f (pathToFun refl a)) ∎
    )
    B
  )
  A -}


rewind : (x : S¹) → bundle x → base ≡ x
rewind = S¹Rec loop^_ (
  Iso.inv (PathPIsoPath (λ i → bundle (loop i) → (base ≡ loop i)) loop^_ loop^_)
    (
      subst (λ x → bundle x → base ≡ x) loop loop^_
    ≡⟨ subst→ bundle (_≡_ base) loop loop^_ ⟩ -- subst when the motive is a → type
     (λ ŷ → subst (_≡_ base) loop (loop^ subst bundle (sym loop) ŷ))
    ≡⟨ refl ⟩ -- subst (_≡_ base) loop p =ₑₓₜ p ∙ loop
     (λ ŷ → (loop^ subst bundle (sym loop) ŷ) ∙ loop)
    ≡⟨ refl ⟩ -- subst bundle (sym loop) =ₑₓₜ fun base (sym loop) =ₑₓₜ predℤ
     (λ ŷ → (loop^ predℤ ŷ) ∙ loop)
    ≡⟨ funExt predℤ∙ ⟩
     loop^_ ∎
    )
  )

-- rewind : (x : S¹) → bundle x → base ≡ x
-- rewind base = loop^_
-- rewind (loop i) = Iso.rewind (PathPIsoPath (λ i → bundle (loop i) → (base ≡ loop i)) loop^_ loop^_)
--   (
--     subst (λ x → bundle x → base ≡ x) loop loop^_
--   ≡⟨ subst→ bundle (_≡_ base) loop loop^_ ⟩ -- subst when the motive is a → type
--     (λ ŷ → subst (_≡_ base) loop (loop^ subst bundle (sym loop) ŷ))
--   ≡⟨ refl ⟩ -- subst (_≡_ base) loop p =ₑₓₜ p ∙ loop
--     (λ ŷ → (loop^ subst bundle (sym loop) ŷ) ∙ loop)
--   ≡⟨ refl ⟩ -- subst bundle (sym loop) =ₑₓₜ fun base (sym loop) =ₑₓₜ predℤ
--     (λ ŷ → (loop^ predℤ ŷ) ∙ loop)
--   ≡⟨ funExt predℤ∙ ⟩
--     loop^_ ∎
--   )
--   i

funLoop^ : (n : ℤ) → fun base (loop^ n) ≡ n
funLoop^ (pos zero) = refl
funLoop^ (pos (suc n)) =
    fun base ((loop^ pos n) ∙ loop)
  ≡⟨ refl ⟩
    (fun base (loop^ (pos n))) + (fun base loop)
  ≡⟨ refl ⟩
    (sucℤ (fun base (loop^ (pos n))))
  ≡⟨ cong sucℤ (funLoop^ (pos n)) ⟩
    _ ∎
funLoop^ (negsuc zero) = refl
funLoop^ (negsuc (suc n)) =
    fun base ((loop^ negsuc n) ∙ (sym loop))
  ≡⟨ refl ⟩
    (predℤ (fun base (loop^ (negsuc n))))
  ≡⟨ cong predℤ (funLoop^ (negsuc n)) ⟩
    _ ∎

rewindFun : (x : S¹) → (p : base ≡ x) → rewind x (fun x p) ≡ p
rewindFun x = J (λ x p → rewind x (fun x p) ≡ p) refl

funRewind : (x : S¹) → (c : bundle x) → fun x (rewind x c) ≡ c
funRewind x = S¹Rec {M = λ x → (c : bundle x) → fun x (rewind x c) ≡ c}
  funLoop^ (Iso.inv (PathPIsoPath _ _ _) (funExt λ n → isSetℤ _ _ _ _)) x

ΩS¹ = base ≡ base

ΩS¹Isoℤ : Iso (ΩS¹) ℤ
Iso.fun ΩS¹Isoℤ = fun base
Iso.inv ΩS¹Isoℤ = rewind base
Iso.rightInv ΩS¹Isoℤ = funRewind base
Iso.leftInv ΩS¹Isoℤ = rewindFun base

ΩS¹≡ℤ : ΩS¹ ≡ ℤ
ΩS¹≡ℤ = isoToPath ΩS¹Isoℤ

π₁S¹ = ∥ ΩS¹ ∥ 2

π₁S¹≡ℤ : π₁S¹ ≡ ℤ
π₁S¹≡ℤ = π₁S¹
  ≡⟨ cong (λ x → ∥_∥_ x 2) ΩS¹≡ℤ ⟩
    (∥ ℤ ∥ 2)
  ≡⟨ (truncIdempotent 2 isSetℤ) ⟩
    ℤ ∎
