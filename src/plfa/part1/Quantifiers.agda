{-# OPTIONS --without-K #-}

module plfa.part1.Quantifiers where

open import Agda.Primitive

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm; *-identityˡ; *-identityʳ; *-comm; ≤-reflexive; +-monoˡ-≤)
open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _∘_)

open import plfa.part1.Induction using (suc-inj; +-cancel-r; *-cancel-r; *-cancel-l)
open import plfa.part1.Relations using (Even; Odd)
open import plfa.part1.Equality using (subst-cong; subst₂; subst-cong₂; subst₂≡subst×subst)
open import plfa.part1.Isomorphism using (_≅_; extensionality; Π-extensionality; Is-hProp; Is-hSet; ⊤-Is-hProp; ⊥-Is-hProp; ×-Is-hProp; Σ-eq-iso; hProp-iso; ≅-Is-hProp)
open import plfa.part1.Connectives using (Color)

private
    variable
        i j k l : Level

Π : (A : Set i) → (B : A → Set j) → Set (i ⊔ j)
Π A B = (x : A) → B x

η-Π : {A : Set i} → {B : A → Set j}
    → (f : Π A B)
    → (λ x → f x) ≡ f
η-Π f = refl

Π-elim : {A : Set i} → {B : A → Set j}
    → (f : Π A B)
    → (x : A)
    → B x
Π-elim f x = f x

open _≅_

Π-distrib-× : {A : Set i} → {B : A → Set j} → {C : A → Set k}
    → Π A (λ x → B x × C x) ≅ Π A B × Π A C
Π-distrib-× .to f = (λ x → f x .proj₁) , (λ x → f x .proj₂)
Π-distrib-× .from (g , h) = λ x → (g x) , (h x)
Π-distrib-× .from∘to _ = refl
Π-distrib-× .to∘from _ = refl

⊎Π-implies-Π⊎ : {A : Set i} → {B : A → Set j} → {C : A → Set k}
    → Π A B ⊎ Π A C → Π A (λ x → B x ⊎ C x)
⊎Π-implies-Π⊎ (inj₁ f) x = inj₁ (f x)
⊎Π-implies-Π⊎ (inj₂ g) x = inj₂ (g x)

-- The converse does not hold, consider:
-- A = Bool
-- B false = Empty, B true = Unit
-- C false = Unit, C true = Empty

open Color

Π-× : (B : Color {i} → Set j)
    → Π Color B ≅ B red × B green × B blue
Π-× B .to f = f red , f green , f blue
Π-× B .from (r , g , b) red = r
Π-× B .from (r , g , b) green = g
Π-× B .from (r , g , b) blue = b
Π-× B .from∘to f = Π-extensionality λ { red → refl; green → refl; blue → refl }
Π-× B .to∘from _ = refl

Σ-elim : {A : Set i} → {B : A → Set j} -> {C : Set k}
    → ((x : A) → B x → C)
    → Σ A B → C -- this is just a special case of the dependent curry/uncurry
Σ-elim f (x , y) = f x y

ΠΣ-currying : {A : Set i} → {B : A → Set j} -> {C : Set k}
    → ((x : A) → B x → C) ≅ (Σ A B → C) -- this is just a special case of the dependent curry/uncurry
ΠΣ-currying .to f (x , y) = f x y
ΠΣ-currying .from g x y = g (x , y)
ΠΣ-currying .from∘to f = refl
ΠΣ-currying .to∘from g = extensionality λ { (x , y) → refl }

currying : {A : Set i} → {B : A → Set j} -> {C : (x : A) → B x → Set k}
    → ((x : A) → (y : B x) → C x y) ≅ ((w : Σ A B) → C (proj₁ w) (proj₂ w)) -- this is the dependent curry/uncurry
currying .to f (x , y) = f x y
currying .from g x y = g (x , y)
currying .from∘to f = refl
currying .to∘from g = Π-extensionality λ { (x , y) → refl }

Σ-distrib-⊎ : {A : Set i} → {B : A → Set j} → {C : A → Set k}
    → Σ A (λ x → B x ⊎ C x) ≅ Σ A B ⊎ Σ A C
Σ-distrib-⊎ .to (x , inj₁ y) = inj₁ (x , y)
Σ-distrib-⊎ .to (x , inj₂ z) = inj₂ (x , z)
Σ-distrib-⊎ .from (inj₁ (x , y)) = x , inj₁ y
Σ-distrib-⊎ .from (inj₂ (x , z)) = x , inj₂ z
Σ-distrib-⊎ .from∘to (x , inj₁ y) = refl
Σ-distrib-⊎ .from∘to (x , inj₂ z) = refl
Σ-distrib-⊎ .to∘from (inj₁ (x , y)) = refl
Σ-distrib-⊎ .to∘from (inj₂ (x , z)) = refl

Σ×-implies-xΣ : {A : Set i} → {B : A → Set j} → {C : A → Set k}
    → Σ A (λ x → B x × C x) → (Σ A B) × (Σ A C)
Σ×-implies-xΣ (x , y , z) = (x , y) , (x , z)

-- The converse does not hold, consider:
-- A = Bool
-- B false = Empty, B true = Unit
-- C false = Unit, C true = Empty

Σ-⊎ : (B : Color {i} → Set j)
    → Σ Color B ≅ B red ⊎ B green ⊎ B blue
Σ-⊎ B .to (red , r) = inj₁ r
Σ-⊎ B .to (green , g) = inj₂ (inj₁ g)
Σ-⊎ B .to (blue , b) = inj₂ (inj₂ b)
Σ-⊎ B .from (inj₁ r) = red , r
Σ-⊎ B .from (inj₂ (inj₁ g)) = green , g
Σ-⊎ B .from (inj₂ (inj₂ b)) = blue , b
Σ-⊎ B .from∘to (red , r) = refl
Σ-⊎ B .from∘to (green , g) = refl
Σ-⊎ B .from∘to (blue , b) = refl
Σ-⊎ B .to∘from (inj₁ r) = refl
Σ-⊎ B .to∘from (inj₂ (inj₁ g)) = refl
Σ-⊎ B .to∘from (inj₂ (inj₂ b)) = refl

Even-Σeven : {n : ℕ} → Even n → Σ ℕ (λ m → m * 2 ≡ n)
Odd-Σodd : {n : ℕ} → Odd n → Σ ℕ (λ m → 1 + m * 2 ≡ n)
Even-Σeven Even.zero = zero , refl
Even-Σeven (Even.suc x) with Odd-Σodd x
... | m , refl = suc m , refl
Odd-Σodd (Odd.suc x) with Even-Σeven x
... | m , refl = m , refl
-- Even-Σeven (Even.suc x) = helper-even (Odd-Σodd x) where
--     helper-even : {n : ℕ} → Σ ℕ (λ m → 1 + m * 2 ≡ n) → Σ ℕ (λ m → m * 2 ≡ suc n)
--     helper-even (m , refl) = suc m , refl
-- Odd-Σodd (Odd.suc x) = helper-odd (Even-Σeven x) where
--    helper-odd : {n : ℕ} → Σ ℕ (λ m → m * 2 ≡ n) → Σ ℕ (λ m → 1 + m * 2 ≡ suc n)
--    helper-odd (m , refl) = m , refl

Σeven-Even : {n : ℕ} → Σ ℕ (λ m → m * 2 ≡ n) → Even n
Σodd-Odd : {n : ℕ} → Σ ℕ (λ m → 1 + m * 2 ≡ n) → Odd n
Σeven-Even (zero , refl) = Even.zero -- question: how would type checker force n ≡ 0?
Σeven-Even (suc m , refl) = Even.suc (Σodd-Odd (m , refl))
Σodd-Odd (m , refl) = Odd.suc (Σeven-Even (m , refl))

Codeℕ : ℕ → ℕ → Set
Codeℕ zero zero = ⊤
Codeℕ zero (suc m) = ⊥
Codeℕ (suc n) zero = ⊥
Codeℕ (suc n) (suc m) = Codeℕ n m

rℕ : (n : ℕ) → Codeℕ n n
rℕ zero = tt
rℕ (suc n) = rℕ n

ℕ-eq≅Codeℕ : (n m : ℕ) → n ≡ m ≅ Codeℕ n m -- HoTT Book Theorem 2.13.1
ℕ-eq≅Codeℕ n m = record {
        to = encodeℕ n m;
        from = decodeℕ n m;
        from∘to = decodeℕ-encodeℕ n m;
        to∘from = encodeℕ-decodeℕ n m
    } where
        encodeℕ : (n m : ℕ) → n ≡ m → Codeℕ n m
        encodeℕ n .n refl = rℕ n
        -- encodeℕ n m p = subst (Codeℕ n) p (rℕ n)

        decodeℕ : (n m : ℕ) → Codeℕ n m → n ≡ m
        decodeℕ zero zero tt = refl
        decodeℕ (suc n) (suc m) code = cong suc (decodeℕ n m code)

        decodeℕ-encodeℕ : (n m : ℕ) → (p : n ≡ m) → decodeℕ n m (encodeℕ n m p) ≡ p
        decodeℕ-encodeℕ zero .zero refl = refl
        decodeℕ-encodeℕ (suc n) .(suc n) refl = cong (cong suc) (decodeℕ-encodeℕ n n refl)

        encodeℕ-decodeℕ :(n m : ℕ) → (code : Codeℕ n m) → encodeℕ n m (decodeℕ n m code) ≡ code
        encodeℕ-decodeℕ zero zero tt = refl
        encodeℕ-decodeℕ (suc n) (suc m) code with decodeℕ n m code | encodeℕ-decodeℕ n m code
        ... | refl | refl = refl

        -- encodeℕ-decodeℕ :(n m : ℕ) → (code : Codeℕ n m) → encodeℕ n m (decodeℕ n m code) ≡ code
        -- encodeℕ-decodeℕ zero zero tt = refl
        -- encodeℕ-decodeℕ (suc n) (suc m) code = -- trans (subst-cong (Codeℕ (suc n)) (decodeℕ n m code)) (encodeℕ-decodeℕ n m code)
        --     begin
        --         encodeℕ (suc n) (suc m) (decodeℕ (suc n) (suc m) code)
        --     ≡⟨⟩
        --         encodeℕ (suc n) (suc m) (cong suc (decodeℕ n m code))
        --     ≡⟨⟩
        --         subst (Codeℕ (suc n)) (cong suc (decodeℕ n m code)) (rℕ (suc n))
        --     ≡⟨ subst-cong (Codeℕ (suc n)) (decodeℕ n m code) ⟩ -- HoTT Book Lemma 2.3.10
        --         subst (λ k → Codeℕ (suc n) (suc k)) (decodeℕ n m code) (rℕ (suc n))
        --     ≡⟨⟩
        --         subst (λ k → Codeℕ n k) (decodeℕ n m code) (rℕ n)
        --     ≡⟨⟩
        --         subst (Codeℕ n) (decodeℕ n m code) (rℕ n)
        --     ≡⟨⟩
        --         encodeℕ n m (decodeℕ n m code)
        --     ≡⟨ encodeℕ-decodeℕ n m code ⟩
        --         code
        --     ∎

Codeℕ-Is-hProp : (n m : ℕ) → Is-hProp (Codeℕ n m)
Codeℕ-Is-hProp zero zero = ⊤-Is-hProp
Codeℕ-Is-hProp (suc n) (suc m) = Codeℕ-Is-hProp n m

ℕ-Is-hSet : Is-hSet ℕ
ℕ-Is-hSet n m = ≅-Is-hProp (ℕ-eq≅Codeℕ n m) (Codeℕ-Is-hProp n m)

Even-Is-hProp : {n : ℕ} → Is-hProp (Even n)
Odd-Is-hProp : {n : ℕ} → Is-hProp (Odd n)
Even-Is-hProp Even.zero Even.zero = refl
Even-Is-hProp (Even.suc p) (Even.suc q) = cong Even.suc (Odd-Is-hProp p q)
Odd-Is-hProp (Odd.suc p) (Odd.suc q) = cong Odd.suc (Even-Is-hProp p q)

--  *-cancel-r m k 1 (trans p (sym q))

Σeven-Is-hProp : {n : ℕ} → Is-hProp (Σ ℕ (λ m → m * 2 ≡ n))
Σeven-Is-hProp (m , refl) (k , q) with *-cancel-r k m 1 q
... | refl = cong (λ p → m , p) (ℕ-Is-hSet (m * 2) (m * 2) refl q)
-- Note if axiom-K is enabled, then the following proof would be accepted without proving ℕ-Is-hSet first:
-- Σeven-Is-hProp (m , refl) (k , q) with *-cancel-r k m 1 q
-- Σeven-Is-hProp (m , refl) (.m , refl) | refl = refl

Σodd-Is-hProp : {n : ℕ} → Is-hProp (Σ ℕ (λ m → 1 + m * 2 ≡ n))
Σodd-Is-hProp (m , refl) (k , q) with *-cancel-r k m 1 (suc-inj q)
... | refl = cong (λ p → m , p) (ℕ-Is-hSet (1 + m * 2) (1 + m * 2) refl q)
-- same as above, ℕ-Is-hSet essentially says axiom-K can be applied to ℕ:
-- Σodd-Is-hProp (m , refl) (.m , refl) | refl = refl

Even≅Σeven : {n : ℕ} → Even n ≅ Σ ℕ (λ m → m * 2 ≡ n)
Even≅Σeven = hProp-iso Even-Is-hProp Σeven-Is-hProp Even-Σeven Σeven-Even

Odd≅Σodd : {n : ℕ} → Odd n ≅ Σ ℕ (λ m → 1 + m * 2 ≡ n)
Odd≅Σodd = hProp-iso Odd-Is-hProp Σodd-Is-hProp Odd-Σodd Σodd-Odd

Even-Σeven′ : {n : ℕ} → Even n → Σ ℕ (λ m → 2 * m ≡ n)
Odd-Σodd′ : {n : ℕ} → Odd n → Σ ℕ (λ m → 2 * m + 1 ≡ n)
Even-Σeven′ Even.zero = zero , refl
Even-Σeven′ (Even.suc x) with Odd-Σodd′ x
... | m , refl = (suc m) , cong suc (sym (trans (+-assoc m (m + 0) 1) (cong₂ _+_ refl (+-comm (m + 0) 1))))
Odd-Σodd′ (Odd.suc x) with Even-Σeven′ x
... | m , refl = m , +-comm (m + (m + 0)) 1

Σeven′-Even : {n : ℕ} → Σ ℕ (λ m → 2 * m ≡ n) → Even n
Σodd′-Odd : {n : ℕ} → Σ ℕ (λ m → 2 * m + 1 ≡ n) → Odd n
Σeven′-Even (zero , refl) = Even.zero
Σeven′-Even (suc m , refl) = Even.suc (subst Odd (trans (+-assoc m (m + 0) 1) (cong₂ _+_ refl (+-comm (m + 0) 1))) (Σodd′-Odd (m , refl)))
Σodd′-Odd (m , refl) = subst Odd (+-comm 1 (m + (m + 0))) (Odd.suc (Σeven′-Even (m , refl)))

Σeven′-Is-hProp : {n : ℕ} → Is-hProp (Σ ℕ (λ m → 2 * m ≡ n))
Σeven′-Is-hProp (m , refl) (k , q) with *-cancel-l k m 1 q
... | refl = cong (λ p → m , p) (ℕ-Is-hSet (2 * m) (2 * m) refl q)
-- Σeven′-Is-hProp (m , refl) (.m , refl) | refl = refl

Σodd′-Is-hProp : {n : ℕ} → Is-hProp (Σ ℕ (λ m → 2 * m + 1 ≡ n))
Σodd′-Is-hProp (m , refl) (k , q) with *-cancel-l k m 1 (+-cancel-r (k + (k + zero)) (m + (m + zero)) 1 q)
... | refl = cong (λ p → m , p) (ℕ-Is-hSet (2 * m + 1) (2 * m + 1) refl q)
-- Σodd′-Is-hProp (m , refl) (.m , refl) | refl = refl

Even≅Σeven′ : {n : ℕ} → Even n ≅ Σ ℕ (λ m → 2 * m ≡ n)
Even≅Σeven′ = hProp-iso Even-Is-hProp Σeven′-Is-hProp Even-Σeven′ Σeven′-Even

Odd≅Σodd′ : {n : ℕ} → Odd n ≅ Σ ℕ (λ m → 2 * m + 1 ≡ n)
Odd≅Σodd′ = hProp-iso Odd-Is-hProp Σodd′-Is-hProp Odd-Σodd′ Σodd′-Odd

open _≤_

≤-Σ≤ : {n m : ℕ} → n ≤ m → Σ ℕ (λ k → k + n ≡ m)
≤-Σ≤ {n} {m} z≤n = m , +-identityʳ m
≤-Σ≤ {n} {m} (s≤s {m′} p) with ≤-Σ≤ p
... | k , refl = k , +-suc k m′

Σ≤-≤ : {n m : ℕ} → Σ ℕ (λ k → k + n ≡ m) → n ≤ m
Σ≤-≤ (zero , refl) = ≤-reflexive refl
Σ≤-≤ {n} {m} (suc k , refl) = +-monoˡ-≤ n z≤n

≤-Is-hProp : {n m : ℕ} → Is-hProp (n ≤ m)
≤-Is-hProp z≤n z≤n = refl
≤-Is-hProp (s≤s p) (s≤s q) = cong s≤s (≤-Is-hProp p q)

Σ≤-Is-hProp : {n m : ℕ} → Is-hProp (Σ ℕ (λ k → k + n ≡ m))
Σ≤-Is-hProp {n} {m} (k , refl) (l , q) with +-cancel-r l k n q
... | refl = cong (λ p → k , p) (ℕ-Is-hSet (k + n) (k + n) refl q)
-- Σ≤-Is-hProp {n} {.(k + n)} (k , refl) (.k , refl) | refl = refl

≤≅Σ≤ : {n m : ℕ} → n ≤ m ≅ Σ ℕ (λ k → k + n ≡ m)
≤≅Σ≤ = hProp-iso ≤-Is-hProp Σ≤-Is-hProp ≤-Σ≤ Σ≤-≤

¬Σ≅Π¬ : {A : Set i} → {B : A → Set j}
    → ¬ Σ A B ≅ Π A (¬_ ∘ B)
¬Σ≅Π¬ .to f x y = f (x , y)
¬Σ≅Π¬ .from g (x , y) = g x y
¬Σ≅Π¬ .from∘to f = extensionality (λ { (x , y) → refl })
¬Σ≅Π¬ .to∘from g = refl

Σ¬→¬Π : {A : Set i} → {B : A → Set j}
    → Σ A (¬_ ∘ B) → ¬ Π A B
Σ¬→¬Π (x , f) g = f (g x)

-- The converse cannot be disproved, if the converse can be disproved, then it must hold in all Heyting models,
-- in particular all Boolean models, hence the double negation translation of the converse must not hold as well,
-- but since the converse can be classically proved, its double negation translation can be constructively proved,
-- as shown below in ¬Π¬¬→¬¬Σ¬, furthermore, the converse is logically equivalent to excluded middle, see NotPiAsSigma
-- in Negation.agda

¬-Is-hProp : {A : Set i} → Is-hProp (¬ A)
¬-Is-hProp f g = extensionality λ x → ⊥-elim (f x)

¬¬¬≅¬ : {A : Set i} → ¬ ¬ ¬ A ≅ ¬ A
¬¬¬≅¬ = record {
        to = λ f x → f λ g → g x;
        from = λ f g → g f;
        from∘to = λ f → extensionality λ g → ⊥-elim (f g);
        to∘from = λ f → refl
    }

¬Π¬¬→¬¬Σ¬¬¬ : {A : Set i} → {B : A → Set j}
    → ¬ Π A (¬_ ∘ ¬_ ∘ B) → ¬ ¬ Σ A (¬_ ∘ ¬_ ∘ ¬_ ∘ B)
¬Π¬¬→¬¬Σ¬¬¬ f g = f (λ x h → g (x , λ j → j h))

¬Π¬¬→¬¬Σ¬ : {A : Set i} → {B : A → Set j}
    → ¬ Π A (¬_ ∘ ¬_ ∘ B) → ¬ ¬ Σ A (¬_ ∘ B)
¬Π¬¬→¬¬Σ¬ f g = f (λ x h → g (x , h))

open import plfa.part1.Induction using (Bin; toBin; fromBin; fromBin-toBin)
open import plfa.part1.Relations using (One; Can; can-toBin; can-toBin-fromBin)

open Bin
open One
open Can

One-Is-hProp : {x : Bin} → Is-hProp (One x)
One-Is-hProp justI justI = refl
One-Is-hProp (caseO p) (caseO q) = cong caseO (One-Is-hProp p q)
One-Is-hProp (caseI p) (caseI q) = cong caseI (One-Is-hProp p q)

Can-Is-hProp : {x : Bin} → Is-hProp (Can x)
Can-Is-hProp justO justO = refl
Can-Is-hProp justO (fromOne (caseO ()))
Can-Is-hProp (fromOne (caseO ())) justO
Can-Is-hProp (fromOne justI) (fromOne justI) = refl
Can-Is-hProp (fromOne (caseO p)) (fromOne (caseO q)) = cong fromOne (One-Is-hProp (caseO p) (caseO q))
Can-Is-hProp (fromOne (caseI p)) (fromOne (caseI q)) = cong fromOne (One-Is-hProp (caseI p) (caseI q))

ℕ≅ΣBinCan : ℕ ≅ Σ Bin Can
ℕ≅ΣBinCan .to n = toBin n , can-toBin n
ℕ≅ΣBinCan .from (x , p) = fromBin x
ℕ≅ΣBinCan .from∘to = fromBin-toBin
ℕ≅ΣBinCan .to∘from (x , p) = Σ-eq-iso .from (can-toBin-fromBin x p , Can-Is-hProp (subst Can (can-toBin-fromBin x p) (can-toBin (fromBin x))) p)

-- Bonus: use encode-decode to prove Bin-Is-hSet

CodeBin : Bin → Bin → Set
CodeBin ⟨⟩ ⟨⟩ = ⊤
CodeBin ⟨⟩ (y O) = ⊥
CodeBin ⟨⟩ (y I) = ⊥
CodeBin (x O) ⟨⟩ = ⊥
CodeBin (x O) (y O) = CodeBin x y
CodeBin (x O) (y I) = ⊥
CodeBin (x I) ⟨⟩ = ⊥
CodeBin (x I) (y O) = ⊥
CodeBin (x I) (y I) = CodeBin x y

rBin : (x : Bin) → CodeBin x x
rBin ⟨⟩ = tt
rBin (x O) = rBin x
rBin (x I) = rBin x

Bin-eq≅CodeBin : (x y : Bin) → x ≡ y ≅ CodeBin x y
Bin-eq≅CodeBin x y = record {
        to = encodeBin x y;
        from = decodeBin x y;
        from∘to = decodeBin-encodeBin x y;
        to∘from = encodeBin-decodeBin x y
    } where
        encodeBin : (x y : Bin) → x ≡ y → CodeBin x y
        encodeBin x .x refl = rBin x
        -- encodeBin x y p = subst (CodeBin x) p (rBin x)

        decodeBin : (x y : Bin) → CodeBin x y → x ≡ y
        decodeBin ⟨⟩ ⟨⟩ tt = refl
        decodeBin (x O) (y O) code = cong _O (decodeBin x y code)
        decodeBin (x I) (y I) code = cong _I (decodeBin x y code)

        decodeBin-encodeBin : (x y : Bin) → (p : x ≡ y) → decodeBin x y (encodeBin x y p) ≡ p
        decodeBin-encodeBin ⟨⟩ .⟨⟩ refl = refl
        decodeBin-encodeBin (x O) .(x O) refl = cong (cong _O) (decodeBin-encodeBin x x refl)
        decodeBin-encodeBin (x I) .(x I) refl = cong (cong _I) (decodeBin-encodeBin x x refl)

        encodeBin-decodeBin : (x y : Bin) → (code : CodeBin x y) → encodeBin x y (decodeBin x y code) ≡ code
        encodeBin-decodeBin ⟨⟩ ⟨⟩ tt = refl
        encodeBin-decodeBin (x O) (y O) code with decodeBin x y code | encodeBin-decodeBin x y code
        ... | refl | refl = refl
        -- encodeBin-decodeBin (x O) (y O) code = trans (subst-cong (CodeBin (x O)) (decodeBin x y code)) (encodeBin-decodeBin x y code)
        encodeBin-decodeBin (x I) (y I) code with decodeBin x y code | encodeBin-decodeBin x y code
        ... | refl | refl = refl
        -- encodeBin-decodeBin (x I) (y I) code = trans (subst-cong (CodeBin (x I)) (decodeBin x y code)) (encodeBin-decodeBin x y code)

CodeBin-Is-hProp : (x y : Bin) → Is-hProp (CodeBin x y)
CodeBin-Is-hProp ⟨⟩ ⟨⟩ = ⊤-Is-hProp
CodeBin-Is-hProp (x O) (y O) = CodeBin-Is-hProp x y
CodeBin-Is-hProp (x I) (y I) = CodeBin-Is-hProp x y

Bin-Is-hSet : Is-hSet Bin
Bin-Is-hSet x y = ≅-Is-hProp (Bin-eq≅CodeBin x y) (CodeBin-Is-hProp x y)
-- Bin-Is-hSet ⟨⟩ ⟨⟩ refl refl = refl
-- Bin-Is-hSet (x O) (.x O) refl refl = refl
-- Bin-Is-hSet (x I) (.x I) refl refl = refl

-- Binary naturals without Can:

data Pos : Set where
    p1 : Pos
    _b0 : Pos → Pos
    _b1 : Pos → Pos

data Bℕ : Set where
    bzero : Bℕ
    pos : Pos → Bℕ

sucPos : Pos → Pos
sucPos p1 = p1 b0
sucPos (x b0) = x b1
sucPos (x b1) = (sucPos x) b0

sucBℕ : Bℕ → Bℕ
sucBℕ bzero = pos p1
sucBℕ (pos x) = pos (sucPos x)

toBℕ : ℕ → Bℕ
toBℕ zero = bzero
toBℕ (suc n) = sucBℕ (toBℕ n)

fromBℕ : Bℕ → ℕ
fromBℕ bzero = 0
fromBℕ (pos p1) = 1
fromBℕ (pos (x b0)) = fromBℕ (pos x) + fromBℕ (pos x)
fromBℕ (pos (x b1)) = suc (fromBℕ (pos x) + fromBℕ (pos x))

fromBℕ∘sucBℕ : (x : Bℕ) → fromBℕ (sucBℕ x) ≡ suc (fromBℕ x)
fromBℕ∘sucBℕ bzero = refl
fromBℕ∘sucBℕ (pos p1) = refl
fromBℕ∘sucBℕ (pos (x b0)) = refl
fromBℕ∘sucBℕ (pos (x b1)) =
    trans
        (cong₂ _+_ (fromBℕ∘sucBℕ (pos x)) (fromBℕ∘sucBℕ (pos x)))
        (+-suc (suc (fromBℕ (pos x))) (fromBℕ (pos x)))

fromBℕ∘toBℕ : (n : ℕ) → fromBℕ (toBℕ n) ≡ n
fromBℕ∘toBℕ zero = refl
fromBℕ∘toBℕ (suc n) =
    trans
        (fromBℕ∘sucBℕ (toBℕ n))
        (cong suc (fromBℕ∘toBℕ n))

_+Pos_ : Pos → Pos → Pos
p1 +Pos p1 = p1 b0
p1 +Pos (y b0) = y b1
p1 +Pos (y b1) = (sucPos y) b0
(x b0) +Pos p1 = x b1
(x b0) +Pos (y b0) = (x +Pos y) b0
(x b0) +Pos (y b1) = (x +Pos y) b1
(x b1) +Pos p1 = (sucPos x) b0
(x b1) +Pos (y b0) = (x +Pos y) b1
(x b1) +Pos (y b1) = (sucPos (x +Pos y)) b0

_+Bℕ_ : Bℕ → Bℕ → Bℕ
bzero +Bℕ y = y
pos x +Bℕ bzero = pos x
pos x +Bℕ pos y = pos (x +Pos y)

_ : (toBℕ 16) +Bℕ (toBℕ 9) ≡ toBℕ 25
_ = refl

sucPos≡p1+Pos : (x : Pos) → sucPos x ≡ p1 +Pos x
sucPos≡p1+Pos p1 = refl
sucPos≡p1+Pos (x b0) = refl
sucPos≡p1+Pos (x b1) = refl

sucPos∘+Pos : (x y : Pos) → sucPos (x +Pos y) ≡ (sucPos x) +Pos y
sucPos∘+Pos p1 p1 = refl
sucPos∘+Pos p1 (y b0) = cong _b0 (sucPos≡p1+Pos y)
sucPos∘+Pos p1 (y b1) = cong _b1 (sucPos≡p1+Pos y)
sucPos∘+Pos (x b0) p1 = refl
sucPos∘+Pos (x b0) (y b0) = refl
sucPos∘+Pos (x b0) (y b1) = refl
sucPos∘+Pos (x b1) p1 = refl
sucPos∘+Pos (x b1) (y b0) = cong _b0 (sucPos∘+Pos x y)
sucPos∘+Pos (x b1) (y b1) = cong _b1 (sucPos∘+Pos x y)

sucBℕ∘+Bℕ : (x y : Bℕ) → sucBℕ (x +Bℕ y) ≡ (sucBℕ x) +Bℕ y
sucBℕ∘+Bℕ bzero bzero = refl
sucBℕ∘+Bℕ bzero (pos y) = cong pos (sucPos≡p1+Pos y)
sucBℕ∘+Bℕ (pos x) bzero = refl
sucBℕ∘+Bℕ (pos x) (pos y) = cong pos (sucPos∘+Pos x y)

toBℕ∘+ : (n m : ℕ) → toBℕ (n + m) ≡ (toBℕ n) +Bℕ (toBℕ m)
toBℕ∘+ zero m = refl
toBℕ∘+ (suc n) m =
    trans
        (cong sucBℕ (toBℕ∘+ n m))
        (sucBℕ∘+Bℕ (toBℕ n) (toBℕ m))

doublePos : (x : Pos) → x +Pos x ≡ x b0
doublePos p1 = refl
doublePos (x b0) = cong _b0 (doublePos x)
doublePos (x b1) = cong _b0 (cong sucPos (doublePos x))

toBℕ∘fromBℕ : (x : Bℕ) → toBℕ (fromBℕ x) ≡ x
toBℕ∘fromBℕ bzero = refl
toBℕ∘fromBℕ (pos p1) = refl
toBℕ∘fromBℕ (pos (x b0)) =
    trans
        (toBℕ∘+ (fromBℕ (pos x)) (fromBℕ (pos x)))
        (trans
            (cong₂ _+Bℕ_ (toBℕ∘fromBℕ (pos x)) (toBℕ∘fromBℕ (pos x)))
            (cong pos (doublePos x)))
toBℕ∘fromBℕ (pos (x b1)) =
    trans
        (cong sucBℕ (toBℕ∘+ (fromBℕ (pos x)) (fromBℕ (pos x))))
        (trans
            (cong sucBℕ (cong₂ _+Bℕ_ (toBℕ∘fromBℕ (pos x)) (toBℕ∘fromBℕ (pos x))))
            (cong pos (cong sucPos (doublePos x))))

ℕ≅Bℕ : ℕ ≅ Bℕ
ℕ≅Bℕ .to = toBℕ
ℕ≅Bℕ .from = fromBℕ
ℕ≅Bℕ .from∘to = fromBℕ∘toBℕ
ℕ≅Bℕ .to∘from = toBℕ∘fromBℕ

-- Binary naturals without Pos and Can

data ℕb : Set where
    0b : ℕb
    1+2*_ : ℕb → ℕb
    2+2*_ : ℕb → ℕb

1b : ℕb
1b = 1+2* 0b

2b : ℕb
2b = 2+2* 0b

3b : ℕb
3b = 1+2* 1b

4b : ℕb
4b = 2+2* 1b

-- 0 0 0
-- 1 1 1
-- 2 10 2
-- 3 11 11
-- 4 100 21
-- 5 101 12
-- 6 110 22
-- 7 111 111
-- 8 1000 211
-- 9 1001 121
-- 10 1010 221
-- 11 1011 112
-- 12 1100 212
-- 13 1101 122
-- 14 1110 222
-- 15 1111 1111

sucℕb : ℕb → ℕb
sucℕb 0b = 1b
sucℕb (1+2* x) = 2+2* x
sucℕb (2+2* x) = 1+2* (sucℕb x)

toℕb : ℕ → ℕb
toℕb zero = 0b
toℕb (suc n) = sucℕb (toℕb n)

fromℕb : ℕb → ℕ
fromℕb 0b = 0
fromℕb (1+2* x) = 1 + fromℕb x + fromℕb x
fromℕb (2+2* x) = 2 + fromℕb x + fromℕb x

fromℕb∘sucℕb : (x : ℕb) → fromℕb (sucℕb x) ≡ suc (fromℕb x)
fromℕb∘sucℕb 0b = refl
fromℕb∘sucℕb (1+2* x) = refl
fromℕb∘sucℕb (2+2* x) =
    begin
        suc (fromℕb (sucℕb x) + fromℕb (sucℕb x))
    ≡⟨ cong suc (cong₂ _+_ (fromℕb∘sucℕb x) (fromℕb∘sucℕb x)) ⟩
        suc (suc (fromℕb x) + suc (fromℕb x))
    ≡⟨ cong (suc ∘ suc) (+-suc (fromℕb x) (fromℕb x)) ⟩
        suc (suc (suc (fromℕb x + fromℕb x)))
    ∎

fromℕb∘toℕb : (n : ℕ) → fromℕb (toℕb n) ≡ n
fromℕb∘toℕb zero = refl
fromℕb∘toℕb (suc n) = trans (fromℕb∘sucℕb (toℕb n)) (cong suc (fromℕb∘toℕb n))

_+ℕb_ : ℕb → ℕb → ℕb
0b +ℕb y = y
(1+2* x) +ℕb 0b = 1+2* x
(1+2* x) +ℕb (1+2* y) = 2+2* (x +ℕb y)
(1+2* x) +ℕb (2+2* y) = 1+2* (sucℕb (x +ℕb y))
(2+2* x) +ℕb 0b = 2+2* x
(2+2* x) +ℕb (1+2* y) = 1+2* (sucℕb (x +ℕb y))
(2+2* x) +ℕb (2+2* y) = 2+2* (sucℕb (x +ℕb y))

_ : fromℕb ((toℕb 123) +ℕb (toℕb 321)) ≡ 444
_ = refl

sucℕb≡1b+ℕb : (x : ℕb) → sucℕb x ≡ 1b +ℕb x
sucℕb≡1b+ℕb 0b = refl
sucℕb≡1b+ℕb (1+2* x) = refl
sucℕb≡1b+ℕb (2+2* x) = refl

sucℕb∘+ℕb : (x y : ℕb) → sucℕb (x +ℕb y) ≡ (sucℕb x) +ℕb y
sucℕb∘+ℕb 0b y = sucℕb≡1b+ℕb y
sucℕb∘+ℕb (1+2* x) 0b = refl
sucℕb∘+ℕb (1+2* x) (1+2* y) = refl
sucℕb∘+ℕb (1+2* x) (2+2* y) = refl
sucℕb∘+ℕb (2+2* x) 0b = refl
sucℕb∘+ℕb (2+2* x) (1+2* y) = cong 2+2*_ (sucℕb∘+ℕb x y)
sucℕb∘+ℕb (2+2* x) (2+2* y) = cong (1+2*_ ∘ sucℕb) (sucℕb∘+ℕb x y)

toℕb∘+ : (n m : ℕ) → toℕb (n + m) ≡ (toℕb n) +ℕb (toℕb m)
toℕb∘+ zero m = refl
toℕb∘+ (suc n) m = trans (cong sucℕb (toℕb∘+ n m)) (sucℕb∘+ℕb (toℕb n) (toℕb m))

double∘sucℕb : (x : ℕb) → sucℕb (x +ℕb x) ≡ 1+2* x
double∘sucℕb 0b = refl
double∘sucℕb (1+2* x) = cong 1+2*_ (double∘sucℕb x)
double∘sucℕb (2+2* x) = cong (1+2*_ ∘ sucℕb) (double∘sucℕb x)

toℕb∘fromℕb : (x : ℕb) → toℕb (fromℕb x) ≡ x
toℕb∘fromℕb 0b = refl
toℕb∘fromℕb (1+2* x) =
    begin
        sucℕb (toℕb (fromℕb x + fromℕb x))
    ≡⟨ cong sucℕb (toℕb∘+ (fromℕb x) (fromℕb x)) ⟩
        sucℕb (toℕb (fromℕb x) +ℕb toℕb (fromℕb x))
    ≡⟨ cong sucℕb (cong₂ _+ℕb_ (toℕb∘fromℕb x) (toℕb∘fromℕb x)) ⟩
        sucℕb (x +ℕb x)
    ≡⟨ double∘sucℕb x ⟩
        1+2* x
    ∎
toℕb∘fromℕb (2+2* x) =
    begin
        toℕb (fromℕb (2+2* x))
    ≡⟨ cong (sucℕb ∘ sucℕb) (toℕb∘+ (fromℕb x) (fromℕb x)) ⟩
        sucℕb (sucℕb (toℕb (fromℕb x) +ℕb toℕb (fromℕb x)))
    ≡⟨ cong (sucℕb ∘ sucℕb) (cong₂ _+ℕb_ (toℕb∘fromℕb x) (toℕb∘fromℕb x)) ⟩
        sucℕb (sucℕb (x +ℕb x))
    ≡⟨ cong sucℕb (double∘sucℕb x) ⟩
        (2+2* x)
    ∎

ℕ≅ℕb : ℕ ≅ ℕb
ℕ≅ℕb .to = toℕb
ℕ≅ℕb .from = fromℕb
ℕ≅ℕb .from∘to = fromℕb∘toℕb
ℕ≅ℕb .to∘from = toℕb∘fromℕb

-- import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

-- Bonus: use encode-decode to prove Tree-Is-hSet

data Tree : Set where
    leaf : Tree
    node : Tree → Tree → Tree

CodeTree : Tree → Tree → Set
CodeTree leaf leaf = ⊤
CodeTree leaf (node tree₂₁ tree₂₂) = ⊥
CodeTree (node tree₁₁ tree₁₂) leaf = ⊥
CodeTree (node tree₁₁ tree₁₂) (node tree₂₁ tree₂₂) = CodeTree tree₁₁ tree₂₁ × CodeTree tree₁₂ tree₂₂

rTree : (tree : Tree) → CodeTree tree tree
rTree leaf = tt
rTree (node tree₁ tree₂) = (rTree tree₁) , (rTree tree₂)

Tree-eq≅CodeTree : (tree₁ tree₂ : Tree) → tree₁ ≡ tree₂ ≅ CodeTree tree₁ tree₂
Tree-eq≅CodeTree tree₁ tree₂ = record {
        to = encodeTree tree₁ tree₂;
        from = decodeTree tree₁ tree₂;
        from∘to = decodeTree-encodeTree tree₁ tree₂;
        to∘from = encodeTree-decodeTree tree₁ tree₂
    } where
        encodeTree : (tree₁ tree₂ : Tree) → tree₁ ≡ tree₂ → CodeTree tree₁ tree₂
        encodeTree tree₁ .tree₁ refl = rTree tree₁
        -- encodeTree tree₁ tree₂ p = subst (CodeTree tree₁) p (rTree tree₁)

        decodeTree : (tree₁ tree₂ : Tree) → CodeTree tree₁ tree₂ → tree₁ ≡ tree₂
        decodeTree leaf leaf tt = refl
        decodeTree (node tree₁₁ tree₁₂) (node tree₂₁ tree₂₂) (code₁ , code₂) = cong₂ node (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂)

        decodeTree-encodeTree : (tree₁ tree₂ : Tree) → (p : tree₁ ≡ tree₂) → decodeTree tree₁ tree₂ (encodeTree tree₁ tree₂ p) ≡ p
        decodeTree-encodeTree leaf .leaf refl = refl
        decodeTree-encodeTree (node tree₁₁ tree₁₂) .(node tree₁₁ tree₁₂) refl = cong₂ (cong₂ node) (decodeTree-encodeTree tree₁₁ tree₁₁ refl) (decodeTree-encodeTree tree₁₂ tree₁₂ refl)
            -- begin
            --     decodeTree (node tree₁₁ tree₁₂) (node tree₁₁ tree₁₂) (encodeTree (node tree₁₁ tree₁₂) (node tree₁₁ tree₁₂) refl)
            -- ≡⟨⟩
            --     decodeTree (node tree₁₁ tree₁₂) (node tree₁₁ tree₁₂) (rTree tree₁₁ , rTree tree₁₂)
            -- ≡⟨⟩
            --     cong₂ node (decodeTree tree₁₁ tree₁₁ (rTree tree₁₁)) (decodeTree tree₁₂ tree₁₂ (rTree tree₁₂))
            -- ≡⟨⟩
            --     cong₂ node (decodeTree tree₁₁ tree₁₁ (encodeTree tree₁₁ tree₁₁ refl)) (decodeTree tree₁₂ tree₁₂ (encodeTree tree₁₂ tree₁₂ refl))
            -- ≡⟨ cong₂ (cong₂ node) (decodeTree-encodeTree tree₁₁ tree₁₁ refl) (decodeTree-encodeTree tree₁₂ tree₁₂ refl) ⟩
            --     cong₂ node refl refl
            -- ≡⟨⟩
            --     refl
            -- ∎

        encodeTree-decodeTree : (tree₁ tree₂ : Tree) → (code : CodeTree tree₁ tree₂) → encodeTree tree₁ tree₂ (decodeTree tree₁ tree₂ code) ≡ code
        encodeTree-decodeTree leaf leaf tt = refl
        encodeTree-decodeTree (node tree₁₁ tree₁₂) (node tree₂₁ tree₂₂) (code₁ , code₂)
            with
                decodeTree tree₁₁ tree₂₁ code₁ |
                decodeTree tree₁₂ tree₂₂ code₂ |
                encodeTree-decodeTree tree₁₁ tree₂₁ code₁ |
                encodeTree-decodeTree tree₁₂ tree₂₂ code₂
        ... | refl | refl | refl | refl = refl
        
        -- encodeTree-decodeTree : (tree₁ tree₂ : Tree) → (code : CodeTree tree₁ tree₂) → encodeTree tree₁ tree₂ (decodeTree tree₁ tree₂ code) ≡ code
        -- encodeTree-decodeTree leaf leaf tt = refl
        -- encodeTree-decodeTree (node tree₁₁ tree₁₂) (node tree₂₁ tree₂₂) (code₁ , code₂) =
        --     begin
        --         encodeTree (node tree₁₁ tree₁₂) (node tree₂₁ tree₂₂) (decodeTree (node tree₁₁ tree₁₂) (node tree₂₁ tree₂₂) (code₁ , code₂))
        --     ≡⟨⟩
        --         encodeTree (node tree₁₁ tree₁₂) (node tree₂₁ tree₂₂) (cong₂ node (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂))
        --     ≡⟨⟩
        --         subst (CodeTree (node tree₁₁ tree₁₂)) (cong₂ node (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂)) (rTree tree₁₁ , rTree tree₁₂)
        --     ≡⟨ subst-cong₂ (CodeTree (node tree₁₁ tree₁₂)) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) ⟩
        --         subst₂ (λ tree₂₁ tree₂₂ → CodeTree (node tree₁₁ tree₁₂) (node tree₂₁ tree₂₂)) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) (rTree tree₁₁ , rTree tree₁₂)
        --     ≡⟨⟩
        --         subst₂ (λ tree₂₁ tree₂₂ → CodeTree tree₁₁ tree₂₁ × CodeTree tree₁₂ tree₂₂) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) (rTree tree₁₁ , rTree tree₁₂)
        --     ≡⟨ subst₂≡subst×subst (CodeTree tree₁₁) (CodeTree tree₁₂) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) ⟩
        --         subst (CodeTree tree₁₁) (decodeTree tree₁₁ tree₂₁ code₁) (rTree tree₁₁) , subst (CodeTree tree₁₂) (decodeTree tree₁₂ tree₂₂ code₂) (rTree tree₁₂)
        --     ≡⟨⟩
        --         encodeTree tree₁₁ tree₂₁ (decodeTree tree₁₁ tree₂₁ code₁) , encodeTree tree₁₂ tree₂₂ (decodeTree tree₁₂ tree₂₂ code₂)
        --     ≡⟨ cong₂ _,_ (encodeTree-decodeTree tree₁₁ tree₂₁ code₁) (encodeTree-decodeTree tree₁₂ tree₂₂ code₂) ⟩
        --         code₁ , code₂
        --     ∎

CodeTree-Is-hProp : (tree₁ tree₂ : Tree) → Is-hProp (CodeTree tree₁ tree₂)
CodeTree-Is-hProp leaf leaf = ⊤-Is-hProp
CodeTree-Is-hProp (node tree₁₁ tree₁₂) (node tree₂₁ tree₂₂) = ×-Is-hProp (CodeTree-Is-hProp tree₁₁ tree₂₁) (CodeTree-Is-hProp tree₁₂ tree₂₂)

Tree-Is-hSet : Is-hSet Tree
Tree-Is-hSet tree₁ tree₂ = ≅-Is-hProp (Tree-eq≅CodeTree tree₁ tree₂) (CodeTree-Is-hProp tree₁ tree₂)
  