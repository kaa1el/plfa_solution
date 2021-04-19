{-# OPTIONS --without-K #-}

module plfa.part1.Quantifiers where

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
open import Function using (_∘_)

open import plfa.part1.Induction using (suc-inj; +-cancel-r; *-cancel-r; *-cancel-l)
open import plfa.part1.Relations using (Even; Odd)
open import plfa.part1.Isomorphism using (_≅_; extensionality; Π-extensionality)
open import plfa.part1.Connectives using (Color)

Π : (A : Set) → (B : A → Set) → Set
Π A B = (x : A) → B x

η-Π : {A : Set} → {B : A → Set}
    → (f : Π A B)
    → (λ x → f x) ≡ f
η-Π f = refl

Π-elim : {A : Set} → {B : A → Set}
    → (f : Π A B)
    → (x : A)
    → B x
Π-elim f x = f x

open _≅_

Π-distrib-× : {A : Set} → {B C : A → Set}
    → Π A (λ x → B x × C x) ≅ Π A B × Π A C
Π-distrib-× .to f = (λ x → f x .proj₁) , (λ x → f x .proj₂)
Π-distrib-× .from (g , h) = λ x → (g x) , (h x)
Π-distrib-× .from∘to _ = refl
Π-distrib-× .to∘from _ = refl

⊎Π-implies-Π⊎ : {A : Set} → {B C : A → Set}
    → Π A B ⊎ Π A C → Π A (λ x → B x ⊎ C x)
⊎Π-implies-Π⊎ (inj₁ f) x = inj₁ (f x)
⊎Π-implies-Π⊎ (inj₂ g) x = inj₂ (g x)

-- The converse does not hold, consider:
-- A = Bool
-- B false = Empty, B true = Unit
-- C false = Unit, C true = Empty

open Color

Π-× : (B : Color → Set)
    → Π Color B ≅ B red × B green × B blue
Π-× B .to f = f red , f green , f blue
Π-× B .from (r , g , b) red = r
Π-× B .from (r , g , b) green = g
Π-× B .from (r , g , b) blue = b
Π-× B .from∘to f = Π-extensionality λ { red → refl; green → refl; blue → refl }
Π-× B .to∘from _ = refl

Σ-elim : {A : Set} → {B : A → Set} -> {C : Set}
    → ((x : A) → B x → C)
    → Σ A B → C -- this is just a special case of the dependent curry/uncurry
Σ-elim f (x , y) = f x y

ΠΣ-currying : {A : Set} → {B : A → Set} -> {C : Set}
    → ((x : A) → B x → C) ≅ (Σ A B → C) -- this is just a special case of the dependent curry/uncurry
ΠΣ-currying .to f (x , y) = f x y
ΠΣ-currying .from g x y = g (x , y)
ΠΣ-currying .from∘to f = refl
ΠΣ-currying .to∘from g = extensionality λ { (x , y) → refl }

currying : {A : Set} → {B : A → Set} -> {C : (x : A) → B x → Set}
    → ((x : A) → (y : B x) → C x y) ≅ ((w : Σ A B) → C (proj₁ w) (proj₂ w)) -- this is the dependent curry/uncurry
currying .to f (x , y) = f x y
currying .from g x y = g (x , y)
currying .from∘to f = refl
currying .to∘from g = Π-extensionality λ { (x , y) → refl }

Σ-distrib-⊎ : {A : Set} → {B C : A → Set}
    → Σ A (λ x → B x ⊎ C x) ≅ Σ A B ⊎ Σ A C
Σ-distrib-⊎ .to (x , inj₁ y) = inj₁ (x , y)
Σ-distrib-⊎ .to (x , inj₂ z) = inj₂ (x , z)
Σ-distrib-⊎ .from (inj₁ (x , y)) = x , inj₁ y
Σ-distrib-⊎ .from (inj₂ (x , z)) = x , inj₂ z
Σ-distrib-⊎ .from∘to (x , inj₁ y) = refl
Σ-distrib-⊎ .from∘to (x , inj₂ z) = refl
Σ-distrib-⊎ .to∘from (inj₁ (x , y)) = refl
Σ-distrib-⊎ .to∘from (inj₂ (x , z)) = refl

Σ×-implies-xΣ : {A : Set} → {B C : A → Set}
    → Σ A (λ x → B x × C x) → (Σ A B) × (Σ A C)
Σ×-implies-xΣ (x , y , z) = (x , y) , (x , z)

-- The converse does not hold, consider:
-- A = Bool
-- B false = Empty, B true = Unit
-- C false = Unit, C true = Empty

Σ-⊎ : (B : Color → Set)
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

Is-Contractible : Set → Set
Is-Contractible A = Σ A (λ x → (y : A) → x ≡ y)

Is-hProp : Set → Set
Is-hProp A = (x y : A) → x ≡ y

Is-hSet : Set → Set
Is-hSet A = (x y : A) → Is-hProp (x ≡ y)

×-Is-hProp : (A B : Set) → Is-hProp A → Is-hProp B → Is-hProp (A × B)
×-Is-hProp A B p q (x1 , y1) (x2 , y2) = cong₂ _,_ (p x1 x2) (q y1 y2)

→-Is-hProp : (A B : Set) → Is-hProp B → Is-hProp (A → B)
→-Is-hProp A B q f g = extensionality λ x → q (f x) (g x)

Π-Is-hProp : (A : Set) → (P : A → Set) → ((x : A) → Is-hProp (P x)) → Is-hProp ((x : A) → P x)
Π-Is-hProp A P q f g = Π-extensionality (λ x → q x (f x) (g x))

code : ℕ → ℕ → Set
code zero zero = ⊤
code zero (suc m) = ⊥
code (suc n) zero = ⊥
code (suc n) (suc m) = code n m

r : (n : ℕ) → code n n
r zero = tt
r (suc n) = r n

encode : (n m : ℕ) → n ≡ m → code n m
encode n m p = subst (code n) p (r n) -- encode n n refl ≡ r n

decode : (n m : ℕ) → code n m → n ≡ m
decode zero zero tt = refl
decode (suc n) (suc m) c = cong suc (decode n m c)

subst-cong : {A B : Set}
    → {f : A → B}
    → (P : B → Set)
    → {x y : A}
    → {u : P (f x)}
    → (e : x ≡ y)
    → subst P (cong f e) u ≡ subst (λ x → P (f x)) e u -- HoTT Book Lemma 2.3.10
subst-cong P refl = refl

ℕ-eq≅code : (n m : ℕ) → n ≡ m ≅ code n m -- HoTT Book Theorem 2.13.1
ℕ-eq≅code n m .to = encode n m
ℕ-eq≅code n m .from = decode n m
ℕ-eq≅code zero .zero .from∘to refl = refl
ℕ-eq≅code (suc n) .(suc n) .from∘to refl = cong (cong suc) (ℕ-eq≅code n n .from∘to refl)
ℕ-eq≅code zero zero .to∘from tt = refl
ℕ-eq≅code (suc n) (suc m) .to∘from c = -- trans (subst-cong (code (suc n)) (decode n m c)) (ℕ-eq≅code n m .to∘from c)
    begin
        encode (suc n) (suc m) (decode (suc n) (suc m) c)
    ≡⟨⟩
        encode (suc n) (suc m) (cong suc (decode n m c))
    ≡⟨⟩
        subst (code (suc n)) (cong suc (decode n m c)) (r (suc n))
    ≡⟨ subst-cong (code (suc n)) (decode n m c) ⟩ -- HoTT Book Lemma 2.3.10
        subst (λ k → code (suc n) (suc k)) (decode n m c) (r (suc n))
    ≡⟨⟩
        subst (λ k → code n k) (decode n m c) (r n)
    ≡⟨⟩
        subst (code n) (decode n m c) (r n)
    ≡⟨⟩
        encode n m (decode n m c)
    ≡⟨ ℕ-eq≅code n m .to∘from c ⟩
        c
    ∎

Unit-Is-hProp : Is-hProp ⊤
Unit-Is-hProp tt tt = refl

Empty-Is-hProp : Is-hProp ⊥
Empty-Is-hProp () ()

code-Is-hProp : (n m : ℕ) → Is-hProp (code n m)
code-Is-hProp zero zero = Unit-Is-hProp
code-Is-hProp (suc n) (suc m) = code-Is-hProp n m

≅-Is-hProp : {A B : Set} → A ≅ B → Is-hProp B → Is-hProp A
≅-Is-hProp iso p x y =
    begin
        x
    ≡⟨ sym (iso .from∘to x) ⟩
        iso .from (iso .to x)
    ≡⟨ cong (iso .from) (p (iso .to x) (iso .to y)) ⟩
        iso .from (iso .to y)
    ≡⟨ iso .from∘to y ⟩
        y
    ∎

ℕ-Is-hSet : Is-hSet ℕ
ℕ-Is-hSet n m = ≅-Is-hProp (ℕ-eq≅code n m) (code-Is-hProp n m)

hProp-iso : {A B : Set}
    → Is-hProp A → Is-hProp B
    → (A → B) → (B → A) -- we can also package these conditions into a record type (uncurrying)
    → A ≅ B
hProp-iso p q f g .to = f
hProp-iso p q f g .from = g
hProp-iso p q f g .from∘to x = p (g (f x)) x
hProp-iso p q f g .to∘from y = q (f (g y)) y

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

¬Σ≅Π¬ : {A : Set} → {B : A → Set}
    → ¬ Σ A B ≅ Π A (¬_ ∘ B)
¬Σ≅Π¬ .to f x y = f (x , y)
¬Σ≅Π¬ .from g (x , y) = g x y
¬Σ≅Π¬ .from∘to f = extensionality (λ { (x , y) → refl })
¬Σ≅Π¬ .to∘from g = refl

Σ¬→¬Π : {A : Set} → {B : A → Set}
    → Σ A (¬_ ∘ B) → ¬ Π A B
Σ¬→¬Π (x , f) g = f (g x)

-- The converse cannot be disproved, if the converse can be disproved, then it must hold in all Heyting models,
-- in particular all Boolean models, hence the double negation translation of the converse must not hold as well,
-- but since the converse can be classically proved, its double negation translation can be constructively proved,
-- as shown below in ¬Π¬¬→¬¬Σ¬, furthermore, the converse is logically equivalent to excluded middle, see NotPiAsSigma
-- in Negation.agda

¬-Is-hProp : {A : Set} → Is-hProp (¬ A)
¬-Is-hProp f g = extensionality λ x → ⊥-elim (f x)

¬¬¬≅¬ : {A : Set} → ¬ ¬ ¬ A ≅ ¬ A
¬¬¬≅¬ = record {
        to = λ f x → f λ g → g x;
        from = λ f g → g f;
        from∘to = λ f → extensionality λ g → ⊥-elim (f g);
        to∘from = λ f → refl
    }

¬Π¬¬→¬¬Σ¬¬¬ : {A : Set} → {B : A → Set}
    → ¬ Π A (¬_ ∘ ¬_ ∘ B) → ¬ ¬ Σ A (¬_ ∘ ¬_ ∘ ¬_ ∘ B)
¬Π¬¬→¬¬Σ¬¬¬ f g = f (λ x h → g (x , λ j → j h))

¬Π¬¬→¬¬Σ¬ : {A : Set} → {B : A → Set}
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

Σ-eq-iso : {A : Set} → {B : A → Set}
    → {x1 x2 : A} → {y1 : B x1} → {y2 : B x2}
    → (x1 , y1) ≡ (x2 , y2) ≅ Σ (x1 ≡ x2) (λ p → subst B p y1 ≡ y2)
Σ-eq-iso .to refl = refl , refl
Σ-eq-iso .from (refl , refl) = refl
Σ-eq-iso .from∘to refl = refl
Σ-eq-iso .to∘from (refl , refl) = refl

ℕ≅ΣBinCan : ℕ ≅ Σ Bin Can
ℕ≅ΣBinCan .to n = toBin n , can-toBin n
ℕ≅ΣBinCan .from (x , p) = fromBin x
ℕ≅ΣBinCan .from∘to = fromBin-toBin
ℕ≅ΣBinCan .to∘from (x , p) = Σ-eq-iso .from (can-toBin-fromBin x p , Can-Is-hProp (subst Can (can-toBin-fromBin x p) (can-toBin (fromBin x))) p)

-- Bonus: use encode-decode to prove Is-hSet Bin

codeBin : Bin → Bin → Set
codeBin ⟨⟩ ⟨⟩ = ⊤
codeBin ⟨⟩ (y O) = ⊥
codeBin ⟨⟩ (y I) = ⊥
codeBin (x O) ⟨⟩ = ⊥
codeBin (x O) (y O) = codeBin x y
codeBin (x O) (y I) = ⊥
codeBin (x I) ⟨⟩ = ⊥
codeBin (x I) (y O) = ⊥
codeBin (x I) (y I) = codeBin x y

rBin : (x : Bin) → codeBin x x
rBin ⟨⟩ = tt
rBin (x O) = rBin x
rBin (x I) = rBin x

encodeBin : (x y : Bin) → x ≡ y → codeBin x y
encodeBin x y p = subst (codeBin x) p (rBin x)

decodeBin : (x y : Bin) → codeBin x y → x ≡ y
decodeBin ⟨⟩ ⟨⟩ tt = refl
decodeBin (x O) (y O) c = cong _O (decodeBin x y c)
decodeBin (x I) (y I) c = cong _I (decodeBin x y c)

Bin-eq≅codeBin : (x y : Bin) → x ≡ y ≅ codeBin x y
Bin-eq≅codeBin x y .to = encodeBin x y
Bin-eq≅codeBin x y .from = decodeBin x y
Bin-eq≅codeBin ⟨⟩ .⟨⟩ .from∘to refl = refl
Bin-eq≅codeBin (x O) .(x O) .from∘to refl = cong (cong _O) (Bin-eq≅codeBin x x .from∘to refl)
Bin-eq≅codeBin (x I) .(x I) .from∘to refl = cong (cong _I) (Bin-eq≅codeBin x x .from∘to refl)
Bin-eq≅codeBin ⟨⟩ ⟨⟩ .to∘from tt = refl
Bin-eq≅codeBin (x O) (y O) .to∘from c = trans (subst-cong (codeBin (x O)) (decodeBin x y c)) (Bin-eq≅codeBin x y .to∘from c)
Bin-eq≅codeBin (x I) (y I) .to∘from c = trans (subst-cong (codeBin (x I)) (decodeBin x y c)) (Bin-eq≅codeBin x y .to∘from c)

codeBin-Is-hProp : (x y : Bin) → Is-hProp (codeBin x y)
codeBin-Is-hProp ⟨⟩ ⟨⟩ = Unit-Is-hProp
codeBin-Is-hProp ⟨⟩ (y O) = Empty-Is-hProp
codeBin-Is-hProp ⟨⟩ (y I) = Empty-Is-hProp
codeBin-Is-hProp (x O) ⟨⟩ = Empty-Is-hProp
codeBin-Is-hProp (x O) (y O) = codeBin-Is-hProp x y
codeBin-Is-hProp (x O) (y I) = Empty-Is-hProp
codeBin-Is-hProp (x I) ⟨⟩ = Empty-Is-hProp
codeBin-Is-hProp (x I) (y O) = Empty-Is-hProp
codeBin-Is-hProp (x I) (y I) = codeBin-Is-hProp x y

Bin-Is-hSet : Is-hSet Bin
Bin-Is-hSet x y = ≅-Is-hProp (Bin-eq≅codeBin x y) (codeBin-Is-hProp x y)
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
