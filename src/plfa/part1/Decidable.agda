{-# OPTIONS --without-K #-}

module plfa.part1.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; _≢_)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import plfa.part1.Induction using (suc-inj)
open import plfa.part1.Relations using (_≤_; z≤n; s≤s; _<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_≅_; _⇔_)
open import plfa.part1.Connectives using (Bool; false; true)
open import plfa.part1.Quantifiers using (Is-hProp; Empty-Is-hProp; Unit-Is-hProp; hProp-iso)

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ m = true
suc n ≤ᵇ zero = false
suc n ≤ᵇ suc m = n ≤ᵇ m

_ : (2 ≤ᵇ 4) ≡ true
_ =
    begin
        2 ≤ᵇ 4
    ≡⟨⟩
        1 ≤ᵇ 3
    ≡⟨⟩
        0 ≤ᵇ 2
    ≡⟨⟩
        true
    ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
    begin
        4 ≤ᵇ 2
    ≡⟨⟩
        3 ≤ᵇ 1
    ≡⟨⟩
        2 ≤ᵇ 0
    ≡⟨⟩
        false
    ∎

T : Bool → Set
T false = ⊥
T true = ⊤

T→≡ : (b : Bool) → T b → b ≡ true
T→≡ true tt = refl

≡→T : (b : Bool) → b ≡ true → T b
≡→T .true refl = tt

≤ᵇ→≤ : (n m : ℕ) → T (n ≤ᵇ m) → n ≤ m
≤ᵇ→≤ zero m tt = z≤n
≤ᵇ→≤ (suc n) zero ()
≤ᵇ→≤ (suc n) (suc m) t = s≤s (≤ᵇ→≤ n m t)

≤→≤ᵇ : (n m : ℕ) → n ≤ m → T (n ≤ᵇ m)
≤→≤ᵇ .0 m z≤n = tt
≤→≤ᵇ .(suc n) .(suc m) (s≤s {n} {m} p) = ≤→≤ᵇ n m p

open _≅_

T-Is-hProp : (n m : ℕ) → Is-hProp (T (n ≤ᵇ m))
T-Is-hProp zero m = Unit-Is-hProp
T-Is-hProp (suc n) zero = Empty-Is-hProp
T-Is-hProp (suc n) (suc m) = T-Is-hProp n m

≤-Is-hProp : (n m : ℕ) → Is-hProp (n ≤ m)
≤-Is-hProp .0 m z≤n z≤n = refl
≤-Is-hProp .(suc n) .(suc m) (s≤s {n} {m} p) (s≤s {n} {m} q) = cong s≤s (≤-Is-hProp n m p q)

≤ᵇ≅≤ : (n m : ℕ) → T (n ≤ᵇ m) ≅ n ≤ m
≤ᵇ≅≤ n m = hProp-iso (T-Is-hProp n m) (≤-Is-hProp n m) (≤ᵇ→≤ n m) (≤→≤ᵇ n m)

data Dec (A : Set) : Set where
    yes : A → Dec A
    no : ¬ A → Dec A

¬s≤z : {n : ℕ} → ¬ suc n ≤ zero
¬s≤z ()

¬s≤s : {n m : ℕ} → ¬ n ≤ m → ¬ suc n ≤ suc m
¬s≤s f (s≤s q) = f q

_≤?_ : (n m : ℕ) → Dec (n ≤ m)
zero ≤? m = yes z≤n
suc n ≤? zero = no ¬s≤z
suc n ≤? suc m with n ≤? m
... | yes p = yes (s≤s p)
... | no f = no (¬s≤s f)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

¬n<z : {n : ℕ} → ¬ n < zero
¬n<z ()

¬s<s : {n m : ℕ} → ¬ n < m → ¬ suc n < suc m
¬s<s f (s<s q) = f q

_<?_ : (n m : ℕ) → Dec (n < m)
n <? zero = no ¬n<z
zero <? suc m = yes z<s
suc n <? suc m with n <? m
... | yes p = yes (s<s p)
... | no f = no (¬s<s f)

_≡?_ : (n m : ℕ) → Dec (n ≡ m)
zero ≡? zero = yes refl
zero ≡? suc m = no (λ ())
suc n ≡? zero = no (λ ())
suc n ≡? suc m with n ≡? m
... | yes p = yes (cong suc p)
... | no f = no λ q → f (suc-inj q)

_≤?′_ : (n m : ℕ) → Dec (n ≤ m)
n ≤?′ m with n ≤ᵇ m | ≤ᵇ→≤ n m | ≤→≤ᵇ n m
... | false | f | g = no g
... | true | f | g = yes (f tt)
-- n ≤?′ m with n ≤ᵇ m -- this does not work, check the usage for with-clause
-- ... | false = yes (≤ᵇ→≤ n m tt)
-- ... | true = no (≤→≤ᵇ n m)

test : {P : ℕ → Set} → (n m : ℕ) → P (n + m) → P (m + n)
test n m t with n + m | +-comm n m
-- ... | x | p = ?
... | .(m + n) | refl = t
-- test n m t with +-comm n m | n + m
-- ... | p | x = ?

⌊_⌋ : {A : Set} → Dec A → Bool
⌊ yes _ ⌋ = true
⌊ no _ ⌋ = false

_≤ᵇ′_ : ℕ → ℕ → Bool
n ≤ᵇ′ m = ⌊ n ≤? m ⌋

toWitness : {A : Set} → {x : Dec A} → T ⌊ x ⌋ → A
toWitness {A} {yes p} _ = p

fromWitness : {A : Set} → {x : Dec A} → A → T ⌊ x ⌋
fromWitness {A} {yes _} _ = tt
fromWitness {A} {no f} x = f x

≤ᵇ′→≤ : {n m : ℕ} → T (n ≤ᵇ′ m) → n ≤ m
≤ᵇ′→≤ = toWitness

≤→≤ᵇ′ : {n m : ℕ} → n ≤ m → T (n ≤ᵇ′ m)
≤→≤ᵇ′ = fromWitness

infixr 6 _∧_
_∧_ : Bool → Bool → Bool
false ∧ _ = false
true ∧ b = b

infixr 6 _×-dec_
_×-dec_ : {A B : Set} → Dec A → Dec B → Dec (A × B)
yes p ×-dec yes q = yes (p , q)
yes _ ×-dec no g = no (λ z → g (proj₂ z))
no f ×-dec _ = no (λ z → f (proj₁ z))

infixr 5 _∨_
_∨_ : Bool → Bool → Bool
false ∨ b = b
true ∨ _ = true

infixr 5 _⊎-dec_
_⊎-dec_ : {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes p ⊎-dec _ = yes (inj₁ p)
no f ⊎-dec yes q = yes (inj₂ q)
no f ⊎-dec no g = no λ { (inj₁ x) → f x; (inj₂ y) → g y }

not : Bool → Bool
not false = true
not true = false

¬? : {A : Set} → Dec A → Dec (¬ A)
¬? (yes p) = no λ f → f p
¬? (no f) = yes f

_⊃_ : Bool → Bool → Bool
false ⊃ _ = true
true ⊃ b = b

_→-dec_ : {A B : Set} → Dec A → Dec B → Dec (A → B)
yes _ →-dec yes q = yes λ _ → q
yes p →-dec no g = no (λ h → g (h p))
no f →-dec q = yes λ x → ⊥-elim (f x)

_iff_ : Bool → Bool → Bool
false iff false = true
false iff true = false
true iff b = b

_⇔-dec_ : {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes p ⇔-dec yes q = yes (record { to = λ _ → q; from = λ _ → p })
yes p ⇔-dec no g = no (λ z → g (_⇔_.to z p))
no f ⇔-dec yes q = no (λ z → f (_⇔_.from z q))
no f ⇔-dec no g = yes (record { to = λ x → ⊥-elim (f x); from = λ y → ⊥-elim (g y) })

-- erasure

∧-× : {A B : Set} → (x : Dec A) → (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes _) (yes _) = refl
∧-× (yes _) (no _) = refl
∧-× (no _) _ = refl

∨-⊎ : {A B : Set} → (x : Dec A) → (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes _) _ = refl
∨-⊎ (no _) (yes _) = refl
∨-⊎ (no _) (no _) = refl

not-¬ : {A : Set} → (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes _) = refl
not-¬ (no _) = refl

iff-⇔ : {A B : Set} → (x : Dec A) → (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes _) (yes _) = refl
iff-⇔ (yes _) (no _) = refl
iff-⇔ (no _) (yes _) = refl
iff-⇔ (no _) (no _) = refl

minus : (n m : ℕ) → m ≤ n → ℕ
minus n .0 z≤n = n
minus .(suc n) .(suc m) (s≤s {m} {n} p) = minus n m p

_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl

_-_ : (n m : ℕ) → {T ⌊ m ≤? n ⌋} → ℕ
_-_ n m {p} = minus n m (toWitness p)

_ : 5 - 3 ≡ 2
_ = refl

True : {A : Set} → Dec A → Set
True x = T ⌊ x ⌋

False : {A : Set} → Dec A → Set
False x = T (not ⌊ x ⌋)

toWitnessFalse : {A : Set} → {x : Dec A} → False x → ¬ A
toWitnessFalse {A} {no f} _ = f

fromWitnessFalse : {A : Set} → {x : Dec A} → ¬ A → False x
fromWitnessFalse {A} {yes p} f = ⊥-elim (f p)
fromWitnessFalse {A} {no _} _ = tt

-- import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
-- import Data.Nat using (_≤?_)
-- import Relation.Nullary using (Dec; yes; no)
-- import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
-- import Relation.Nullary.Negation using (¬?)
-- import Relation.Nullary.Product using (_×-dec_)
-- import Relation.Nullary.Sum using (_⊎-dec_)
-- import Relation.Binary using (Decidable)
