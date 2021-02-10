{-# OPTIONS --without-K #-}

module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm; +-suc)

data _≤_ : ℕ → ℕ → Set where -- indexed data type
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)

+-identityʳ′ : {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _

infix 4 _≤_

inv-s≤s : {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-trans′ : (m n p : ℕ) → m ≤ n → n ≤ p → m ≤ p
≤-trans′ zero _ _ _ _ = z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans′ m n p m≤n n≤p)

≤-antisym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where -- parameterized data type
    forward : m ≤ n → Total m n -- parameters must be the same for all constructors
    flipped : n ≤ m → Total m n -- m and n became implicit parameters of the constructors

data Total′ : ℕ → ℕ → Set where -- this is indexed data type, but same as above
    forward′ : {m n : ℕ} → m ≤ n → Total′ m n
    flipped′ : {m n : ℕ} → n ≤ m → Total′ m n

≤-total : (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)

≤-total′ : (m n : ℕ) → Total m n -- this is equivalent to the previous definition with "with" clause
≤-total′ zero n = forward z≤n
≤-total′ (suc m) zero = flipped z≤n
≤-total′ (suc m) (suc n) = helper (≤-total′ m n) where
    helper : Total m n → Total (suc m) (suc n)
    helper (forward m≤n) = forward (s≤s m≤n)
    helper (flipped n≤m) = flipped (s≤s n≤m)

≤-total″ : (m n : ℕ) → Total m n -- alternative definition to ≤-total
≤-total″ m zero = flipped z≤n
≤-total″ zero (suc n) = forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n
    rewrite +-comm m p
    | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n
    rewrite *-comm m p
    | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

_≥_ : ℕ → ℕ → Set
m ≥ n = n ≤ m

infix 4 _≥_

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
    z<s : {n : ℕ} → zero < suc n
    s<s : {m n : ℕ} → m < n → suc m < suc n

<-trans : {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s _) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

_>_ : ℕ → ℕ → Set
m > n = n < m

infix 4 _>_

data Trichotomy (m n : ℕ) : Set where
    <-case : m < n → Trichotomy m n
    ≡-case : m ≡ n → Trichotomy m n
    >-case : m > n → Trichotomy m n

<-trichotomy : (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = ≡-case refl
<-trichotomy zero (suc n) = <-case z<s
<-trichotomy (suc m) zero = >-case z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
... | <-case m<n = <-case (s<s m<n)
... | ≡-case m≡n rewrite m≡n = ≡-case refl
... | >-case m>n = >-case (s<s m>n)

+-monoʳ-< : (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n
    rewrite +-comm m p
    | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

*-monoʳ-< : (n p q : ℕ) → p < q → (suc n) * p < (suc n) * q
*-monoʳ-< zero p q p<q rewrite +-identityʳ p | +-identityʳ q = p<q
*-monoʳ-< (suc n) p q p<q =
    <-trans
        (+-monoˡ-< p q (p + n * p) p<q)
        (+-monoʳ-< q (p + n * p) (q + n * q) (*-monoʳ-< n p q p<q))

≤-to-< : (m n : ℕ) → suc m ≤ n → m < n
≤-to-< zero (suc _) (s≤s _) = z<s
≤-to-< (suc m) (suc n) (s≤s e) = s<s (≤-to-< m n e)

<-to-≤ : (m n : ℕ) → m < n → suc m ≤ n
<-to-≤ zero (suc _) z<s = s≤s z≤n
<-to-≤ (suc m) (suc n) (s<s e) = s≤s (<-to-≤ m n e)

≤-suc : (n : ℕ) → n ≤ suc n
≤-suc zero = z≤n
≤-suc (suc n) = s≤s (≤-suc n)

<-suc : (n : ℕ) → n < suc n
<-suc zero = z<s
<-suc (suc n) = s<s (<-suc n)

<-trans-revisited : {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited {m} {n} {p} m<n n<p = ≤-to-< m p (≤-trans first second) where
    first : suc m ≤ suc n
    first = ≤-trans (<-to-≤ m n m<n) (≤-suc n)
    second : suc n ≤ p
    second = <-to-≤ n p n<p

data Even : ℕ → Set
data Odd : ℕ → Set
data Even where
    zero : Even zero
    suc : {n : ℕ} → Odd n → Even (suc n)
data Odd where
    suc : {n : ℕ} → Even n → Odd (suc n)

e+e≡e : {m n : ℕ} → Even m → Even n → Even (m + n)
o+e≡o : {m n : ℕ} → Odd m → Even n → Odd (m + n)
e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)
o+e≡o (suc em) en = suc (e+e≡e em en)

o+o≡e : {m n : ℕ} → Odd m → Odd n → Even (m + n)
o+o≡e (suc {m} em) (suc {n} en) rewrite +-suc m n = suc (suc (e+e≡e em en))

-- Binary Natural Numbers (Continued)

open import plfa.part1.Induction
    using (Bin; ⟨⟩; _O; _I; bsuc; toBin; fromBin; badd; bzero; badd-bsuc-l)

data One : Bin → Set where
    justI : One (⟨⟩ I)
    caseO : {b : Bin} → One b → One (b O)
    caseI : {b : Bin} → One b → One (b I)

data Can : Bin → Set where
    justO : Can (⟨⟩ O)
    fromOne : {b : Bin} → One b → Can b

one-bsuc : {b : Bin} → One b → One (bsuc b)
one-bsuc justI = caseO justI
one-bsuc (caseO p) = caseI p
one-bsuc (caseI p) = caseO (one-bsuc p)

can-bsuc : {b : Bin} → Can b → Can (bsuc b)
can-bsuc justO = fromOne justI
can-bsuc (fromOne p) = fromOne (one-bsuc p)

one-toBin : (n : ℕ) → One (toBin (suc n))
one-toBin zero = justI
one-toBin (suc n) = one-bsuc (one-toBin n)

can-toBin : (n : ℕ) → Can (toBin n)
can-toBin zero = justO
can-toBin (suc n) = fromOne (one-toBin n)

badd-bzero : (b : Bin) → Can b → badd bzero b ≡ b
badd-bzero _ justO = refl
badd-bzero (b O) (fromOne p) = refl
badd-bzero (b I) (fromOne p) = refl

toBin-hom-+ : (n m : ℕ) → toBin (n + m) ≡ badd (toBin n) (toBin m)
toBin-hom-+ zero m rewrite badd-bzero (toBin m) (can-toBin m) = refl
toBin-hom-+ (suc n) m
    rewrite badd-bsuc-l (toBin n) (toBin m)
    | toBin-hom-+ n m = refl

badd-double : (b : Bin) → One b → badd b b ≡ b O
badd-double _ justI = refl
badd-double (b O) (caseO p) rewrite badd-double b p = refl
badd-double (b I) (caseI p) rewrite badd-double b p = refl

one-toBin-fromBin : (b : Bin) → One b → toBin (fromBin b) ≡ b
one-toBin-fromBin _ justI = refl
one-toBin-fromBin (b O) (caseO p)
    rewrite toBin-hom-+ (fromBin b) (fromBin b)
    | one-toBin-fromBin b p
    | badd-double b p = refl
one-toBin-fromBin (b I) (caseI p)
    rewrite toBin-hom-+ (fromBin b) (fromBin b)
    | one-toBin-fromBin b p
    | badd-double b p = refl

can-toBin-fromBin : (b : Bin) → Can b → toBin (fromBin b) ≡ b
can-toBin-fromBin _ justO = refl
can-toBin-fromBin b (fromOne p) = one-toBin-fromBin b p
