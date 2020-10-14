module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
    begin
        (3 + 4) + 5
    ≡⟨⟩
        7 + 5
    ≡⟨⟩
        12
    ≡⟨⟩
        3 + 9
    ≡⟨⟩
        3 + (4 + 5)
    ∎

+-assoc : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
    begin
        (zero + n) + p
    ≡⟨⟩
        n + p
    ≡⟨⟩
        zero + (n + p)
    ∎
+-assoc (suc m) n p = 
    begin
        (suc m + n) + p
    ≡⟨⟩
        suc (m + n) + p
    ≡⟨⟩
        suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩
        suc (m + (n + p))
    ≡⟨⟩
        suc m + (n + p)
    ∎

+-assoc-2 : (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
    begin
        (2 + n) + p
    ≡⟨⟩
        suc (1 + n) + p
    ≡⟨⟩
        suc ((1 + n) + p)
    ≡⟨ cong suc (+-assoc-1 n p) ⟩
        suc (1 + (n + p))
    ≡⟨⟩
        2 + (n + p)
    ∎
    where
    +-assoc-1 : (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
    +-assoc-1 n p =
        begin
            (1 + n) + p
        ≡⟨⟩
            suc (0 + n) + p
        ≡⟨⟩
            suc ((0 + n) + p)
        ≡⟨ cong suc (+-assoc-0 n p) ⟩
            suc (0 + (n + p))
        ≡⟨⟩
            1 + (n + p)
        ∎
        where
        +-assoc-0 : (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
        +-assoc-0 n p =
            begin
                (0 + n) + p
            ≡⟨⟩
                n + p
            ≡⟨⟩
                0 + (n + p)
            ∎

+-identityʳ : (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
    begin
        zero + zero
    ≡⟨⟩
        zero
    ∎
+-identityʳ (suc m) =
    begin
        suc m + zero
    ≡⟨⟩
        suc (m + zero)
    ≡⟨ cong suc (+-identityʳ m) ⟩
        suc m
    ∎

+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
    begin
        zero + suc n
    ≡⟨⟩
        suc n
    ≡⟨⟩
        suc (zero + n)
    ∎
+-suc (suc m) n =
    begin
        suc m + suc n
    ≡⟨⟩
        suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩
        suc (suc (m + n))
    ≡⟨⟩
        suc (suc m + n)
    ∎

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
    begin
        m + zero
    ≡⟨ +-identityʳ m ⟩
        m
    ≡⟨⟩
        zero + m
    ∎
+-comm m (suc n) =
    begin
        m + suc n
    ≡⟨ +-suc m n ⟩
        suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
        suc (n + m)
    ≡⟨⟩
        suc n + m
    ∎

+-rearrange : (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
    begin
        (m + n) + (p + q)
    ≡⟨ +-assoc m n (p + q) ⟩
        m + (n + (p + q))
    ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
        m + ((n + p) + q)
    ≡⟨ sym (+-assoc m (n + p) q) ⟩
        (m + (n + p)) + q
    ∎

+-assoc′ : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-identityʳ′ : (n : ℕ) → n + zero ≡ n
+-identityʳ′ zero = refl
+-identityʳ′ (suc n) rewrite +-identityʳ′ n = refl

+-suc′ : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identityʳ′ m = refl
+-comm′ m (suc n)
    rewrite +-suc′ m n
    | +-comm′ m n = refl

+-swap : (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p
    rewrite sym (+-assoc m n p)
    | +-comm m n
    | +-assoc n m p = refl

*-distrib-+ : (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
    rewrite *-distrib-+ m n p
    | sym (+-assoc p (m * p) (n * p)) = refl

*-assoc : (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
    rewrite *-distrib-+ n (m * n) p
    | *-assoc m n p = refl

*-zero : (n : ℕ) → n * zero ≡ zero
*-zero zero = refl
*-zero (suc n) rewrite *-zero n = refl

*-suc : (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl

*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zero n = refl
*-comm (suc m) n rewrite *-suc n m | *-comm m n = refl

0∸n≡0 : (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-+-assoc : (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite 0∸n≡0 n | 0∸n≡0 p | 0∸n≡0 (n + p) = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

^-distribˡ-+-* : (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-+-* m (suc n) p
    rewrite ^-distribˡ-+-* m n p
    | *-assoc m (m ^ n) (m ^ p) = refl

^-distribʳ-* : (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
    rewrite ^-distribʳ-* m n p
    | *-assoc m n ((m ^ p) * (n ^ p))
    | *-assoc m (m ^ p) (n * (n ^ p))
    | sym (*-assoc n (m ^ p) (n ^ p))
    | sym (*-assoc (m ^ p) n (n ^ p))
    | *-comm n (m ^ p) = refl

^-*-assoc : (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-zero n = refl
^-*-assoc m n (suc p)
    rewrite ^-*-assoc m n p
    | *-suc n p
    | ^-distribˡ-+-* m n (n * p) = refl

-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
