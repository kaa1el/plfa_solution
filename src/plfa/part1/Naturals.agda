{-# OPTIONS --without-K #-}

module plfa.part1.Naturals where

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

_ : ℕ
_ = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

_ : ℕ
_ = 7

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

_ : 2 + 3 ≡ 5
_ = 
    begin
        2 + 3
    ≡⟨⟩    -- is shorthand for
        (suc (suc zero)) + (suc (suc (suc zero)))
    ≡⟨⟩    -- inductive case
        suc ((suc zero) + (suc (suc (suc zero))))
    ≡⟨⟩    -- inductive case
        suc (suc (zero + (suc (suc (suc zero)))))
    ≡⟨⟩    -- base case
        suc (suc (suc (suc (suc zero))))
    ≡⟨⟩    -- is longhand for
        5
    ∎

_ : 2 + 3 ≡ 5
_ =
    begin
        2 + 3
    ≡⟨⟩
        suc (1 + 3)
    ≡⟨⟩
        suc (suc (0 + 3))
    ≡⟨⟩
        suc (suc 3)
    ≡⟨⟩
        5
    ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 + 4 ≡ 7
_ = refl

_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + (n * m)

_ =
    begin
        2 * 3
    ≡⟨⟩    -- inductive case
        3 + (1 * 3)
    ≡⟨⟩    -- inductive case
        3 + (3 + (0 * 3))
    ≡⟨⟩    -- base case
        3 + (3 + 0)
    ≡⟨⟩    -- simplify
        6
    ∎

_ : 3 * 4 ≡ 12
_ = refl

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ = refl

_∸_ : ℕ → ℕ → ℕ
n ∸ zero = n
zero ∸ suc m = zero
suc n ∸ suc m = n ∸ m

_ =
    begin
        3 ∸ 2
    ≡⟨⟩
        2 ∸ 1
    ≡⟨⟩
        1 ∸ 0
    ≡⟨⟩
        1
    ∎

_ =
    begin
        2 ∸ 3
    ≡⟨⟩
        1 ∸ 2
    ≡⟨⟩
        0 ∸ 1
    ≡⟨⟩
        0
    ∎

_ : 5 ∸ 3 ≡ 2
_ = refl

_ : 3 ∸ 5 ≡ 0
_ = refl

infixl 6 _+_ _∸_
infixl 7 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

div-suc-aux : (quotient m n counter : ℕ) → ℕ
div-suc-aux quotient m zero counter = quotient
div-suc-aux quotient m (suc n) zero = div-suc-aux (suc quotient) m n m
div-suc-aux quotient m (suc n) (suc counter) = div-suc-aux quotient m n counter

{-# BUILTIN NATDIVSUCAUX div-suc-aux #-}

-- div-suc-aux 0 2 10 2
-- div-suc-aux 0 2 9 1
-- div-suc-aux 0 2 8 0
-- div-suc-aux 1 2 7 2
-- div-suc-aux 1 2 6 1
-- div-suc-aux 1 2 5 0
-- div-suc-aux 2 2 4 2
-- div-suc-aux 2 2 3 1
-- div-suc-aux 2 2 2 0
-- div-suc-aux 3 2 1 2
-- div-suc-aux 3 2 0 1
-- 3

-- div-suc n m ≡ n / (suc m)

div-suc : ℕ → ℕ → ℕ
div-suc n m = div-suc-aux 0 m n m

mod-suc-aux : (remainder m n counter : ℕ) → ℕ
mod-suc-aux remainder m zero counter = remainder
mod-suc-aux remainder m (suc n) zero = mod-suc-aux zero m n m
mod-suc-aux remainder m (suc n) (suc counter) = mod-suc-aux (suc remainder) m n counter

{-# BUILTIN NATMODSUCAUX mod-suc-aux #-}

-- mod-suc-aux 0 2 10 2
-- mod-suc-aux 1 2 9 1
-- mod-suc-aux 2 2 8 0
-- mod-suc-aux 0 2 7 2
-- mod-suc-aux 1 2 6 1
-- mod-suc-aux 2 2 5 0
-- mod-suc-aux 0 2 4 2
-- mod-suc-aux 1 2 3 1
-- mod-suc-aux 2 2 2 0
-- mod-suc-aux 0 2 1 2
-- mod-suc-aux 1 2 0 1
-- 1

mod-suc : ℕ → ℕ → ℕ
mod-suc n m = mod-suc-aux 0 m n m

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
