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

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
