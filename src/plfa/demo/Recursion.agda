{-# OPTIONS --without-K #-}

module plfa.demo.Recursion where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; uncurry)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import plfa.part1.Equality using (trans-identity-l; trans-identity-r; trans-sym-l; trans-sym-r; trans-assoc; trans-cong; sym-cong; sym-trans; cong-d; subst-cong; subst-trans)
open import plfa.demo.EckmannHilton using (lift; lift-proj₁)

ind-ℕ : {P : ℕ → Set} -- standard induction
    → (P zero)
    → ((n : ℕ) → P n → P (suc n))
    → ((n : ℕ) → P n)
ind-ℕ pz ps zero = pz
ind-ℕ pz ps (suc n) = ps n (ind-ℕ pz ps n)

ind-ℕ-η : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (f : (n : ℕ) → P n)
    → f zero ≡ pz
    → ((n : ℕ) → f (suc n) ≡ ps n (f n))
    → ((n : ℕ) → f n ≡ ind-ℕ pz ps n)
ind-ℕ-η pz ps f ez es = ind-ℕ ez qs where
    qs : (n : ℕ) → f n ≡ ind-ℕ pz ps n → f (suc n) ≡ ind-ℕ pz ps (suc n)
    qs n e = trans (es n) (cong (ps n) e)

rec-ℕ : {C : Set} → C → (ℕ → C → C) → (ℕ → C) -- standard recursion, non-dependent version of standard induction
rec-ℕ cz cs = ind-ℕ cz cs
-- rec-ℕ cz cs zero = cz
-- rec-ℕ cz cs (suc n) = cs n (rec-ℕ cz cs n)

rec-ℕ-η : {C : Set} → (cz : C) → (cs : ℕ → C → C) → (f : ℕ → C)
    → f zero ≡ cz
    → ((n : ℕ) → f (suc n) ≡ cs n (f n))
    → ((n : ℕ) → f n ≡ rec-ℕ cz cs n)
rec-ℕ-η = ind-ℕ-η

postulate
    r-ℕ : {X : Set} → X → (X → X) → (ℕ → X) -- categorical recursion (initial algebra), also called iteration
-- r-ℕ xz xs = rec-ℕ xz (λ _ → xs)
-- r-ℕ xz xs zero = xz
-- r-ℕ xz xs (suc n) = xs (r-ℕ xz xs n)
    r-ℕ-βz : {X : Set}
        → (xz : X)
        → (xs : X → X)
        → r-ℕ xz xs zero ≡ xz
    r-ℕ-βs : {X : Set}
        → (xz : X)
        → (xs : X → X)
        → ((n : ℕ) → r-ℕ xz xs (suc n) ≡ xs (r-ℕ xz xs n))

postulate
    r-ℕ-η : {X : Set} → (xz : X) → (xs : X → X) → (f : ℕ → X)
        → f zero ≡ xz
        → ((n : ℕ) → f (suc n) ≡ xs (f n))
        → ((n : ℕ) → f n ≡ r-ℕ xz xs n)
    r-ℕ-η-βz : {X : Set} → (xz : X) → (xs : X → X) → (f : ℕ → X)
        → (ez : f zero ≡ xz)
        → (es : (n : ℕ) → f (suc n) ≡ xs (f n))
        → r-ℕ-η xz xs f ez es zero ≡ trans ez (sym (r-ℕ-βz xz xs))
    r-ℕ-η-βs : {X : Set} → (xz : X) → (xs : X → X) → (f : ℕ → X)
        → (ez : f zero ≡ xz)
        → (es : (n : ℕ) → f (suc n) ≡ xs (f n))
        → (n : ℕ) → r-ℕ-η xz xs f ez es (suc n) ≡ trans (trans (es n) (cong xs (r-ℕ-η xz xs f ez es n))) (sym (r-ℕ-βs xz xs n))

-- deriving standard recursion from iteration

rec-ℕ′-full : {C : Set} → C → (ℕ → C → C) → (ℕ → ℕ × C)
rec-ℕ′-full {C} cz cs n = r-ℕ {ℕ × C} xz xs n where
    xz : ℕ × C
    xz = (zero , cz)
    xs : ℕ × C → ℕ × C
    xs w = (suc (proj₁ w) , cs (proj₁ w) (proj₂ w))

rec-ℕ′-1 : {C : Set} → C → (ℕ → C → C) → (ℕ → ℕ)
rec-ℕ′-1 cz cs n = proj₁ (rec-ℕ′-full cz cs n)

rec-ℕ′-1-βz : {C : Set} → (cz : C) → (cs : ℕ → C → C)
    → rec-ℕ′-1 cz cs zero ≡ zero
rec-ℕ′-1-βz {C} cz cs = cong proj₁ (r-ℕ-βz xz xs) where
    xz : ℕ × C
    xz = (zero , cz)
    xs : ℕ × C → ℕ × C
    xs w = (suc (proj₁ w) , cs (proj₁ w) (proj₂ w))

rec-ℕ′-1-βs : {C : Set} → (cz : C) → (cs : ℕ → C → C)
    → (n : ℕ) → rec-ℕ′-1 cz cs (suc n) ≡ suc (rec-ℕ′-1 cz cs n)
rec-ℕ′-1-βs {C} cz cs n = cong proj₁ (r-ℕ-βs xz xs n) where
    xz : ℕ × C
    xz = (zero , cz)
    xs : ℕ × C → ℕ × C
    xs w = (suc (proj₁ w) , cs (proj₁ w) (proj₂ w))

rec-ℕ′-1-β : {C : Set} → (cz : C) → (cs : ℕ → C → C)
    → (n : ℕ) → rec-ℕ′-1 cz cs n ≡ n
rec-ℕ′-1-β cz cs n =
    trans
        (r-ℕ-η zero suc (rec-ℕ′-1 cz cs) (rec-ℕ′-1-βz cz cs) (rec-ℕ′-1-βs cz cs) n)
        (sym (r-ℕ-η zero suc id refl (λ _ → refl) n))

rec-ℕ′ : {C : Set} → C → (ℕ → C → C) → (ℕ → C) -- standard recursion from iteration
rec-ℕ′ cz cs n = proj₂ (rec-ℕ′-full cz cs n)

rec-ℕ′-βz : {C : Set} → (cz : C) → (cs : ℕ → C → C)
    → rec-ℕ′ cz cs zero ≡ cz
rec-ℕ′-βz {C} cz cs = cong proj₂ (r-ℕ-βz xz xs) where
    xz : ℕ × C
    xz = (zero , cz)
    xs : ℕ × C → ℕ × C
    xs w = (suc (proj₁ w) , cs (proj₁ w) (proj₂ w))

rec-ℕ′-βs : {C : Set} → (cz : C) → (cs : ℕ → C → C)
    → (n : ℕ) → rec-ℕ′ cz cs (suc n) ≡ cs n (rec-ℕ′ cz cs n)
rec-ℕ′-βs {C} cz cs n =
    begin
        rec-ℕ′ cz cs (suc n)
    ≡⟨⟩
        proj₂ (r-ℕ xz xs (suc n))
    ≡⟨ cong proj₂ (r-ℕ-βs xz xs n) ⟩
        cs (proj₁ (r-ℕ xz xs n)) (proj₂ (r-ℕ xz xs n))
    ≡⟨⟩
        cs (rec-ℕ′-1 cz cs n) (rec-ℕ′ cz cs n)
    ≡⟨ cong (λ m → cs m (rec-ℕ′ cz cs n)) (rec-ℕ′-1-β cz cs n) ⟩
        cs n (rec-ℕ′ cz cs n)
    ∎ where
    xz : ℕ × C
    xz = (zero , cz)
    xs : ℕ × C → ℕ × C
    xs w = (suc (proj₁ w) , cs (proj₁ w) (proj₂ w))

rec-ℕ′≡rec-ℕ : {C : Set} → (cz : C) → (cs : ℕ → C → C)
    → (n : ℕ) → rec-ℕ′ cz cs n ≡ rec-ℕ cz cs n
rec-ℕ′≡rec-ℕ cz cs = rec-ℕ-η cz cs (rec-ℕ′ cz cs) (rec-ℕ′-βz cz cs) (rec-ℕ′-βs cz cs)

-- deriving standard induction from iteration

ind-ℕ′-full : {P : ℕ → Set}
    → P zero
    → ((n : ℕ) → P n → P (suc n))
    → ((n : ℕ) → Σ ℕ P)
ind-ℕ′-full {P} pz ps n = r-ℕ {Σ ℕ P} xz xs n where
    xz : Σ ℕ P
    xz = (zero , pz)
    xs : Σ ℕ P → Σ ℕ P
    xs w = (suc (proj₁ w) , ps (proj₁ w) (proj₂ w))

ind-ℕ′-1 : {P : ℕ → Set}
    → P zero
    → ((n : ℕ) → P n → P (suc n))
    → ((n : ℕ) → ℕ)
ind-ℕ′-1 pz ps n = proj₁ (ind-ℕ′-full pz ps n)

ind-ℕ′-1-βz : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → ind-ℕ′-1 pz ps zero ≡ zero
ind-ℕ′-1-βz {P} pz ps = cong proj₁ (r-ℕ-βz xz xs) where
    xz : Σ ℕ P
    xz = (zero , pz)
    xs : Σ ℕ P → Σ ℕ P
    xs w = (suc (proj₁ w) , ps (proj₁ w) (proj₂ w))

ind-ℕ′-1-βs : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′-1 pz ps (suc n) ≡ suc (ind-ℕ′-1 pz ps n)
ind-ℕ′-1-βs {P} pz ps n = cong proj₁ (r-ℕ-βs xz xs n) where
    xz : Σ ℕ P
    xz = (zero , pz)
    xs : Σ ℕ P → Σ ℕ P
    xs w = (suc (proj₁ w) , ps (proj₁ w) (proj₂ w))

ind-ℕ′-1-β : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′-1 pz ps n ≡ n
ind-ℕ′-1-β pz ps n =
    trans
        (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)
        (sym (r-ℕ-η zero suc id refl (λ _ → refl) n))

ind-ℕ′-1-β-βz : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → ind-ℕ′-1-β pz ps zero ≡ ind-ℕ′-1-βz pz ps
ind-ℕ′-1-β-βz {P} pz ps =
    begin
        ind-ℕ′-1-β pz ps zero
    ≡⟨⟩
        trans
            (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) zero)
            (sym (r-ℕ-η zero suc id refl (λ _ → refl) zero))
    ≡⟨ cong₂ (λ e₁ e₂ → trans e₁ (sym e₂)) (r-ℕ-η-βz zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps)) (r-ℕ-η-βz zero suc id refl (λ _ → refl)) ⟩
        trans
            (trans (ind-ℕ′-1-βz pz ps) (sym (r-ℕ-βz zero suc)))
            (sym (trans refl (sym (r-ℕ-βz zero suc))))
    ≡⟨ cong (λ e → trans (trans (ind-ℕ′-1-βz pz ps) (sym (r-ℕ-βz zero suc))) (sym e)) (trans-identity-l (sym (r-ℕ-βz zero suc))) ⟩
        trans
            (trans (ind-ℕ′-1-βz pz ps) (sym (r-ℕ-βz zero suc)))
            (sym (sym (r-ℕ-βz zero suc)))
    ≡⟨ trans-assoc (ind-ℕ′-1-βz pz ps) (sym (r-ℕ-βz zero suc)) (sym (sym (r-ℕ-βz zero suc))) ⟩
        trans
            (ind-ℕ′-1-βz pz ps)
            (trans
                (sym (r-ℕ-βz zero suc))
                (sym (sym (r-ℕ-βz zero suc))))
    ≡⟨ cong (λ e → trans (ind-ℕ′-1-βz pz ps) e) (trans-sym-r (sym (r-ℕ-βz zero suc))) ⟩
        trans (ind-ℕ′-1-βz pz ps) refl
    ≡⟨ trans-identity-r (ind-ℕ′-1-βz pz ps) ⟩
        ind-ℕ′-1-βz pz ps
    ∎ where
    xz : Σ ℕ P
    xz = (zero , pz)
    xs : Σ ℕ P → Σ ℕ P
    xs w = (suc (proj₁ w) , ps (proj₁ w) (proj₂ w))

ind-ℕ′-1-β-βs : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′-1-β pz ps (suc n) ≡ trans (ind-ℕ′-1-βs pz ps n) (cong suc (ind-ℕ′-1-β pz ps n))
ind-ℕ′-1-β-βs {P} pz ps n =
    begin
        ind-ℕ′-1-β pz ps (suc n)
    ≡⟨⟩
        trans
            (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) (suc n))
            (sym (r-ℕ-η zero suc id refl (λ _ → refl) (suc n)))
    ≡⟨ cong₂ (λ e₁ e₂ → trans e₁ (sym e₂)) (r-ℕ-η-βs zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n) (r-ℕ-η-βs zero suc id refl (λ _ → refl) n) ⟩
        trans
            (trans
                (trans
                    (ind-ℕ′-1-βs pz ps n)
                    (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)))
                (sym (r-ℕ-βs zero suc n)))
            (sym (trans
                (trans
                    refl
                    (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n)))
                (sym (r-ℕ-βs zero suc n))))
    ≡⟨ cong (λ e → trans (trans (trans (ind-ℕ′-1-βs pz ps n) (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n))) (sym (r-ℕ-βs zero suc n))) (sym (trans e (sym (r-ℕ-βs zero suc n))))) (trans-identity-l (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n))) ⟩
        trans
            (trans
                (trans
                    (ind-ℕ′-1-βs pz ps n)
                    (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)))
                (sym (r-ℕ-βs zero suc n)))
            (sym (trans
                (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n))
                (sym (r-ℕ-βs zero suc n))))
    ≡⟨ cong (λ e → trans (trans (trans (ind-ℕ′-1-βs pz ps n) (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n))) (sym (r-ℕ-βs zero suc n))) e) (sym-trans (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n)) (sym (r-ℕ-βs zero suc n))) ⟩
        trans
            (trans
                (trans
                    (ind-ℕ′-1-βs pz ps n)
                    (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)))
                (sym (r-ℕ-βs zero suc n)))
            (trans
                (sym (sym (r-ℕ-βs zero suc n)))
                (sym (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n))))
    ≡⟨ trans-assoc (trans (ind-ℕ′-1-βs pz ps n) (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n))) (sym (r-ℕ-βs zero suc n)) (trans (sym (sym (r-ℕ-βs zero suc n))) (sym (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n)))) ⟩
        trans
            (trans
                (ind-ℕ′-1-βs pz ps n)
                (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)))
            (trans
                (sym (r-ℕ-βs zero suc n))
                (trans
                    (sym (sym (r-ℕ-βs zero suc n)))
                    (sym (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n)))))
    ≡⟨ cong (λ e → trans (trans (ind-ℕ′-1-βs pz ps n) (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n))) e) (sym (trans-assoc (sym (r-ℕ-βs zero suc n)) (sym (sym (r-ℕ-βs zero suc n))) (sym (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n))))) ⟩
        trans
            (trans
                (ind-ℕ′-1-βs pz ps n)
                (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)))
            (trans
                (trans
                    (sym (r-ℕ-βs zero suc n))
                    (sym (sym (r-ℕ-βs zero suc n))))
                (sym (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n))))
    ≡⟨ cong (λ e → trans (trans (ind-ℕ′-1-βs pz ps n) (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n))) (trans e (sym (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n))))) (trans-sym-r (sym (r-ℕ-βs zero suc n))) ⟩
        trans
            (trans
                (ind-ℕ′-1-βs pz ps n)
                (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)))
            (trans
                refl
                (sym (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n))))
    ≡⟨ cong (λ e → trans (trans (ind-ℕ′-1-βs pz ps n) (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n))) e) (trans-identity-l (sym (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n)))) ⟩
        trans
            (trans
                (ind-ℕ′-1-βs pz ps n)
                (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)))
            (sym (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n)))
    ≡⟨ cong (λ e → trans (trans (ind-ℕ′-1-βs pz ps n) (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n))) e) (sym-cong (r-ℕ-η zero suc id refl (λ _ → refl) n)) ⟩
        trans
            (trans
                (ind-ℕ′-1-βs pz ps n)
                (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)))
            (cong suc (sym (r-ℕ-η zero suc id refl (λ _ → refl) n)))
    ≡⟨ trans-assoc (ind-ℕ′-1-βs pz ps n) (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)) (cong suc (sym (r-ℕ-η zero suc id refl (λ _ → refl) n))) ⟩
        trans
            (ind-ℕ′-1-βs pz ps n)
            (trans
                (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n))
                (cong suc (sym (r-ℕ-η zero suc id refl (λ _ → refl) n))))
    ≡⟨ cong (λ e → trans (ind-ℕ′-1-βs pz ps n) e) (trans-cong (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n) (sym (r-ℕ-η zero suc id refl (λ _ → refl) n))) ⟩
        trans
            (ind-ℕ′-1-βs pz ps n)
            (cong suc
                (trans
                    (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)
                    (sym (r-ℕ-η zero suc id refl (λ _ → refl) n))))
    ≡⟨⟩
        trans
            (ind-ℕ′-1-βs pz ps n)
            (cong suc (ind-ℕ′-1-β pz ps n))
    ∎ where
    xz : Σ ℕ P
    xz = (zero , pz)
    xs : Σ ℕ P → Σ ℕ P
    xs w = (suc (proj₁ w) , ps (proj₁ w) (proj₂ w))

ind-ℕ′ : {P : ℕ → Set} -- standard induction from iteration
    → P zero
    → ((n : ℕ) → P n → P (suc n))
    → ((n : ℕ) → P n)
ind-ℕ′ {P} pz ps n = subst P (ind-ℕ′-1-β pz ps n) (proj₂ (ind-ℕ′-full pz ps n))

ind-ℕ′-βz : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → ind-ℕ′ pz ps zero ≡ pz
ind-ℕ′-βz {P} pz ps =
    begin
        ind-ℕ′ pz ps zero
    ≡⟨⟩
        subst P (ind-ℕ′-1-β pz ps zero) (proj₂ (ind-ℕ′-full pz ps zero))
    ≡⟨⟩
        subst P (ind-ℕ′-1-β pz ps zero) (proj₂ (r-ℕ xz xs zero))
    ≡⟨ cong (λ e → subst P e (proj₂ (r-ℕ xz xs zero))) (ind-ℕ′-1-β-βz pz ps) ⟩
        subst P (ind-ℕ′-1-βz pz ps) (proj₂ (r-ℕ xz xs zero))
    ≡⟨⟩
        subst P (cong proj₁ (r-ℕ-βz xz xs)) (proj₂ (r-ℕ xz xs zero))
    ≡⟨ subst-cong P (r-ℕ-βz xz xs) ⟩
        subst (P ∘ proj₁) (r-ℕ-βz xz xs) (proj₂ (r-ℕ xz xs zero))
    ≡⟨ cong-d proj₂ (r-ℕ-βz xz xs) ⟩
        proj₂ xz
    ≡⟨⟩
        pz
    ∎ where
    xz : Σ ℕ P
    xz = (zero , pz)
    xs : Σ ℕ P → Σ ℕ P
    xs w = (suc (proj₁ w) , ps (proj₁ w) (proj₂ w))

ind-ℕ′-βs : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′ pz ps (suc n) ≡ ps n (ind-ℕ′ pz ps n)
ind-ℕ′-βs {P} pz ps n =
    begin
        ind-ℕ′ pz ps (suc n)
    ≡⟨⟩
        subst P (ind-ℕ′-1-β pz ps (suc n)) (proj₂ (ind-ℕ′-full pz ps (suc n)))
    ≡⟨⟩
        subst P (ind-ℕ′-1-β pz ps (suc n)) (proj₂ (r-ℕ xz xs (suc n)))
    ≡⟨ cong (λ e → subst P e (proj₂ (r-ℕ xz xs (suc n)))) (ind-ℕ′-1-β-βs pz ps n) ⟩ -- key step: ind-ℕ′-1-β-βs
        subst P
            (trans
                (ind-ℕ′-1-βs pz ps n)
                (cong suc (ind-ℕ′-1-β pz ps n)))
            (proj₂ (r-ℕ xz xs (suc n)))
    ≡⟨ subst-trans P (ind-ℕ′-1-βs pz ps n) (cong suc (ind-ℕ′-1-β pz ps n)) ⟩
        subst P
            (cong suc (ind-ℕ′-1-β pz ps n))
            (subst P
                (ind-ℕ′-1-βs pz ps n)
                (proj₂ (r-ℕ xz xs (suc n))))
    ≡⟨ subst-cong P (ind-ℕ′-1-β pz ps n) ⟩
        subst (P ∘ suc)
            (ind-ℕ′-1-β pz ps n)
            (subst P
                (ind-ℕ′-1-βs pz ps n)
                (proj₂ (r-ℕ xz xs (suc n)))) -- proj₂ (xs (r-ℕ xz xs n))
    ≡⟨ cong (λ e → subst (P ∘ suc) (ind-ℕ′-1-β pz ps n) (subst P (ind-ℕ′-1-βs pz ps n) e)) (sym (cong-d proj₂ (sym (r-ℕ-βs xz xs n)))) ⟩
        subst (P ∘ suc)
            (ind-ℕ′-1-β pz ps n)
            (subst P
                (ind-ℕ′-1-βs pz ps n)
                (subst (P ∘ proj₁) (sym (r-ℕ-βs xz xs n)) (proj₂ (xs (r-ℕ xz xs n)))))
    ≡⟨⟩
        subst (P ∘ suc)
            (ind-ℕ′-1-β pz ps n)
            (subst P
                (cong proj₁ (r-ℕ-βs xz xs n)) -- should be cancellable
                (subst (P ∘ proj₁) (sym (r-ℕ-βs xz xs n)) (ps (proj₁ (r-ℕ xz xs n)) (proj₂ (r-ℕ xz xs n)))))
    ≡⟨ cong (λ e → subst (P ∘ suc) (ind-ℕ′-1-β pz ps n) (subst P (cong proj₁ (r-ℕ-βs xz xs n)) e)) (sym (subst-cong P (sym (r-ℕ-βs xz xs n)))) ⟩
        subst (P ∘ suc)
            (ind-ℕ′-1-β pz ps n)
            (subst P
                (cong proj₁ (r-ℕ-βs xz xs n))
                (subst P (cong proj₁ (sym (r-ℕ-βs xz xs n))) (ps (proj₁ (r-ℕ xz xs n)) (proj₂ (r-ℕ xz xs n)))))
    ≡⟨ cong (λ e → subst (P ∘ suc) (ind-ℕ′-1-β pz ps n) e) (sym (subst-trans P (cong proj₁ (sym (r-ℕ-βs xz xs n))) (cong proj₁ (r-ℕ-βs xz xs n)))) ⟩
        subst (P ∘ suc)
            (ind-ℕ′-1-β pz ps n)
            (subst P
                (trans
                    (cong proj₁ (sym (r-ℕ-βs xz xs n)))
                    (cong proj₁ (r-ℕ-βs xz xs n)))
                (ps (proj₁ (r-ℕ xz xs n)) (proj₂ (r-ℕ xz xs n))))
    ≡⟨ cong (λ e → subst (P ∘ suc) (ind-ℕ′-1-β pz ps n) (subst P (trans e (cong proj₁ (r-ℕ-βs xz xs n))) (ps (proj₁ (r-ℕ xz xs n)) (proj₂ (r-ℕ xz xs n))))) (sym (sym-cong (r-ℕ-βs xz xs n))) ⟩
        subst (P ∘ suc)
            (ind-ℕ′-1-β pz ps n)
            (subst P
                (trans
                    (sym (cong proj₁ (r-ℕ-βs xz xs n)))
                    (cong proj₁ (r-ℕ-βs xz xs n)))
                (ps (proj₁ (r-ℕ xz xs n)) (proj₂ (r-ℕ xz xs n))))
    ≡⟨ cong (λ e → subst (P ∘ suc) (ind-ℕ′-1-β pz ps n) (subst P e (ps (proj₁ (r-ℕ xz xs n)) (proj₂ (r-ℕ xz xs n))))) (trans-sym-l (cong proj₁ (r-ℕ-βs xz xs n))) ⟩
        subst (P ∘ suc)
            (ind-ℕ′-1-β pz ps n)
            (subst P
                refl
                (ps (proj₁ (r-ℕ xz xs n)) (proj₂ (r-ℕ xz xs n))))
    ≡⟨⟩
        subst (P ∘ suc)
            (ind-ℕ′-1-β pz ps n)
            (ps (proj₁ (r-ℕ xz xs n)) (proj₂ (r-ℕ xz xs n)))
    ≡⟨⟩
        subst (P ∘ suc)
            (ind-ℕ′-1-β pz ps n)
            (uncurry ps (r-ℕ xz xs n))
    ≡⟨ cong (λ e → subst (P ∘ suc) e (uncurry ps (r-ℕ xz xs n))) (sym (lift-proj₁ (proj₂ (r-ℕ xz xs n)) (ind-ℕ′-1-β pz ps n))) ⟩
        subst (P ∘ suc)
            (cong proj₁ (lift (proj₂ (r-ℕ xz xs n)) (ind-ℕ′-1-β pz ps n)))
            (uncurry ps (r-ℕ xz xs n))
    ≡⟨ subst-cong (P ∘ suc) (lift (proj₂ (r-ℕ xz xs n)) (ind-ℕ′-1-β pz ps n)) ⟩
        subst (P ∘ suc ∘ proj₁)
            (lift (proj₂ (r-ℕ xz xs n)) (ind-ℕ′-1-β pz ps n))
            (uncurry ps (r-ℕ xz xs n))
    ≡⟨ cong-d (uncurry ps) (lift (proj₂ (r-ℕ xz xs n)) (ind-ℕ′-1-β pz ps n)) ⟩
        uncurry ps (n , subst P (ind-ℕ′-1-β pz ps n) (proj₂ (r-ℕ xz xs n)))
    ≡⟨⟩
        ps n (subst P (ind-ℕ′-1-β pz ps n) (proj₂ (r-ℕ xz xs n)))
    ≡⟨⟩
        ps n (subst P (ind-ℕ′-1-β pz ps n) (proj₂ (ind-ℕ′-full pz ps n)))
    ≡⟨⟩
        ps n (ind-ℕ′ pz ps n)
    ∎ where
    xz : Σ ℕ P
    xz = (zero , pz)
    xs : Σ ℕ P → Σ ℕ P
    xs w = (suc (proj₁ w) , ps (proj₁ w) (proj₂ w))
-- proj₂ (r-ℕ xz xs (suc n)) : P (proj₁ (r-ℕ xz xs (suc n)))
-- proj₂ (xs (r-ℕ xz xs n)) : P (proj₁ (xs (r-ℕ xz xs n)))

ind-ℕ′≡ind-ℕ : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′ pz ps n ≡ ind-ℕ pz ps n
ind-ℕ′≡ind-ℕ pz ps = ind-ℕ-η pz ps (ind-ℕ′ pz ps) (ind-ℕ′-βz pz ps) (ind-ℕ′-βs pz ps)
