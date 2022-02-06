module plfa.demo.RecursionLite where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Function using (id; _∘_)

open import plfa.demo.HoTT

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
-- ind-ℕ-η pz ps f ez es zero = ez
-- ind-ℕ-η pz ps f ez es (suc n) rewrite es n | ind-ℕ-η pz ps f ez es n = refl

rec-ℕ : {C : Set} → C → (ℕ → C → C) → (ℕ → C) -- standard recursion, non-dependent version of standard induction
rec-ℕ cz cs = ind-ℕ cz cs
-- rec-ℕ cz cs zero = cz
-- rec-ℕ cz cs (suc n) = cs n (rec-ℕ cz cs n)

rec-ℕ-η : {C : Set} → (cz : C) → (cs : ℕ → C → C) → (f : ℕ → C)
    → f zero ≡ cz
    → ((n : ℕ) → f (suc n) ≡ cs n (f n))
    → ((n : ℕ) → f n ≡ rec-ℕ cz cs n)
rec-ℕ-η = ind-ℕ-η
-- rec-ℕ-η cz cs f ez es = ind-ℕ ez qs where
--     qs : (n : ℕ) → f n ≡ rec-ℕ cz cs n → f (suc n) ≡ rec-ℕ cz cs (suc n)
--     qs n e = trans (es n) (cong (cs n) e)
-- rec-ℕ-η cz cs f ez es zero = ez
-- rec-ℕ-η cz cs f ez es (suc n) rewrite es n | rec-ℕ-η cz cs f ez es n = refl

r-ℕ : {X : Set} → X → (X → X) → (ℕ → X) -- categorical recursion (initial algebra), also called iteration
r-ℕ xz xs = rec-ℕ xz (λ _ → xs)
-- r-ℕ xz xs zero = xz
-- r-ℕ xz xs (suc n) = xs (r-ℕ xz xs n)

r-ℕ-η : {X : Set} → (xz : X) → (xs : X → X) → (f : ℕ → X)
    → f zero ≡ xz
    → ((n : ℕ) → f (suc n) ≡ xs (f n))
    → ((n : ℕ) → f n ≡ r-ℕ xz xs n)
r-ℕ-η xz xs = rec-ℕ-η xz (λ _ → xs)
-- r-ℕ-η xz xs f ez es = ind-ℕ ez qs where
--     qs : (n : ℕ) → f n ≡ r-ℕ xz xs n → f (suc n) ≡ r-ℕ xz xs (suc n)
--     qs n e = trans (es n) (cong xs e)
-- r-ℕ-η xz xs f ez es zero = ez
-- r-ℕ-η xz xs f ez es (suc n) rewrite es n | r-ℕ-η xz xs f ez es n = refl

r-ℕ-η-βz : {X : Set} → (xz : X) → (xs : X → X) → (f : ℕ → X)
    → (ez : f zero ≡ xz)
    → (es : (n : ℕ) → f (suc n) ≡ xs (f n))
    → r-ℕ-η xz xs f ez es zero ≡ ez
r-ℕ-η-βz xz xs f ez es = refl

r-ℕ-η-βs : {X : Set} → (xz : X) → (xs : X → X) → (f : ℕ → X)
    → (ez : f zero ≡ xz)
    → (es : (n : ℕ) → f (suc n) ≡ xs (f n))
    → (n : ℕ) → r-ℕ-η xz xs f ez es (suc n) ≡ trans (es n) (cong xs (r-ℕ-η xz xs f ez es n))
r-ℕ-η-βs xz xs f ez es n = refl

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
rec-ℕ′-1-βz {C} cz cs = refl

rec-ℕ′-1-βs : {C : Set} → (cz : C) → (cs : ℕ → C → C)
    → (n : ℕ) → rec-ℕ′-1 cz cs (suc n) ≡ suc (rec-ℕ′-1 cz cs n)
rec-ℕ′-1-βs {C} cz cs n = refl

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
rec-ℕ′-βz cz cs = refl

rec-ℕ′-βs-test1 : {C : Set} → (cz : C) → (cs : ℕ → C → C)
    → rec-ℕ′ cz cs 1 ≡ cs 0 (rec-ℕ′ cz cs 0)
rec-ℕ′-βs-test1 cz cs = refl

rec-ℕ′-βs-test2 : {C : Set} → (cz : C) → (cs : ℕ → C → C)
    → rec-ℕ′ cz cs 2 ≡ cs 1 (rec-ℕ′ cz cs 1)
rec-ℕ′-βs-test2 cz cs = refl

rec-ℕ′-βs : {C : Set} → (cz : C) → (cs : ℕ → C → C)
    → (n : ℕ) → rec-ℕ′ cz cs (suc n) ≡ cs n (rec-ℕ′ cz cs n)
rec-ℕ′-βs {C} cz cs n = cong (λ m → cs m (rec-ℕ′ cz cs n)) (rec-ℕ′-1-β cz cs n) -- rewrite rec-ℕ′-1-β cz cs n = refl

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
ind-ℕ′-1-βz {P} pz ps = refl

ind-ℕ′-1-βs : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′-1 pz ps (suc n) ≡ suc (ind-ℕ′-1 pz ps n)
ind-ℕ′-1-βs {P} pz ps n = refl

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
ind-ℕ′-1-β-βz pz ps = refl

ind-ℕ′-1-β-βs : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′-1-β pz ps (suc n) ≡ cong suc (ind-ℕ′-1-β pz ps n)
ind-ℕ′-1-β-βs {P} pz ps n =
    begin
        ind-ℕ′-1-β pz ps (suc n)
    ≡⟨⟩
        trans
            (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) (suc n))
            (sym (r-ℕ-η zero suc id refl (λ _ → refl) (suc n)))
    ≡⟨⟩
        trans
            (trans refl (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)))
            (sym (trans refl (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n))))
    ≡⟨ cong₂ (λ e₁ e₂ → trans e₁ (sym e₂)) (trans-identity-l (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n))) (trans-identity-l (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n))) ⟩
        trans
            (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n))
            (sym (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n)))
    ≡⟨ cong (λ e → trans (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)) e) (sym-cong (r-ℕ-η zero suc id refl (λ _ → refl) n)) ⟩
        trans
            (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n))
            (cong suc (sym (r-ℕ-η zero suc id refl (λ _ → refl) n)))
    ≡⟨ trans-cong (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n) (sym (r-ℕ-η zero suc id refl (λ _ → refl) n)) ⟩
        cong suc
            (trans
                (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) (ind-ℕ′-1-βz pz ps) (ind-ℕ′-1-βs pz ps) n)
                (sym (r-ℕ-η zero suc id refl (λ _ → refl) n)))
    ≡⟨⟩
        cong suc (ind-ℕ′-1-β pz ps n)
    ∎ where
    xz : Σ ℕ P
    xz = (zero , pz)
    xs : Σ ℕ P → Σ ℕ P
    xs w = (suc (proj₁ w) , ps (proj₁ w) (proj₂ w))

ind-ℕ′ : {P : ℕ → Set} -- standard induction from categorical recursion
    → P zero
    → ((n : ℕ) → P n → P (suc n))
    → ((n : ℕ) → P n)
ind-ℕ′ {P} pz ps n = subst P (ind-ℕ′-1-β pz ps n) (proj₂ (ind-ℕ′-full pz ps n))
-- ind-ℕ′ pz ps n rewrite sym (ind-ℕ′-1-β pz ps n) = proj₂ (ind-ℕ′-full pz ps n)

ind-ℕ′-βz : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → ind-ℕ′ pz ps zero ≡ pz
ind-ℕ′-βz pz ps = refl

ind-ℕ′-βs-test1 : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → ind-ℕ′ pz ps 1 ≡ ps 0 (ind-ℕ′ pz ps 0)
ind-ℕ′-βs-test1 pz ps = refl

ind-ℕ′-βs-test2 : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → ind-ℕ′ pz ps 2 ≡ ps 1 (ind-ℕ′ pz ps 1)
ind-ℕ′-βs-test2 pz ps = refl

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
    ≡⟨ cong (λ e → subst P e (proj₂ (r-ℕ xz xs (suc n)))) (ind-ℕ′-1-β-βs pz ps n) ⟩
        subst P
            (cong suc (ind-ℕ′-1-β pz ps n))
            (proj₂ (r-ℕ xz xs (suc n)))
    ≡⟨ subst-cong P (ind-ℕ′-1-β pz ps n) ⟩
        subst (P ∘ suc)
            (ind-ℕ′-1-β pz ps n)
            (proj₂ (r-ℕ xz xs (suc n)))
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

ind-ℕ′≡ind-ℕ : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′ pz ps n ≡ ind-ℕ pz ps n
ind-ℕ′≡ind-ℕ pz ps = ind-ℕ-η pz ps (ind-ℕ′ pz ps) (ind-ℕ′-βz pz ps) (ind-ℕ′-βs pz ps)
