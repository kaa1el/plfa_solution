{-# OPTIONS --without-K #-}

module plfa.part2.Bisimulation where

open import Agda.Primitive

open import Data.Bool using (Bool; T; not)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import plfa.part1.Isomorphism using (_≅_; ≅-sym; _⇔_; Is-hProp; hProp-iso; ≅-Is-hProp)
open import plfa.part2.More

private
    variable
        i j k : Level

-- Simulation

infix 4 _~_

data _~_ : {Γ : Context} → {A : Type} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
    lookup : {Γ : Context} → {A : Type}
        → {index : Γ ∋ A}
        → lookup index ~ lookup index
    λ̇_ : {Γ : Context} → {A B : Type}
        → {term term′ : Γ ‚ A ⊢ B}
        → term ~ term′
        → λ̇ term ~ λ̇ term′
    _·_ : {Γ : Context} → {A B : Type}
        → {term₁ term₁′ : Γ ⊢ A →̇ B} → {term₂ term₂′ : Γ ⊢ A}
        → term₁ ~ term₁′
        → term₂ ~ term₂′
        → term₁ · term₂ ~ term₁′ · term₂′
    l̇et : {Γ : Context} → {A B : Type} -- l̇et term₁ term₂ ~ (λ̇ term₂) · term₁ ⟶ term₂ [ term₁ ]
        → {term₁ term₁′ : Γ ⊢ A} → {term₂ term₂′ : Γ ‚ A ⊢ B}
        → term₁ ~ term₁′
        → term₂ ~ term₂′
        → l̇et term₁ term₂ ~ (λ̇ term₂′) · term₁′

-- alternative formulation

data IsInterested : {Γ : Context} → {A : Type} → (term : Γ ⊢ A) → Set where
    lookup : {Γ : Context} → {A : Type}
        → {index : Γ ∋ A}
        → IsInterested (lookup index)
    λ̇_ : {Γ : Context} → {A B : Type}
        → {term : Γ ‚ A ⊢ B}
        → IsInterested term
        → IsInterested (λ̇ term)
    _·_ : {Γ : Context} → {A B : Type}
        → {term₁ : Γ ⊢ A →̇ B} → {term₂ : Γ ⊢ A}
        → IsInterested term₁
        → IsInterested term₂
        → IsInterested (term₁ · term₂)
    l̇et : {Γ : Context} → {A B : Type}
        → {term₁ : Γ ⊢ A} → {term₂ : Γ ‚ A ⊢ B}
        → IsInterested term₁
        → IsInterested term₂
        → IsInterested (l̇et term₁ term₂)

IsInterested? : {Γ : Context} → {A : Type}
    → (term : Γ ⊢ A)
    → Dec (IsInterested term)
IsInterested? (lookup index) = yes lookup
IsInterested? (λ̇ term) with IsInterested? term
... | yes isInterested = yes (λ̇ isInterested)
... | no isNotInterested = no λ { (λ̇ isInterested) → isNotInterested isInterested }
IsInterested? (term₁ · term₂) with IsInterested? term₁ | IsInterested? term₂
... | yes isInterested₁ | yes isInterested₂ = yes (isInterested₁ · isInterested₂)
... | yes _ | no isNotInterested₂ = no λ { (_ · isInterested₂) → isNotInterested₂ isInterested₂}
... | no isNotInterested₁ | _ = no λ { (isInterested₁ · _) → isNotInterested₁ isInterested₁}
IsInterested? żero = no λ ()
IsInterested? (ṡuc term) = no λ ()
IsInterested? (caseℕ̇ term₁ term₂ term₃) = no λ ()
IsInterested? (μ̇ term) = no λ ()
IsInterested? (l̇et term₁ term₂) with IsInterested? term₁ | IsInterested? term₂
... | yes isInterested₁ | yes isInterested₂ = yes (l̇et isInterested₁ isInterested₂)
... | yes _ | no isNotInterested₂ = no λ { (l̇et _ isInterested₂) → isNotInterested₂ isInterested₂ }
... | no isNotInterested₁ | _ = no λ { (l̇et isInterested₁ _) → isNotInterested₁ isInterested₁ }
IsInterested? (prim n) = no λ ()
IsInterested? ẑero = no λ ()
IsInterested? (ŝuc term) = no λ ()
IsInterested? (term₁ +̂ term₂) = no λ ()
IsInterested? (term₁ *̂ term₂) = no λ ()
IsInterested? (case𝟘̇ term) = no λ ()
IsInterested? ṫt = no λ ()
IsInterested? (case𝟙̇ term₁ term₂) = no λ ()
IsInterested? (i̇nj₁ term) = no λ ()
IsInterested? (i̇nj₂ term) = no λ ()
IsInterested? (case+̇ term₁ term₂ term₃) = no λ ()
IsInterested? (term₁ ,̇ term₂) = no λ ()
IsInterested? (ṗroj₁ term) = no λ ()
IsInterested? (ṗroj₂ term) = no λ ()
IsInterested? (case×̇ term₁ term₂) = no λ ()
IsInterested? [̇] = no λ ()
IsInterested? (term₁ ∷̇ term₂) = no λ ()
IsInterested? (caseL̇ist term₁ term₂ term₃) = no λ ()

simulate : {Γ : Context} → {A : Type} → (term : Γ ⊢ A) → IsInterested term → (Γ ⊢ A)
simulate (lookup index) isInterested = lookup index
simulate (λ̇ term) (λ̇ isInterested) = λ̇ simulate term isInterested
simulate (term₁ · term₂) (isInterested₁ · isInterested₂) = (simulate term₁ isInterested₁) · (simulate term₂ isInterested₂)
simulate (l̇et term₁ term₂) (l̇et isInterested₁ isInterested₂) = (λ̇ simulate term₂ isInterested₂) · (simulate term₁ isInterested₁)

infix 4 _′

_′ : {Γ : Context} → {A : Type} → (term : Γ ⊢ A) → {True (IsInterested? term)} → (Γ ⊢ A)
_′ term {t} = simulate term (toWitness t)

simulate-iso : {Γ : Context} → {A : Type}
    → {term₁ term₂ : Γ ⊢ A} → {isInterested : IsInterested term₁}
    → (simulate term₁ isInterested ≡ term₂) ≅ (term₁ ~ term₂)
simulate-iso = record {
        to = to;
        from = from;
        from∘to = from∘to;
        to∘from = to∘from
    } where
        to : {Γ : Context} → {A : Type}
            → {term₁ term₂ : Γ ⊢ A} → {isInterested : IsInterested term₁}
            → simulate term₁ isInterested ≡ term₂ → term₁ ~ term₂
        to {isInterested = lookup} refl = lookup
        to {isInterested = λ̇ isInterested} refl = λ̇ to refl
        to {isInterested = isInterested₁ · isInterested₂} refl = (to refl) · (to refl)
        to {isInterested = l̇et isInterested₁ isInterested₂} refl = l̇et (to refl) (to refl)
        
        from : {Γ : Context} → {A : Type}
            → {term₁ term₂ : Γ ⊢ A} → {isInterested : IsInterested term₁}
            → term₁ ~ term₂ → simulate term₁ isInterested ≡ term₂
        from lookup = refl
        from {isInterested = λ̇ isInterested} (λ̇ simulation) = cong λ̇_ (from simulation)
        from {isInterested = isInterested₁ · isInterested₂} (simulation₁ · simulation₂) = cong₂ _·_ (from simulation₁) (from simulation₂)
        from {isInterested = l̇et isInterested₁ isInterested₂} (l̇et simulation₁ simulation₂) = cong₂ _·_ (from (λ̇ simulation₂)) (from simulation₁)

        from∘to : {Γ : Context} → {A : Type}
            → {term₁ term₂ : Γ ⊢ A} → {isInterested : IsInterested term₁}
            → (p : simulate term₁ isInterested ≡ term₂) → from (to p) ≡ p
        from∘to {isInterested = lookup} refl = refl
        from∘to {isInterested = λ̇ isInterested} refl = cong (cong λ̇_) (from∘to refl)
        from∘to {isInterested = isInterested₁ · isInterested₂} refl = cong₂ (cong₂ _·_) (from∘to refl) (from∘to refl)
        from∘to {isInterested = l̇et isInterested₁ isInterested₂} refl = cong₂ (cong₂ _·_) (cong (cong λ̇_) (from∘to refl)) (from∘to refl)

        to∘from : {Γ : Context} → {A : Type}
            → {term₁ term₂ : Γ ⊢ A} → {isInterested : IsInterested term₁}
            → (simulation : term₁ ~ term₂) → to {isInterested = isInterested} (from simulation) ≡ simulation
        to∘from {isInterested = lookup} lookup = refl
        to∘from {isInterested = λ̇ isInterested} (λ̇ simulation) with from {isInterested = isInterested} simulation | to∘from {isInterested = isInterested} simulation
        ... | refl | refl = refl
        to∘from {isInterested = isInterested₁ · isInterested₂} (simulation₁ · simulation₂)
            with
                from {isInterested = isInterested₁} simulation₁ |
                from {isInterested = isInterested₂} simulation₂ |
                to∘from {isInterested = isInterested₁} simulation₁ |
                to∘from {isInterested = isInterested₂} simulation₂
        ... | refl | refl | refl | refl = refl
        to∘from {isInterested = l̇et isInterested₁ isInterested₂} (l̇et simulation₁ simulation₂)
            with
                from {isInterested = isInterested₁} simulation₁ |
                from {isInterested = isInterested₂} simulation₂ |
                to∘from {isInterested = isInterested₁} simulation₁ |
                to∘from {isInterested = isInterested₂} simulation₂
        ... | refl | refl | refl | refl = refl

Simulation-Is-hProp : {Γ : Context} → {A : Type}
    → {term₁ term₂ : Γ ⊢ A} → {IsInterested term₁}
    → Is-hProp (term₁ ~ term₂)
Simulation-Is-hProp {term₁ = term₁} {term₂} {isInterested} = ≅-Is-hProp
    (≅-sym (simulate-iso {isInterested = isInterested}))
    (Term-Is-hSet (simulate term₁ isInterested) term₂)

-- Simulation preserves values

Value-Is-hProp : {Γ : Context} → {A : Type}
    → {term : Γ ⊢ A}
    → Is-hProp (Value term)
Value-Is-hProp value-λ̇ value-λ̇ = refl
Value-Is-hProp value-żero value-żero = refl
Value-Is-hProp (value-ṡuc value₁) (value-ṡuc value₂) = cong value-ṡuc (Value-Is-hProp value₁ value₂)
Value-Is-hProp value-prim value-prim = refl
Value-Is-hProp value-ṫt value-ṫt = refl
Value-Is-hProp (value-i̇nj₁ value₁) (value-i̇nj₁ value₂) = cong value-i̇nj₁ (Value-Is-hProp value₁ value₂)
Value-Is-hProp (value-i̇nj₂ value₁) (value-i̇nj₂ value₂) = cong value-i̇nj₂ (Value-Is-hProp value₁ value₂)
Value-Is-hProp (value-,̇ value₁₁ value₁₂) (value-,̇ value₂₁ value₂₂) = cong₂ value-,̇ (Value-Is-hProp value₁₁ value₂₁) (Value-Is-hProp value₁₂ value₂₂)
Value-Is-hProp value-[̇] value-[̇] = refl
Value-Is-hProp (value-∷̇ value₁₁ value₁₂) (value-∷̇ value₂₁ value₂₂) = cong₂ value-∷̇ (Value-Is-hProp value₁₁ value₂₁) (Value-Is-hProp value₁₂ value₂₂)

simulation-value-iso : {Γ : Context} → {A : Type}
    → {term₁ term₂ : Γ ⊢ A}
    → term₁ ~ term₂
    → Value term₁ ≅ Value term₂
simulation-value-iso simulation = hProp-iso Value-Is-hProp Value-Is-hProp (to simulation) (from simulation)
    where
        to : {Γ : Context} → {A : Type}
            → {term₁ term₂ : Γ ⊢ A}
            → term₁ ~ term₂
            → Value term₁ → Value term₂
        to (λ̇ simulation) value-λ̇ = value-λ̇

        from : {Γ : Context} → {A : Type}
            → {term₁ term₂ : Γ ⊢ A}
            → term₁ ~ term₂
            → Value term₂ → Value term₁
        from (λ̇ simulation) value-λ̇ = value-λ̇

-- Simulation commutes with reindex-to-rebase

simulation-reindex-to-rebase : {Γ Δ : Context} → {A : Type}
    → {term₁ term₂ : Γ ⊢ A}
    → (ρ : {A : Type} → Γ ∋ A → Δ ∋ A)
    → term₁ ~ term₂
    → reindex-to-rebase ρ term₁ ~ reindex-to-rebase ρ term₂
simulation-reindex-to-rebase ρ lookup = lookup
simulation-reindex-to-rebase ρ (λ̇ simulation) = λ̇ (simulation-reindex-to-rebase (extend-reindex ρ) simulation)
simulation-reindex-to-rebase ρ (simulation₁ · simulation₂) = simulation-reindex-to-rebase ρ simulation₁ · simulation-reindex-to-rebase ρ simulation₂
simulation-reindex-to-rebase ρ (l̇et simulation₁ simulation₂) = l̇et (simulation-reindex-to-rebase ρ simulation₁) (simulation-reindex-to-rebase (extend-reindex ρ) simulation₂)

-- Simulation commutes with substitution

simulation-extend : {Γ Δ : Context}
    → {σ₁ σ₂ : {A : Type} → Γ ∋ A → Δ ⊢ A}
    → ({A : Type} → (index : Γ ∋ A) → σ₁ index ~ σ₂ index)
    → {A B : Type} → (index : Γ ‚ B ∋ A) → extend σ₁ index ~ extend σ₂ index
simulation-extend simulations here = lookup
simulation-extend simulations (there index) = simulation-reindex-to-rebase there (simulations index)

simulation-substitute : {Γ Δ : Context}
    → {σ₁ σ₂ : {A : Type} → Γ ∋ A → Δ ⊢ A}
    → ({A : Type} → (index : Γ ∋ A) → σ₁ index ~ σ₂ index)
    → {A : Type} → {term₁ term₂ : Γ ⊢ A}
    → term₁ ~ term₂
    → substitute σ₁ term₁ ~ substitute σ₂ term₂
simulation-substitute simulations (lookup {index = index}) = simulations index
simulation-substitute simulations (λ̇ simulation) = λ̇ (simulation-substitute (simulation-extend simulations) simulation)
simulation-substitute simulations (simulation₁ · simulation₂) = (simulation-substitute simulations simulation₁) · (simulation-substitute simulations simulation₂)
simulation-substitute simulations (l̇et simulation₁ simulation₂) = l̇et (simulation-substitute simulations simulation₁) (simulation-substitute (simulation-extend simulations) simulation₂)

simulation-single-substitute : {Γ : Context} → {A B : Type}
    → {term₁₁ term₂₁ : Γ ‚ A ⊢ B} → {term₁₂ term₂₂ : Γ ⊢ A}
    → term₁₁ ~ term₂₁ → term₁₂ ~ term₂₂
    → term₁₁ [ term₁₂ ] ~ term₂₁ [ term₂₂ ]
simulation-single-substitute {Γ} {A} {B} {term₁₁} {term₂₁} {term₁₂} {term₂₂} simulation₁ simulation₂ = simulation-substitute simulations-σ₁ simulation₁
    where
        simulations-σ₁ : {B : Type} → (index : Γ ‚ A ∋ B) → σ₁ term₁₂ index ~ σ₁ term₂₂ index
        simulations-σ₁ here = simulation₂
        simulations-σ₁ (there index) = lookup

simulation-double-substitute : {Γ : Context} → {A B C : Type}
    → {term₁₁ term₂₁ : Γ ‚ A ‚ B ⊢ C} → {term₁₂ term₂₂ : Γ ⊢ A} → {term₁₃ term₂₃ : Γ ⊢ B}
    → term₁₁ ~ term₂₁ → term₁₂ ~ term₂₂ → term₁₃ ~ term₂₃
    → term₁₁ [ term₁₂ ][ term₁₃ ] ~ term₂₁ [ term₂₂ ][ term₂₃ ]
simulation-double-substitute {Γ} {A} {B} {C} {term₁₁} {term₂₁} {term₁₂} {term₂₂} {term₁₃} {term₂₃} simulation₁ simulation₂ simulation₃ = simulation-substitute simulations-σ₂ simulation₁
    where
        simulations-σ₂ : {C : Type} → (index : Γ ‚ A ‚ B ∋ C) → σ₂ term₁₂ term₁₃ index ~ σ₂ term₂₂ term₂₃ index
        simulations-σ₂ here = simulation₃
        simulations-σ₂ (there here) = simulation₂
        simulations-σ₂ (there (there index)) = lookup

-- The simulation relation is a lock-step simulation

open _≅_

-- is-simulation : {Γ : Context} → {A : Type}
--     → {term₁ term₂ term₁′ : Γ ⊢ A}
--     → term₁ ~ term₂
--     → term₁ ⟶ term₁′
--     → Σ (Γ ⊢ A) (λ term₂′ → (term₁′ ~ term₂′) × (term₂ ⟶ term₂′))
-- is-simulation {term₂ = (λ̇ term₂₁) · term₂₂} ((λ̇ simulation₁) · simulation₂) (β-λ̇ value₁₂) =
--     term₂₁ [ term₂₂ ] , simulation-single-substitute simulation₁ simulation₂ , β-λ̇ (simulation-value-iso simulation₂ .to value₁₂)
-- is-simulation {term₂ = (λ̇ term₂₂) · term₂₁} (l̇et simulation₁ simulation₂) (β-l̇et value₁₁) =
--     term₂₂ [ term₂₁ ] , simulation-single-substitute simulation₂ simulation₁ , β-λ̇ (simulation-value-iso simulation₁ .to value₁₁)
-- is-simulation (_·_ {term₂′ = term₂₂} (simulation₁₁ · simulation₁₂) simulation₂) (ξ-·₁ reduction₁₁) with is-simulation (simulation₁₁ · simulation₁₂) reduction₁₁
-- ... | term₂₁′ , simulation₁′ , reduction₂₁ = term₂₁′ · term₂₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₂₁
-- is-simulation (_·_ {term₂′ = term₂₂} (l̇et simulation₁₁ simulation₁₂) simulation₂) (ξ-·₁ reduction₁₁) with is-simulation (l̇et simulation₁₁ simulation₁₂) reduction₁₁
-- ... | term₂₁′ , simulation₁′ , reduction₂₁ = term₂₁′ · term₂₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₂₁
-- is-simulation ((λ̇_ {term′ = term₂₁} simulation₁) · simulation₂) (ξ-·₂ value-λ̇ reduction₁₂) with is-simulation simulation₂ reduction₁₂
-- ... | term₂₂′ , simulation₂′ , redunction₂₂ = (λ̇ term₂₁) · term₂₂′ , (λ̇ simulation₁) · simulation₂′ , ξ-·₂ value-λ̇ redunction₂₂
-- is-simulation (l̇et {term₂′ = term₂₂} simulation₁ simulation₂) (ξ-l̇et reduction₁₁) with is-simulation simulation₁ reduction₁₁
-- ... | term₂₁′ , simulation₁′ , redunction₂₁ = (λ̇ term₂₂) · term₂₁′ , l̇et simulation₁′ simulation₂ , ξ-·₂ value-λ̇ redunction₂₁

is-simulation : {Γ : Context} → {A : Type}
    → {term₁ term₂ term₁′ : Γ ⊢ A}
    → term₁ ~ term₂
    → term₁ ⟶ term₁′
    → Σ (Γ ⊢ A) (λ term₂′ → (term₁′ ~ term₂′) × (term₂ ⟶ term₂′))
is-simulation
    {term₁ = .((λ̇ term₁₁) · term₁₂)}
    {term₂ = .((λ̇ term₂₁) · term₂₂)}
    {term₁′ = .(term₁₁ [ term₁₂ ])}
    (_·_ {term₁ = .(λ̇ term₁₁)} {λ̇ term₂₁} {.term₁₂} {term₂₂} (λ̇ simulation₁) simulation₂)
    (β-λ̇ {term₁ = term₁₁} {term₁₂} value₁₂) =
        term₂₁ [ term₂₂ ] , simulation-single-substitute simulation₁ simulation₂ , β-λ̇ (simulation-value-iso simulation₂ .to value₁₂)
is-simulation
    {term₁ = .(l̇et term₁₁ term₁₂)}
    {term₂ = .((λ̇ term₂₂) · term₂₁)}
    {term₁′ = .(term₁₂ [ term₁₁ ])}
    (l̇et {term₁ = .term₁₁} {term₂₁} {.term₁₂} {term₂₂} simulation₁ simulation₂)
    (β-l̇et {term₁ = term₁₁} {term₁₂} value₁₁) =
        term₂₂ [ term₂₁ ] , simulation-single-substitute simulation₂ simulation₁ , β-λ̇ (simulation-value-iso simulation₁ .to value₁₁)
is-simulation
    {term₁ = .((term₁₁₁ · term₁₁₂) · term₁₂)}
    {term₂ = .((term₂₁₁ · term₂₁₂) · term₂₂)}
    {term₁′ = .(term₁₁′ · term₁₂)}
    (_·_ {term₁ = .(term₁₁₁ · term₁₁₂)} {.(term₂₁₁ · term₂₁₂)} {.term₁₂} {term₂₂} (_·_ {term₁ = .term₁₁₁} {term₂₁₁} {.term₁₁₂} {term₂₁₂} simulation₁₁ simulation₁₂) simulation₂)
    (ξ-·₁ {term₁ = term₁₁₁ · term₁₁₂} {term₁₁′} {term₁₂} reduction₁₁)
        with is-simulation (simulation₁₁ · simulation₁₂) reduction₁₁
... | term₂₁′ , simulation₁′ , reduction₂₁ = term₂₁′ · term₂₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₂₁
is-simulation
    {term₁ = .((l̇et term₁₁₁ term₁₁₂) · term₁₂)}
    {term₂ = .(((λ̇ term₂₁₂) · term₂₁₁) · term₂₂)}
    {term₁′ = .(term₁₁′ · term₁₂)}
    (_·_ {term₁ = .(l̇et term₁₁₁ term₁₁₂)} {.((λ̇ term₂₁₂) · term₂₁₁)} {.term₁₂} {term₂₂} (l̇et {term₁ = .term₁₁₁} {term₂₁₁} {.term₁₁₂} {term₂₁₂} simulation₁₁ simulation₁₂) simulation₂)
    (ξ-·₁ {term₁ = l̇et term₁₁₁ term₁₁₂} {term₁₁′} {term₁₂} reduction₁₁)
        with is-simulation (l̇et simulation₁₁ simulation₁₂) reduction₁₁
... | term₂₁′ , simulation₁′ , reduction₂₁ = term₂₁′ · term₂₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₂₁
is-simulation
    {term₁ = .((λ̇ term₁₁) · term₁₂)}
    {term₂ = .((λ̇ term₂₁) · term₂₂)}
    {term₁′ = .((λ̇ term₁₁) · term₁₂′)}
    (_·_ {term₁ = .(λ̇ term₁₁)} {.(λ̇ term₂₁)} {.term₁₂} {term₂₂} (λ̇_ {term = .term₁₁} {term₂₁} simulation₁) simulation₂)
    (ξ-·₂ {term₁ = .(λ̇ term₁₁)} {term₁₂} {term₁₂′} (value-λ̇ {term = term₁₁}) reduction₁₂)
        with is-simulation simulation₂ reduction₁₂
... | term₂₂′ , simulation₂′ , redunction₂₂ = (λ̇ term₂₁) · term₂₂′ , (λ̇ simulation₁) · simulation₂′ , ξ-·₂ value-λ̇ redunction₂₂
is-simulation
    {term₁ = .(l̇et term₁₁ term₁₂)}
    {term₂ = .((λ̇ term₂₂) · term₂₁)}
    {term₁′ = .(l̇et term₁₁′ term₁₂)}
    (l̇et {term₁ = .term₁₁} {term₂₁} {.term₁₂} {term₂₂} simulation₁ simulation₂)
    (ξ-l̇et {term₁ = term₁₁} {term₁₁′} {term₁₂} reduction₁₁)
        with is-simulation simulation₁ reduction₁₁
... | term₂₁′ , simulation₁′ , redunction₂₁ = (λ̇ term₂₂) · term₂₁′ , l̇et simulation₁′ simulation₂ , ξ-·₂ value-λ̇ redunction₂₁

-- is-simulation-inv : {Γ : Context} → {A : Type}
--     → {term₁ term₂ term₂′ : Γ ⊢ A}
--     → term₁ ~ term₂
--     → term₂ ⟶ term₂′
--     → Σ (Γ ⊢ A) (λ term₁′ → (term₁′ ~ term₂′) × (term₁ ⟶ term₁′))
-- is-simulation-inv {term₁ = (λ̇ term₁₁) · term₁₂} ((λ̇ simulation₁) · simulation₂) (β-λ̇ value₂₂) =
--     term₁₁ [ term₁₂ ] , simulation-single-substitute simulation₁ simulation₂ , β-λ̇ (simulation-value-iso simulation₂ .from value₂₂)
-- is-simulation-inv {term₁ = l̇et term₁₁ term₁₂} (l̇et simulation₁ simulation₂) (β-λ̇ value₂₁) =
--     term₁₂ [ term₁₁ ] , simulation-single-substitute simulation₂ simulation₁ , β-l̇et (simulation-value-iso simulation₁ .from value₂₁)
-- is-simulation-inv (_·_ {term₂ = term₁₂} (simulation₁₁ · simulation₁₂) simulation₂) (ξ-·₁ reduction₂₁) with is-simulation-inv (simulation₁₁ · simulation₁₂) reduction₂₁
-- ... | term₁₁′ , simulation₁′ , reduction₁₁ = term₁₁′ · term₁₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₁₁
-- is-simulation-inv (_·_ {term₂ = term₁₂} (l̇et simulation₁₁ simulation₁₂) simulation₂) (ξ-·₁ reduction₂₁) with is-simulation-inv (l̇et simulation₁₁ simulation₁₂) reduction₂₁
-- ... | term₁₁′ , simulation₁′ , reduction₁₁ = term₁₁′ · term₁₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₁₁
-- is-simulation-inv ((λ̇_ {term = term₁₁} simulation₁) · simulation₂) (ξ-·₂ value-λ̇ reduction₂₂) with is-simulation-inv simulation₂ reduction₂₂
-- ... | term₁₂′ , simulation₂′ , redunction₁₂ = (λ̇ term₁₁) · term₁₂′ , (λ̇ simulation₁) · simulation₂′ , ξ-·₂ value-λ̇ redunction₁₂
-- is-simulation-inv (l̇et {term₂ = term₁₂} simulation₁ simulation₂) (ξ-·₂ value-λ̇ reduction₂₁) with is-simulation-inv simulation₁ reduction₂₁
-- ... | term₁₁′ , simulation₁′ , redunction₁₁ = l̇et term₁₁′ term₁₂ , l̇et simulation₁′ simulation₂ , ξ-l̇et redunction₁₁

is-simulation-inv : {Γ : Context} → {A : Type}
    → {term₁ term₂ term₂′ : Γ ⊢ A}
    → term₁ ~ term₂
    → term₂ ⟶ term₂′
    → Σ (Γ ⊢ A) (λ term₁′ → (term₁′ ~ term₂′) × (term₁ ⟶ term₁′))
is-simulation-inv
    {term₁ = .((λ̇ term₁₁) · term₁₂)}
    {term₂ = .((λ̇ term₂₁) · term₂₂)}
    {term₂′ = .(term₂₁ [ term₂₂ ])}
    (_·_ {term₁ = λ̇ term₁₁} {.(λ̇ term₂₁)} {term₁₂} {.term₂₂} (λ̇ simulation₁) simulation₂)
    (β-λ̇ {term₁ = term₂₁} {term₂₂} value₂₂) =
        term₁₁ [ term₁₂ ] , simulation-single-substitute simulation₁ simulation₂ , β-λ̇ (simulation-value-iso simulation₂ .from value₂₂)
is-simulation-inv
    {term₁ = .(l̇et term₁₁ term₁₂)}
    {term₂ = .((λ̇ term₂₂) · term₂₁)}
    {term₂′ = .(term₂₂ [ term₂₁ ])}
    (l̇et {term₁ = term₁₁} {.term₂₁} {term₁₂} {.term₂₂} simulation₁ simulation₂)
    (β-λ̇ {term₁ = term₂₂} {term₂₁} value₂₁) =
        term₁₂ [ term₁₁ ] , simulation-single-substitute simulation₂ simulation₁ , β-l̇et (simulation-value-iso simulation₁ .from value₂₁)
is-simulation-inv
    {term₁ = .((term₁₁₁ · term₁₁₂) · term₁₂)}
    {term₂ = .((term₂₁₁ · term₂₁₂) · term₂₂)}
    {term₂′ = .(term₂₁′ · term₂₂)}
    (_·_ {term₁ = .(term₁₁₁ · term₁₁₂)} {.(term₂₁₁ · term₂₁₂)} {term₁₂} {.term₂₂} (_·_ {term₁ = term₁₁₁} {.term₂₁₁} {term₁₁₂} {.term₂₁₂} simulation₁₁ simulation₁₂) simulation₂)
    (ξ-·₁ {term₁ = term₂₁₁ · term₂₁₂} {term₂₁′} {term₂₂} reduction₂₁)
        with is-simulation-inv (simulation₁₁ · simulation₁₂) reduction₂₁
... | term₁₁′ , simulation₁′ , reduction₁₁ = term₁₁′ · term₁₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₁₁
is-simulation-inv
    {term₁ = .((l̇et term₁₁₁ term₁₁₂) · term₁₂)}
    {term₂ = .(((λ̇ term₂₁₂) · term₂₁₁) · term₂₂)}
    {term₂′ = .(term₂₁′ · term₂₂)}
    (_·_ {term₁ = .(l̇et term₁₁₁ term₁₁₂)} {.((λ̇ term₂₁₂) · term₂₁₁)} {term₁₂} {.term₂₂} (l̇et {term₁ = term₁₁₁} {.term₂₁₁} {term₁₁₂} {.term₂₁₂} simulation₁₁ simulation₁₂) simulation₂)
    (ξ-·₁ {term₁ = (λ̇ term₂₁₂) · term₂₁₁} {term₂₁′} {term₂₂} reduction₂₁)
        with is-simulation-inv (l̇et simulation₁₁ simulation₁₂) reduction₂₁
... | term₁₁′ , simulation₁′ , reduction₁₁ = term₁₁′ · term₁₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₁₁
is-simulation-inv
    {term₁ = .((λ̇ term₁₁) · term₁₂)}
    {term₂ = .((λ̇ term₂₁) · term₂₂)}
    {term₂′ = .((λ̇ term₂₁) · term₂₂′)}
    (_·_ {term₁ = .(λ̇ term₁₁)} {.(λ̇ term₂₁)} {term₁₂} {.term₂₂} (λ̇_ {term = term₁₁} {.term₂₁} simulation₁) simulation₂)
    (ξ-·₂ {term₁ = .(λ̇ term₂₁)} {term₂₂} {term₂₂′} (value-λ̇ {term = term₂₁}) reduction₂₂)
        with is-simulation-inv simulation₂ reduction₂₂
... | term₁₂′ , simulation₂′ , redunction₁₂ = (λ̇ term₁₁) · term₁₂′ , (λ̇ simulation₁) · simulation₂′ , ξ-·₂ value-λ̇ redunction₁₂
is-simulation-inv
    {term₁ = .(l̇et term₁₁ term₁₂)}
    {term₂ = .((λ̇ term₂₂) · term₂₁)}
    {term₂′ = .((λ̇ term₂₂) · term₂₁′)}
    (l̇et {term₁ = term₁₁} {.term₂₁} {term₁₂} {.term₂₂} simulation₁ simulation₂)
    (ξ-·₂ {term₁ = .(λ̇ term₂₂)} {term₂₁} {term₂₁′} (value-λ̇ {term = term₂₂}) reduction₂₁)
        with is-simulation-inv simulation₁ reduction₂₁
... | term₁₁′ , simulation₁′ , redunction₁₁ = l̇et term₁₁′ term₁₂ , l̇et simulation₁′ simulation₂ , ξ-l̇et redunction₁₁

-- Exercise: show two formulations (ṗroj₁ and ṗroj₂ vs case×̇) are in bisimulation, see BisimulationProduct.agda
