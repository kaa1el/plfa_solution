{-# OPTIONS --without-K #-}

module plfa.demo.BisimulationProduct where

open import Data.Bool using (Bool; T; not)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import plfa.part1.Isomorphism using (_≅_; ≅-sym; _⇔_; Is-hProp; hProp-iso; ≅-Is-hProp)
open import plfa.part2.More

infix 4 _~_
infix 5 λ̇_
infixl 7 _·_
infixr 4 _,̇_

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
    _,̇_ : {Γ : Context} → {A B : Type}
        → {term₁ term₁′ : Γ ⊢ A} → {term₂ term₂′ : Γ ⊢ B}
        → term₁ ~ term₁′
        → term₂ ~ term₂′
        → (term₁ ,̇ term₂) ~ (term₁′ ,̇ term₂′)
    ṗroj₁ : {Γ : Context} → {A B : Type}
        → {term term′ : Γ ⊢ A ×̇ B}
        → term ~ term′
        → ṗroj₁ term ~ case×̇ term′ (lookup (there here))
    ṗroj₂ : {Γ : Context} → {A B : Type}
        → {term term′ : Γ ⊢ A ×̇ B}
        → term ~ term′
        → ṗroj₂ term ~ case×̇ term′ (lookup here)

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
        to (simulation₁ ,̇ simulation₂) (value-,̇ value₁₁ value₁₂) = value-,̇ (to simulation₁ value₁₁) (to simulation₂ value₁₂)

        from : {Γ : Context} → {A : Type}
            → {term₁ term₂ : Γ ⊢ A}
            → term₁ ~ term₂
            → Value term₂ → Value term₁
        from (λ̇ simulation) value-λ̇ = value-λ̇
        from (simulation₁ ,̇ simulation₂) (value-,̇ value₂₁ value₂₂) = value-,̇ (from simulation₁ value₂₁) (from simulation₂ value₂₂)

simulation-reindex-to-rebase : {Γ Δ : Context} → {A : Type}
    → {term₁ term₂ : Γ ⊢ A}
    → (ρ : {A : Type} → Γ ∋ A → Δ ∋ A)
    → term₁ ~ term₂
    → reindex-to-rebase ρ term₁ ~ reindex-to-rebase ρ term₂
simulation-reindex-to-rebase ρ lookup = lookup
simulation-reindex-to-rebase ρ (λ̇ simulation) = λ̇ simulation-reindex-to-rebase (extend-reindex ρ) simulation
simulation-reindex-to-rebase ρ (simulation₁ · simulation₂) = simulation-reindex-to-rebase ρ simulation₁ · simulation-reindex-to-rebase ρ simulation₂
simulation-reindex-to-rebase ρ (simulation₁ ,̇ simulation₂) = simulation-reindex-to-rebase ρ simulation₁ ,̇ simulation-reindex-to-rebase ρ simulation₂
simulation-reindex-to-rebase ρ (ṗroj₁ simulation) = ṗroj₁ (simulation-reindex-to-rebase ρ simulation)
simulation-reindex-to-rebase ρ (ṗroj₂ simulation) = ṗroj₂ (simulation-reindex-to-rebase ρ simulation)

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
simulation-substitute simulations (simulation₁ · simulation₂) = simulation-substitute simulations simulation₁ · simulation-substitute simulations simulation₂
simulation-substitute simulations (simulation₁ ,̇ simulation₂) = simulation-substitute simulations simulation₁ ,̇ simulation-substitute simulations simulation₂
simulation-substitute simulations (ṗroj₁ simulation) = ṗroj₁ (simulation-substitute simulations simulation)
simulation-substitute simulations (ṗroj₂ simulation) = ṗroj₂ (simulation-substitute simulations simulation)

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

open _≅_

-- case split on reduction first, then simulation
is-simulation : {Γ : Context} → {A : Type}
    → {term₁ term₂ term₁′ : Γ ⊢ A}
    → term₁ ~ term₂
    → term₁ ⟶ term₁′
    → Σ (Γ ⊢ A) (λ term₂′ → (term₁′ ~ term₂′) × (term₂ ⟶ term₂′))
is-simulation
    {term₁ = .((λ̇ term₁₁) · term₁₂)}
    {term₂ = .((λ̇ term₂₁) · term₂₂)}
    {term₁′ = .(term₁₁ [ term₁₂ ])}
    (_·_ {term₁ = .(λ̇ term₁₁)} {.(λ̇ term₂₁)} {.term₁₂} {term₂₂} (λ̇_ {term = .term₁₁} {term₂₁} simulation₁) simulation₂)
    (β-λ̇ {term₁ = term₁₁} {term₁₂} value₁₂) =
        (term₂₁ [ term₂₂ ]) , simulation-single-substitute simulation₁ simulation₂ , β-λ̇ (simulation-value-iso simulation₂ .to value₁₂)
is-simulation
    {term₁ = .(ṗroj₁ (term₁₁ ,̇ term₁₂))}
    {term₂ = .(case×̇ (term₂₁ ,̇ term₂₂) (lookup (there here)))}
    {term₁′ = .term₁₁}
    (ṗroj₁ {term = .(term₁₁ ,̇ term₁₂)} {.(term₂₁ ,̇ term₂₂)} (_,̇_ {term₁ = .term₁₁} {term₂₁} {.term₁₂} {term₂₂} simulation₁ simulation₂))
    (β-ṗroj₁ {term₁ = term₁₁} {term₁₂} value₁₁ value₁₂) =
        term₂₁ , simulation₁ , β-case×̇ (simulation-value-iso simulation₁ .to value₁₁) (simulation-value-iso simulation₂ .to value₁₂)
is-simulation
    {term₁ = .(ṗroj₂ (term₁₁ ,̇ term₁₂))}
    {term₂ = .(case×̇ (term₂₁ ,̇ term₂₂) (lookup here))}
    {term₁′ = .term₁₂}
    (ṗroj₂ {term = .(term₁₁ ,̇ term₁₂)} {.(term₂₁ ,̇ term₂₂)} (_,̇_ {term₁ = .term₁₁} {term₂₁} {.term₁₂} {term₂₂} simulation₁ simulation₂))
    (β-ṗroj₂ {term₁ = term₁₁} {term₁₂} value₁₁ value₁₂) =
        term₂₂ , simulation₂ , β-case×̇ (simulation-value-iso simulation₁ .to value₁₁) (simulation-value-iso simulation₂ .to value₁₂)
is-simulation
    {term₁ = .((term₁₁₁ · term₁₁₂) · term₁₂)}
    {term₂ = .((term₂₁₁ · term₂₁₂) · term₂₂)}
    {term₁′ = .(term₁₁′ · term₁₂)}
    (_·_ {term₁ = .(term₁₁₁ · term₁₁₂)} {.(term₂₁₁ · term₂₁₂)} {.term₁₂} {term₂₂} (_·_ {term₁ = .term₁₁₁} {term₂₁₁} {.term₁₁₂} {term₂₁₂} simulation₁₁ simulation₁₂) simulation₂)
    (ξ-·₁ {term₁ = term₁₁₁ · term₁₁₂} {term₁₁′} {term₁₂} reduction₁₁)
        with is-simulation (simulation₁₁ · simulation₁₂) reduction₁₁
... | term₂₁′ , simulation₁′ , reduction₂₁ = term₂₁′ · term₂₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₂₁
is-simulation
    {term₁ = .((ṗroj₁ term₁₁) · term₁₂)}
    {term₂ = .((case×̇ term₂₁ (lookup (there here))) · term₂₂)}
    {term₁′ = .(term₁₁′ · term₁₂)}
    (_·_ {term₁ = .(ṗroj₁ term₁₁)} {.(case×̇ term₂₁ (lookup (there here)))} {.term₁₂} {term₂₂} (ṗroj₁ {term = term₁₁} {term₂₁} simulation₁) simulation₂)
    (ξ-·₁ {term₁ = .(ṗroj₁ term₁₁)} {term₁₁′} {term₁₂} reduction₁₁)
        with is-simulation (ṗroj₁ simulation₁) reduction₁₁
... | term₂₁′ , simulation₁′ , reduction₂₁ = term₂₁′ · term₂₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₂₁
is-simulation
    {term₁ = .((ṗroj₂ term₁₁) · term₁₂)}
    {term₂ = .((case×̇ term₂₁ (lookup here)) · term₂₂)}
    {term₁′ = .(term₁₁′ · term₁₂)}
    (_·_ {term₁ = .(ṗroj₂ term₁₁)} {.(case×̇ term₂₁ (lookup here))} {.term₁₂} {term₂₂} (ṗroj₂ {term = term₁₁} {term₂₁} simulation₁) simulation₂)
    (ξ-·₁ {term₁ = .(ṗroj₂ term₁₁)} {term₁₁′} {term₁₂} reduction₁₁)
        with is-simulation (ṗroj₂ simulation₁) reduction₁₁
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
    {term₁ = .(term₁₁ ,̇ term₁₂)}
    {term₂ = .(term₂₁ ,̇ term₂₂)}
    {term₁′ = .(term₁₁′ ,̇ term₁₂)}
    (_,̇_ {term₁ = .term₁₁} {term₂₁} {.term₁₂} {term₂₂} simulation₁ simulation₂)
    (ξ-,̇₁ {term₁ = term₁₁} {term₁₁′} {term₁₂} reduction₁₁)
        with is-simulation simulation₁ reduction₁₁
... | term₂₁′ , simulation₁′ , reduction₂₁ = (term₂₁′ ,̇ term₂₂) , (simulation₁′ ,̇ simulation₂) , ξ-,̇₁ reduction₂₁
is-simulation
    {term₁ = .(term₁₁ ,̇ term₁₂)}
    {term₂ = .(term₂₁ ,̇ term₂₂)}
    {term₁′ = .(term₁₁ ,̇ term₁₂′)}
    (_,̇_ {term₁ = .term₁₁} {term₂₁} {.term₁₂} {term₂₂} simulation₁ simulation₂)
    (ξ-,̇₂ {term₁ = term₁₁} {term₁₂} {term₁₂′} value₁₁ reduction₁₂)
        with is-simulation simulation₂ reduction₁₂
... | term₂₂′ , simulation₂′ , reduction₂₂ = (term₂₁ ,̇ term₂₂′) , (simulation₁ ,̇ simulation₂′) , ξ-,̇₂ (simulation-value-iso simulation₁ .to value₁₁) reduction₂₂
is-simulation
    {term₁ = .(ṗroj₁ (term₁₁ · term₁₂))}
    {term₂ = .(case×̇ (term₂₁ · term₂₂) (lookup (there here)))}
    {term₁′ = .(ṗroj₁ term₁′)}
    (ṗroj₁ {term = .(term₁₁ · term₁₂)} {.(term₂₁ · term₂₂)} (_·_ {term₁ = term₁₁} {term₂₁} {term₁₂} {term₂₂} simulation₁ simulation₂))
    (ξ-ṗroj₁ {term = .(term₁₁ · term₁₂)} {term₁′} reduction₁)
        with is-simulation (simulation₁ · simulation₂) reduction₁
... | term₂′ , simulation′ , reduction₂ = case×̇ term₂′ (lookup (there here)) , ṗroj₁ simulation′ , ξ-case×̇ reduction₂
is-simulation
    {term₁ = .(ṗroj₁ (term₁₁ ,̇ term₁₂))}
    {term₂ = .(case×̇ (term₂₁ ,̇ term₂₂) (lookup (there here)))}
    {term₁′ = .(ṗroj₁ term₁′)}
    (ṗroj₁ {term = .(term₁₁ ,̇ term₁₂)} {.(term₂₁ ,̇ term₂₂)} (_,̇_ {term₁ = term₁₁} {term₂₁} {term₁₂} {term₂₂} simulation₁ simulation₂))
    (ξ-ṗroj₁ {term = .(term₁₁ ,̇ term₁₂)} {term₁′} reduction₁)
        with is-simulation (simulation₁ ,̇ simulation₂) reduction₁
... | term₂′ , simulation′ , reduction₂ = case×̇ term₂′ (lookup (there here)) , ṗroj₁ simulation′ , ξ-case×̇ reduction₂
is-simulation
    {term₁ = .(ṗroj₁ (ṗroj₁ term₁))}
    {term₂ = .(case×̇ (case×̇ term₂ (lookup (there here))) (lookup (there here)))}
    {term₁′ = .(ṗroj₁ term₁′)}
    (ṗroj₁ {term = .(ṗroj₁ term₁)} {.(case×̇ term₂ (lookup (there here)))} (ṗroj₁ {term = term₁} {term₂} simulation))
    (ξ-ṗroj₁ {term = .(ṗroj₁ term₁)} {term₁′} reduction₁)
        with is-simulation (ṗroj₁ simulation) reduction₁
... | term₂′ , simulation′ , reduction₂ = case×̇ term₂′ (lookup (there here)) , ṗroj₁ simulation′ , ξ-case×̇ reduction₂
is-simulation
    {term₁ = .(ṗroj₁ (ṗroj₂ term₁))}
    {term₂ = .(case×̇ (case×̇ term₂ (lookup here)) (lookup (there here)))}
    {term₁′ = .(ṗroj₁ term₁′)}
    (ṗroj₁ {term = .(ṗroj₂ term₁)} {.(case×̇ term₂ (lookup here))} (ṗroj₂ {term = term₁} {term₂} simulation))
    (ξ-ṗroj₁ {term = .(ṗroj₂ term₁)} {term₁′} reduction₁)
        with is-simulation (ṗroj₂ simulation) reduction₁
... | term₂′ , simulation′ , reduction₂ = case×̇ term₂′ (lookup (there here)) , ṗroj₁ simulation′ , ξ-case×̇ reduction₂
is-simulation
    {term₁ = .(ṗroj₂ (term₁₁ · term₁₂))}
    {term₂ = .(case×̇ (term₂₁ · term₂₂) (lookup here))}
    {term₁′ = .(ṗroj₂ term₁′)}
    (ṗroj₂ {term = .(term₁₁ · term₁₂)} {.(term₂₁ · term₂₂)} (_·_ {term₁ = term₁₁} {term₂₁} {term₁₂} {term₂₂} simulation₁ simulation₂))
    (ξ-ṗroj₂ {term = .(term₁₁ · term₁₂)} {term₁′} reduction₁)
        with is-simulation (simulation₁ · simulation₂) reduction₁
... | term₂′ , simulation′ , reduction₂ = case×̇ term₂′ (lookup here) , ṗroj₂ simulation′ , ξ-case×̇ reduction₂
is-simulation
    {term₁ = .(ṗroj₂ (term₁₁ ,̇ term₁₂))}
    {term₂ = .(case×̇ (term₂₁ ,̇ term₂₂) (lookup here))}
    {term₁′ = .(ṗroj₂ term₁′)}
    (ṗroj₂ {term = .(term₁₁ ,̇ term₁₂)} {.(term₂₁ ,̇ term₂₂)} (_,̇_ {term₁ = term₁₁} {term₂₁} {term₁₂} {term₂₂} simulation₁ simulation₂))
    (ξ-ṗroj₂ {term = .(term₁₁ ,̇ term₁₂)} {term₁′} reduction₁)
        with is-simulation (simulation₁ ,̇ simulation₂) reduction₁
... | term₂′ , simulation′ , reduction₂ = case×̇ term₂′ (lookup here) , ṗroj₂ simulation′ , ξ-case×̇ reduction₂
is-simulation
    {term₁ = .(ṗroj₂ (ṗroj₁ term₁))}
    {term₂ = .(case×̇ (case×̇ term₂ (lookup (there here))) (lookup here))}
    {term₁′ = .(ṗroj₂ term₁′)}
    (ṗroj₂ {term = .(ṗroj₁ term₁)} {.(case×̇ term₂ (lookup (there here)))} (ṗroj₁ {term = term₁} {term₂} simulation))
    (ξ-ṗroj₂ {term = .(ṗroj₁ term₁)} {term₁′} reduction₁)
        with is-simulation (ṗroj₁ simulation) reduction₁
... | term₂′ , simulation′ , reduction₂ = case×̇ term₂′ (lookup here) , ṗroj₂ simulation′ , ξ-case×̇ reduction₂
is-simulation
    {term₁ = .(ṗroj₂ (ṗroj₂ term₁))}
    {term₂ = .(case×̇ (case×̇ term₂ (lookup here)) (lookup here))}
    {term₁′ = .(ṗroj₂ term₁′)}
    (ṗroj₂ {term = .(ṗroj₂ term₁)} {.(case×̇ term₂ (lookup here))} (ṗroj₂ {term = term₁} {term₂} simulation))
    (ξ-ṗroj₂ {term = .(ṗroj₂ term₁)} {term₁′} reduction₁)
        with is-simulation (ṗroj₂ simulation) reduction₁
... | term₂′ , simulation′ , reduction₂ = case×̇ term₂′ (lookup here) , ṗroj₂ simulation′ , ξ-case×̇ reduction₂

-- case split on reduction first, then simulation
is-simulation-inv : {Γ : Context} → {A : Type}
    → {term₁ term₂ term₂′ : Γ ⊢ A}
    → term₁ ~ term₂
    → term₂ ⟶ term₂′
    → Σ (Γ ⊢ A) (λ term₁′ → (term₁′ ~ term₂′) × (term₁ ⟶ term₁′))
is-simulation-inv
    {term₁ = .((λ̇ term₁₁) · term₁₂)}
    {term₂ = .((λ̇ term₂₁) · term₂₂)}
    {term₂′ = .(term₂₁ [ term₂₂ ])}
    (_·_ {term₁ = .(λ̇ term₁₁)} {.(λ̇ term₂₁)} {term₁₂} {.term₂₂} (λ̇_ {term = term₁₁} {.term₂₁} simulation₁) simulation₂)
    (β-λ̇ {term₁ = term₂₁} {term₂₂} value₂₂) =
        term₁₁ [ term₁₂ ] , simulation-single-substitute simulation₁ simulation₂ , β-λ̇ (simulation-value-iso simulation₂ .from value₂₂)
is-simulation-inv
    {term₁ = .(ṗroj₁ (term₁₁ ,̇ term₁₂))}
    {term₂ = .(case×̇ (term₂₁ ,̇ term₂₂) (lookup (there here)))}
    {term₂′ = .term₂₁} -- lookup (there here) [ term₂₁ ][ term₂₂ ]
    (ṗroj₁ {term = .(term₁₁ ,̇ term₁₂)} {term₁′} (_,̇_ {term₁ = term₁₁} {.term₂₁} {term₁₂} {.term₂₂} simulation₁ simulation₂))
    (β-case×̇ {term₁ = term₂₁} {term₂₂} {.(lookup (there here))} value₂₁ value₂₂) =
        term₁₁ , simulation₁ , β-ṗroj₁ (simulation-value-iso simulation₁ .from value₂₁) (simulation-value-iso simulation₂ .from value₂₂)
is-simulation-inv
    {term₁ = .(ṗroj₂ (term₁₁ ,̇ term₁₂))}
    {term₂ = .(case×̇ (term₂₁ ,̇ term₂₂) (lookup here))}
    {term₂′ = .term₂₂} -- lookup here [ term₂₁ ][ term₂₂ ]
    (ṗroj₂ {term = .(term₁₁ ,̇ term₁₂)} {term₁′} (_,̇_ {term₁ = term₁₁} {.term₂₁} {term₁₂} {.term₂₂} simulation₁ simulation₂))
    (β-case×̇ {term₁ = term₂₁} {term₂₂} {.(lookup here)} value₂₁ value₂₂) =
        term₁₂ , simulation₂ , β-ṗroj₂ (simulation-value-iso simulation₁ .from value₂₁) (simulation-value-iso simulation₂ .from value₂₂)
is-simulation-inv
    {term₁ = .((term₁₁₁ · term₁₁₂) · term₁₂)}
    {term₂ = .((term₂₁₁ · term₂₁₂) · term₂₂)}
    {term₂′ = .(term₂₁′ · term₂₂)}
    (_·_ {term₁ = .(term₁₁₁ · term₁₁₂)} {.(term₂₁₁ · term₂₁₂)} {term₁₂} {.term₂₂} (_·_ {term₁ = term₁₁₁} {.term₂₁₁} {term₁₁₂} {.term₂₁₂} simulation₁₁ simulation₁₂) simulation₂)
    (ξ-·₁ {term₁ = term₂₁₁ · term₂₁₂} {term₂₁′} {term₂₂} reduction₂₁)
        with is-simulation-inv (simulation₁₁ · simulation₁₂) reduction₂₁
... | term₁₁′ , simulation₁′ , reduction₁₁ = term₁₁′ · term₁₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₁₁
is-simulation-inv
    {term₁ = .((ṗroj₁ term₁₁) · term₁₂)}
    {term₂ = .((case×̇ term₂₁ (lookup (there here))) · term₂₂)}
    {term₂′ = .(term₂₁′ · term₂₂)}
    (_·_ {term₁ = .(ṗroj₁ term₁₁)} {.(case×̇ term₂₁ (lookup (there here)))} {term₁₂} {.term₂₂} (ṗroj₁ {term = term₁₁} {term₂₁} simulation₁) simulation₂)
    (ξ-·₁ {term₁ = .(case×̇ term₂₁ (lookup (there here)))} {term₂₁′} {term₂₂} reduction₂₁)
        with is-simulation-inv (ṗroj₁ simulation₁) reduction₂₁
... | term₁₁′ , simulation₁′ , reduction₁₁ = term₁₁′ · term₁₂ , simulation₁′ · simulation₂ , ξ-·₁ reduction₁₁
is-simulation-inv
    {term₁ = .((ṗroj₂ term₁₁) · term₁₂)}
    {term₂ = .((case×̇ term₂₁ (lookup here)) · term₂₂)}
    {term₂′ = .(term₂₁′ · term₂₂)}
    (_·_ {term₁ = .(ṗroj₂ term₁₁)} {.(case×̇ term₂₁ (lookup here))} {term₁₂} {.term₂₂} (ṗroj₂ {term = term₁₁} {term₂₁} simulation₁) simulation₂)
    (ξ-·₁ {term₁ = .(case×̇ term₂₁ (lookup here))} {term₂₁′} {term₂₂} reduction₂₁)
        with is-simulation-inv (ṗroj₂ simulation₁) reduction₂₁
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
    {term₁ = .(term₁₁ ,̇ term₁₂)}
    {term₂ = .(term₂₁ ,̇ term₂₂)}
    {term₂′ = .(term₂₁′ ,̇ term₂₂)}
    (_,̇_ {term₁ = term₁₁} {.term₂₁} {term₁₂} {.term₂₂} simulation₁ simulation₂)
    (ξ-,̇₁ {term₁ = term₂₁} {term₂₁′} {term₂₂} reduction₂₁)
        with is-simulation-inv simulation₁ reduction₂₁
... | term₁₁′ , simulation₁′ , reduction₁₁ = (term₁₁′ ,̇ term₁₂) , (simulation₁′ ,̇ simulation₂) , ξ-,̇₁ reduction₁₁
is-simulation-inv
    {term₁ = .(term₁₁ ,̇ term₁₂)}
    {term₂ = .(term₂₁ ,̇ term₂₂)}
    {term₂′ = .(term₂₁ ,̇ term₂₂′)}
    (_,̇_ {term₁ = term₁₁} {.term₂₁} {term₁₂} {.term₂₂} simulation₁ simulation₂)
    (ξ-,̇₂ {term₁ = term₂₁} {term₂₂} {term₂₂′} value₂₁ reduction₂₂)
        with is-simulation-inv simulation₂ reduction₂₂
... | term₁₂′ , simulation₂′ , reduction₁₂ = (term₁₁ ,̇ term₁₂′) , (simulation₁ ,̇ simulation₂′) , ξ-,̇₂ (simulation-value-iso simulation₁ .from value₂₁) reduction₁₂
is-simulation-inv
    {term₁ = .(ṗroj₁ (term₁₁ · term₁₂))}
    {term₂ = .(case×̇ (term₂₁ · term₂₂) (lookup (there here)))}
    {term₂′ = .(case×̇ term₂′ (lookup (there here)))}
    (ṗroj₁ {term = .(term₁₁ · term₁₂)} {.(term₂₁ · term₂₂)} (_·_ {term₁ = term₁₁} {term₂₁} {term₁₂} {term₂₂} simulation₁ simulation₂))
    (ξ-case×̇ {term₁ = .(term₂₁ · term₂₂)} {term₂′} {lookup (there here)} reduction₂)
        with is-simulation-inv (simulation₁ · simulation₂) reduction₂
... | term₁′ , simulation′ , reduction₁ = ṗroj₁ term₁′ , ṗroj₁ simulation′ , ξ-ṗroj₁ reduction₁
is-simulation-inv
    {term₁ = .(ṗroj₁ (term₁₁ ,̇ term₁₂))}
    {term₂ = .(case×̇ (term₂₁ ,̇ term₂₂) (lookup (there here)))}
    {term₂′ = .(case×̇ term₂′ (lookup (there here)))}
    (ṗroj₁ {term = .(term₁₁ ,̇ term₁₂)} {.(term₂₁ ,̇ term₂₂)} (_,̇_ {term₁ = term₁₁} {term₂₁} {term₁₂} {term₂₂} simulation₁ simulation₂))
    (ξ-case×̇ {term₁ = .(term₂₁ ,̇ term₂₂)} {term₂′} {lookup (there here)} reduction₂)
        with is-simulation-inv (simulation₁ ,̇ simulation₂) reduction₂
... | term₁′ , simulation′ , reduction₁ = ṗroj₁ term₁′ , ṗroj₁ simulation′ , ξ-ṗroj₁ reduction₁
is-simulation-inv
    {term₁ = .(ṗroj₁ (ṗroj₁ term₁))}
    {term₂ = .(case×̇ (case×̇ term₂ (lookup (there here))) (lookup (there here)))}
    {term₂′ = .(case×̇ term₂′ (lookup (there here)))}
    (ṗroj₁ {term = .(ṗroj₁ term₁)} {.(case×̇ term₂ (lookup (there here)))} (ṗroj₁ {term = term₁} {term₂} simulation))
    (ξ-case×̇ {term₁ = .(case×̇ term₂ (lookup (there here)))} {term₂′} {lookup (there here)} reduction₂)
        with is-simulation-inv (ṗroj₁ simulation) reduction₂
... | term₁′ , simulation′ , reduction₁ = ṗroj₁ term₁′ , ṗroj₁ simulation′ , ξ-ṗroj₁ reduction₁
is-simulation-inv
    {term₁ = .(ṗroj₁ (ṗroj₂ term₁))}
    {term₂ = .(case×̇ (case×̇ term₂ (lookup here)) (lookup (there here)))}
    {term₂′ = .(case×̇ term₂′ (lookup (there here)))}
    (ṗroj₁ {term = .(ṗroj₂ term₁)} {.(case×̇ term₂ (lookup here))} (ṗroj₂ {term = term₁} {term₂} simulation))
    (ξ-case×̇ {term₁ = .(case×̇ term₂ (lookup here))} {term₂′} {lookup (there here)} reduction₂)
        with is-simulation-inv (ṗroj₂ simulation) reduction₂
... | term₁′ , simulation′ , reduction₁ = ṗroj₁ term₁′ , ṗroj₁ simulation′ , ξ-ṗroj₁ reduction₁
is-simulation-inv
    {term₁ = .(ṗroj₂ (term₁₁ · term₁₂))}
    {term₂ = .(case×̇ (term₂₁ · term₂₂) (lookup here))}
    {term₂′ = .(case×̇ term₂′ (lookup here))}
    (ṗroj₂ {term = .(term₁₁ · term₁₂)} {.(term₂₁ · term₂₂)} (_·_ {term₁ = term₁₁} {term₂₁} {term₁₂} {term₂₂} simulation₁ simulation₂))
    (ξ-case×̇ {term₁ = .(term₂₁ · term₂₂)} {term₂′} {lookup here} reduction₂)
        with is-simulation-inv (simulation₁ · simulation₂) reduction₂
... | term₁′ , simulation′ , reduction₁ = ṗroj₂ term₁′ , ṗroj₂ simulation′ , ξ-ṗroj₂ reduction₁
is-simulation-inv
    {term₁ = .(ṗroj₂ (term₁₁ ,̇ term₁₂))}
    {term₂ = .(case×̇ (term₂₁ ,̇ term₂₂) (lookup here))}
    {term₂′ = .(case×̇ term₂′ (lookup here))}
    (ṗroj₂ {term = .(term₁₁ ,̇ term₁₂)} {.(term₂₁ ,̇ term₂₂)} (_,̇_ {term₁ = term₁₁} {term₂₁} {term₁₂} {term₂₂} simulation₁ simulation₂))
    (ξ-case×̇ {term₁ = .(term₂₁ ,̇ term₂₂)} {term₂′} {lookup here} reduction₂)
        with is-simulation-inv (simulation₁ ,̇ simulation₂) reduction₂
... | term₁′ , simulation′ , reduction₁ = ṗroj₂ term₁′ , ṗroj₂ simulation′ , ξ-ṗroj₂ reduction₁
is-simulation-inv
    {term₁ = .(ṗroj₂ (ṗroj₁ term₁))}
    {term₂ = .(case×̇ (case×̇ term₂ (lookup (there here))) (lookup here))}
    {term₂′ = .(case×̇ term₂′ (lookup here))}
    (ṗroj₂ {term = .(ṗroj₁ term₁)} {.(case×̇ term₂ (lookup (there here)))} (ṗroj₁ {term = term₁} {term₂} simulation))
    (ξ-case×̇ {term₁ = .(case×̇ term₂ (lookup (there here)))} {term₂′} {lookup here} reduction₂)
        with is-simulation-inv (ṗroj₁ simulation) reduction₂
... | term₁′ , simulation′ , reduction₁ = ṗroj₂ term₁′ , ṗroj₂ simulation′ , ξ-ṗroj₂ reduction₁
is-simulation-inv
    {term₁ = .(ṗroj₂ (ṗroj₂ term₁))}
    {term₂ = .(case×̇ (case×̇ term₂ (lookup here)) (lookup here))}
    {term₂′ = .(case×̇ term₂′ (lookup here))}
    (ṗroj₂ {term = .(ṗroj₂ term₁)} {.(case×̇ term₂ (lookup here))} (ṗroj₂ {term = term₁} {term₂} simulation))
    (ξ-case×̇ {term₁ = .(case×̇ term₂ (lookup here))} {term₂′} {lookup here} reduction₂)
        with is-simulation-inv (ṗroj₂ simulation) reduction₂
... | term₁′ , simulation′ , reduction₁ = ṗroj₂ term₁′ , ṗroj₂ simulation′ , ξ-ṗroj₂ reduction₁
