{-# OPTIONS --without-K #-}

module plfa.part2.More where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _<?_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Function using (_∘_; flip)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

infixr 7 _→̇_
infixr 8 _+̇_
infixr 9 _×̇_

data Type : Set where
    ℕ̇ : Type
    ℕ̂ : Type -- primitive natural numbers
    𝟙̇ : Type -- unit type
    𝟘̇ : Type -- empty type
    _→̇_ : Type → Type → Type
    _×̇_ : Type → Type → Type -- product type
    _+̇_ : Type → Type → Type -- sum type
    L̇ist : Type → Type -- list type

Context : Set
Context = List Type

infixl 5 _‚_ -- '‚': U+201A
pattern _‚_ Γ A = A ∷ Γ

infix 4 _∋_
data _∋_ : Context → Type → Set where
    here : {Γ : Context} → {A : Type}
        → Γ ‚ A ∋ A
    there : {Γ : Context} → {A B : Type}
        → Γ ∋ A
        → Γ ‚ B ∋ A

infix 4 _⊢_

infix 5 λ̇_
infix 5 μ̇_
infixl 7 _·_
infix 8 ṡuc_
infix 8 ŝuc_
infixl 7 _+̂_
infixl 8 _*̂_
infixr 4 _,̇_
infixr 5 _∷̇_

data _⊢_ : Context → Type → Set where
    -- variables
    ⊢lookup : {Γ : Context} → {A : Type}
        → Γ ∋ A
        → Γ ⊢ A
    -- function type
    λ̇_ : {Γ : Context} → {A B : Type} -- lambda abstraction (introdcution)
        → Γ ‚ A ⊢ B
        → Γ ⊢ A →̇ B
    _·_ : {Γ : Context} → {A B : Type} -- function application (elimination)
        → Γ ⊢ A →̇ B
        → Γ ⊢ A
        → Γ ⊢ B
    -- natural number type
    żero : {Γ : Context}
        → Γ ⊢ ℕ̇
    ṡuc_ : {Γ : Context}
        → Γ ⊢ ℕ̇
        → Γ ⊢ ℕ̇
    caseℕ̇ : {Γ : Context} → {A : Type}
        → Γ ⊢ ℕ̇
        → Γ ⊢ A
        → Γ ‚ ℕ̇ ⊢ A
        → Γ ⊢ A
    -- fixpoint operator
    μ̇_ : {Γ : Context} → {A : Type}
        → Γ ‚ A ⊢ A
        → Γ ⊢ A
    -- let binding
    l̇et : {Γ : Context} → {A B : Type}
        → Γ ⊢ A
        → Γ ‚ A ⊢ B
        → Γ ⊢ B
    -- primitive natural number type
    prim : {Γ : Context} -- primitive natural numbers
        → ℕ
        → Γ ⊢ ℕ̂
    ŝuc_ : {Γ : Context} -- primitive natural number successor
        → Γ ⊢ ℕ̂
        → Γ ⊢ ℕ̂
    _+̂_ : {Γ : Context} -- primitive natural number addition
        → Γ ⊢ ℕ̂
        → Γ ⊢ ℕ̂
        → Γ ⊢ ℕ̂
    _*̂_ : {Γ : Context} -- primitive natural number multiplication
        → Γ ⊢ ℕ̂
        → Γ ⊢ ℕ̂
        → Γ ⊢ ℕ̂
    -- empty type (initial)
    case𝟘̇ : {Γ : Context} → {A : Type} -- empty type full elimination (recursion/induction)
        → Γ ⊢ 𝟘̇
        → Γ ⊢ A
    -- unit type (terminal)
    ṫt : {Γ : Context} -- unit type introduction
        → Γ ⊢ 𝟙̇
    case𝟙̇ : {Γ : Context} → {A : Type} -- unit type full elimination (recursion/induction)
        → Γ ⊢ 𝟙̇
        → Γ ⊢ A
        → Γ ⊢ A
    -- sum type (coproduct)
    i̇nj₁ : {Γ : Context} → {A B : Type} -- product type introduction 1
        → Γ ⊢ A
        → Γ ⊢ A +̇ B
    i̇nj₂ : {Γ : Context} → {A B : Type} -- product type introduction 2
        → Γ ⊢ B
        → Γ ⊢ A +̇ B
    case+̇ : {Γ : Context} → {A B C : Type} -- product type full elimination (recursion/induction)
        → Γ ⊢ A +̇ B
        → Γ ‚ A ⊢ C
        → Γ ‚ B ⊢ C
        → Γ ⊢ C
    -- product type
    _,̇_ : {Γ : Context} → {A B : Type} -- product type introduction
        → Γ ⊢ A
        → Γ ⊢ B
        → Γ ⊢ A ×̇ B
    ṗroj₁ : {Γ : Context} → {A B : Type} -- product type elimination 1
        → Γ ⊢ A ×̇ B
        → Γ ⊢ A
    ṗroj₂ : {Γ : Context} → {A B : Type} -- product type elimination 2
        → Γ ⊢ A ×̇ B
        → Γ ⊢ B
    case×̇ : {Γ : Context} → {A B C : Type} -- product type full elimination (recursion/induction)
        → Γ ⊢ A ×̇ B
        → Γ ‚ A ‚ B ⊢ C
        → Γ ⊢ C
    -- list type
    [̇] : {Γ : Context} → {A : Type} -- list type introduction nil
        → Γ ⊢ L̇ist A
    _∷̇_ : {Γ : Context} → {A : Type} -- list type introduction cons
        → Γ ⊢ A
        → Γ ⊢ L̇ist A
        → Γ ⊢ L̇ist A
    caseL̇ist : {Γ : Context} → {A B : Type} -- list type full elimination (recursion/induction)
        → Γ ⊢ L̇ist A
        → Γ ⊢ B
        → Γ ‚ A ‚ L̇ist A ⊢ B
        → Γ ⊢ B

length : Context → ℕ
length [] = zero
length (Γ ‚ A) = suc (length Γ)

find : {Γ : Context} → {n : ℕ}
    → (n < length Γ)
    → Type
find {Γ ‚ A} {zero} (s≤s z≤n) = A
find {Γ ‚ A} {suc n} (s≤s p) = find p

count : {Γ : Context} → {n : ℕ}
    → (p : n < length Γ)
    → Γ ∋ find p
count {Γ ‚ A} {zero} (s≤s z≤n) = here
count {Γ ‚ A} {suc n} (s≤s p) = there (count p)

infix 9 #_

#_ : {Γ : Context}
    → (n : ℕ)
    → {z : True (n <? length Γ)}
    → Γ ⊢ find (toWitness z)
#_ n {z} = ⊢lookup (count (toWitness z))

extend : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ∋ A)
    → ({A B : Type} → Γ ‚ B ∋ A → Δ ‚ B ∋ A)
extend ρ here = here
extend ρ (there index) = there (ρ index)

reindex : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ∋ A)
    → ({A : Type} → Γ ⊢ A → Δ ⊢ A)
reindex ρ (⊢lookup index) = ⊢lookup (ρ index)
reindex ρ (λ̇ term) = λ̇ (reindex (extend ρ) term)
reindex ρ (term₁ · term₂) = (reindex ρ term₁) · (reindex ρ term₂)
reindex ρ żero = żero
reindex ρ (ṡuc term) = ṡuc (reindex ρ term)
reindex ρ (caseℕ̇ term₁ term₂ term₃) = caseℕ̇ (reindex ρ term₁) (reindex ρ term₂) (reindex (extend ρ) term₃)
reindex ρ (μ̇ term) = μ̇ (reindex (extend ρ) term)
reindex ρ (l̇et term₁ term₂) = l̇et (reindex ρ term₁) (reindex (extend ρ) term₂)
reindex ρ (prim n) = prim n
reindex ρ (ŝuc term) = ŝuc (reindex ρ term)
reindex ρ (term₁ +̂ term₂) = reindex ρ term₁ +̂ reindex ρ term₂
reindex ρ (term₁ *̂ term₂) = reindex ρ term₁ *̂ reindex ρ term₂
reindex ρ (case𝟘̇ term) = case𝟘̇ (reindex ρ term)
reindex ρ ṫt = ṫt
reindex ρ (case𝟙̇ term₁ term₂) = case𝟙̇ (reindex ρ term₁) (reindex ρ term₂)
reindex ρ (i̇nj₁ term) = i̇nj₁ (reindex ρ term)
reindex ρ (i̇nj₂ term) = i̇nj₂ (reindex ρ term)
reindex ρ (case+̇ term₁ term₂ term₃) = case+̇ (reindex ρ term₁) (reindex (extend ρ) term₂) (reindex (extend ρ) term₃)
reindex ρ (term₁ ,̇ term₂) = (reindex ρ term₁) ,̇ (reindex ρ term₂)
reindex ρ (ṗroj₁ term) = ṗroj₁ (reindex ρ term)
reindex ρ (ṗroj₂ term) = ṗroj₂ (reindex ρ term)
reindex ρ (case×̇ term₁ term₂) = case×̇ (reindex ρ term₁) (reindex (extend (extend ρ)) term₂)
reindex ρ [̇] = [̇]
reindex ρ (term₁ ∷̇ term₂) = reindex ρ term₁ ∷̇ reindex ρ term₂
reindex ρ (caseL̇ist term₁ term₂ term₃) = caseL̇ist (reindex ρ term₁) (reindex ρ term₂) (reindex (extend (extend ρ)) term₃)

⊢extend : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ⊢ A)
    → ({A B : Type} → Γ ‚ B ∋ A → Δ ‚ B ⊢ A)
⊢extend σ here = ⊢lookup here
⊢extend σ (there index) = reindex there (σ index)

substitute : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ⊢ A)
    → ({A : Type} → Γ ⊢ A → Δ ⊢ A)
substitute σ (⊢lookup index) = σ index
substitute σ (λ̇ term) = λ̇ substitute (⊢extend σ) term
substitute σ (term₁ · term₂) = (substitute σ term₁) · (substitute σ term₂)
substitute σ żero = żero
substitute σ (ṡuc term) = ṡuc substitute σ term
substitute σ (caseℕ̇ term₁ term₂ term₃) = caseℕ̇ (substitute σ term₁) (substitute σ term₂) (substitute (⊢extend σ) term₃)
substitute σ (μ̇ term) = μ̇ substitute (⊢extend σ) term
substitute σ (l̇et term₁ term₂) = l̇et (substitute σ term₁) (substitute (⊢extend σ) term₂)
substitute σ (prim n) = prim n
substitute σ (ŝuc term) = ŝuc (substitute σ term)
substitute σ (term₁ +̂ term₂) = substitute σ term₁ +̂ substitute σ term₂
substitute σ (term₁ *̂ term₂) = substitute σ term₁ *̂ substitute σ term₂
substitute σ (case𝟘̇ term) = case𝟘̇ (substitute σ term)
substitute σ ṫt = ṫt
substitute σ (case𝟙̇ term₁ term₂) = case𝟙̇ (substitute σ term₁) (substitute σ term₂)
substitute σ (i̇nj₁ term) = i̇nj₁ (substitute σ term)
substitute σ (i̇nj₂ term) = i̇nj₂ (substitute σ term)
substitute σ (case+̇ term₁ term₂ term₃) = case+̇ (substitute σ term₁) (substitute (⊢extend σ) term₂) (substitute (⊢extend σ) term₃)
substitute σ (term₁ ,̇ term₂) = (substitute σ term₁) ,̇ (substitute σ term₂)
substitute σ (ṗroj₁ term) = ṗroj₁ (substitute σ term)
substitute σ (ṗroj₂ term) = ṗroj₂ (substitute σ term)
substitute σ (case×̇ term₁ term₂) = case×̇ (substitute σ term₁) (substitute (⊢extend (⊢extend σ)) term₂)
substitute σ [̇] = [̇]
substitute σ (term₁ ∷̇ term₂) = substitute σ term₁ ∷̇ substitute σ term₂
substitute σ (caseL̇ist term₁ term₂ term₃) = caseL̇ist (substitute σ term₁) (substitute σ term₂) (substitute (⊢extend (⊢extend σ)) term₃)

_[_] : {Γ : Context} → {A B : Type}
    → Γ ‚ A ⊢ B
    → Γ ⊢ A
    → Γ ⊢ B
_[_] {Γ} {A} {B} term₁ term₂ = substitute {Γ ‚ A} {Γ} σ term₁ where
    σ : {B : Type} → Γ ‚ A ∋ B → Γ ⊢ B
    σ here = term₂
    σ (there index) = ⊢lookup index

_[_][_] : {Γ : Context} → {A B C : Type}
    → Γ ‚ A ‚ B ⊢ C
    → Γ ⊢ A
    → Γ ⊢ B
    → Γ ⊢ C
_[_][_] {Γ} {A} {B} {C} term₁ term₂ term₃ = substitute {Γ ‚ A ‚ B} {Γ} σ term₁ where
    σ : {C : Type} → Γ ‚ A ‚ B ∋ C → Γ ⊢ C
    σ here = term₃
    σ (there here) = term₂
    σ (there (there index)) = ⊢lookup index

-- double-substitute : {Γ : Context} → {A B C : Type}
--     → (term₁ : Γ ‚ A ‚ B ⊢ C)
--     → (term₂ : Γ ⊢ A)
--     → (term₃ : Γ ⊢ B)
--     → term₁ [ term₂ ][ term₃ ] ≡ term₁ [ reindex there term₃ ] [ term₂ ]
-- double-substitute {Γ} {A} {B} {C} term₁ term₂ term₃ = ?

data Value : {Γ : Context} → {A : Type} → Γ ⊢ A → Set where
    value-λ̇ : {Γ : Context} → {A B : Type} → {term : Γ ‚ A ⊢ B}
        → Value (λ̇ term)
    value-żero : {Γ : Context}
        → Value (żero {Γ})
    value-ṡuc : {Γ : Context} → {term : Γ ⊢ ℕ̇}
        → Value term
        → Value (ṡuc term)
    value-prim : {Γ : Context} → {n : ℕ}
        → Value (prim {Γ} n)
    value-ṫt : {Γ : Context}
        → Value (ṫt {Γ})
    value-i̇nj₁ : {Γ : Context} → {A B : Type} → {term₁ : Γ ⊢ A}
        → Value term₁
        → Value (i̇nj₁ {Γ} {A} {B} term₁)
    value-i̇nj₂ : {Γ : Context} → {A B : Type} → {term₂ : Γ ⊢ B}
        → Value term₂
        → Value (i̇nj₂ {Γ} {A} {B} term₂)
    value-,̇ : {Γ : Context} → {A B : Type} → {term₁ : Γ ⊢ A} → {term₂ : Γ ⊢ B}
        → Value term₁
        → Value term₂
        → Value (term₁ ,̇ term₂)
    value-[̇] : {Γ : Context} → {A : Type}
        → Value ([̇] {Γ} {A})
    value-∷̇ : {Γ : Context} → {A : Type} → {term₁ : Γ ⊢ A} → {term₂ : Γ ⊢ L̇ist A}
        → Value term₁
        → Value term₂
        → Value (term₁ ∷̇ term₂)

infix 2 _⟶_

data _⟶_ : {Γ : Context} → {A : Type} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
    -- beta rules
    β-λ̇ : {Γ : Context} → {A B : Type}
        → {term₁ : Γ ‚ A ⊢ B} → {term₂ : Γ ⊢ A}
        → Value term₂
        → (λ̇ term₁) · term₂ ⟶ term₁ [ term₂ ] -- call by value reduction (another choice is call by name)
    β-żero : {Γ : Context} → {A : Type}
        → {term₂ : Γ ⊢ A} → {term₃ : Γ ‚ ℕ̇ ⊢ A}
        → caseℕ̇ żero term₂ term₃ ⟶ term₂
    β-ṡuc : {Γ : Context} → {A : Type}
        → {term₁ : Γ ⊢ ℕ̇} → {term₂ : Γ ⊢ A} → {term₃ : Γ ‚ ℕ̇ ⊢ A}
        → Value term₁
        → caseℕ̇ (ṡuc term₁) term₂ term₃ ⟶ term₃ [ term₁ ]
    β-μ̇ : {Γ : Context} → {A : Type}
        → {term : Γ ‚ A ⊢ A}
        → μ̇ term ⟶ term [ μ̇ term ]
    β-l̇et : {Γ : Context} → {A B : Type} -- l̇et term₁ term₂ ≡ term₂ [ term₁ ] ≡ (λ̇ term₂) · term₁
        → {term₁ : Γ ⊢ A} → {term₂ : Γ ‚ A ⊢ B}
        → Value term₁
        → l̇et term₁ term₂ ⟶ term₂ [ term₁ ]
    β-case𝟙̇ : {Γ : Context} → {A : Type}
        → {term : Γ ⊢ A}
        → case𝟙̇ ṫt term ⟶ term
    β-i̇nj₁ : {Γ : Context} → {A B C : Type}
        → {term₁ : Γ ⊢ A} → {term₃ : Γ ‚ A ⊢ C} → {term₄ : Γ ‚ B ⊢ C}
        → Value term₁
        → case+̇ (i̇nj₁ term₁) term₃ term₄ ⟶ term₃ [ term₁ ]
    β-i̇nj₂ : {Γ : Context} → {A B C : Type}
        → {term₂ : Γ ⊢ B} → {term₃ : Γ ‚ A ⊢ C} → {term₄ : Γ ‚ B ⊢ C}
        → Value term₂
        → case+̇ (i̇nj₂ term₂) term₃ term₄ ⟶ term₄ [ term₂ ]
    β-ṗroj₁ : {Γ : Context} → {A B : Type}
        → {term₁ : Γ ⊢ A} → {term₂ : Γ ⊢ B}
        → Value term₁
        → Value term₂
        → ṗroj₁ (term₁ ,̇ term₂) ⟶ term₁
    β-ṗroj₂ : {Γ : Context} → {A B : Type}
        → {term₁ : Γ ⊢ A} → {term₂ : Γ ⊢ B}
        → Value term₁
        → Value term₂
        → ṗroj₂ (term₁ ,̇ term₂) ⟶ term₂
    β-case×̇ : {Γ : Context} → {A B C : Type}
        → {term₁ : Γ ⊢ A} → {term₂ : Γ ⊢ B} → {term₃ : Γ ‚ A ‚ B ⊢ C}
        → Value term₁
        → Value term₂
        → case×̇ (term₁ ,̇ term₂) term₃ ⟶ term₃ [ term₁ ][ term₂ ]
    β-[̇] : {Γ : Context} → {A B : Type}
        → {term₂ : Γ ⊢ B} → {term₃ : Γ ‚ A ‚ L̇ist A ⊢ B}
        → caseL̇ist [̇] term₂ term₃ ⟶ term₂
    β-∷̇ : {Γ : Context} → {A B : Type}
        → {term₁ : Γ ⊢ A} → {term₂ : Γ ⊢ L̇ist A} → {term₃ : Γ ⊢ B} → {term₄ : Γ ‚ A ‚ L̇ist A ⊢ B}
        → Value term₁
        → Value term₂
        → caseL̇ist (term₁ ∷̇ term₂) term₃ term₄ ⟶ term₄ [ term₁ ][ term₂ ]
    -- delta rules (primitive types)
    δ-ŝuc : {Γ : Context} → {n : ℕ}
        → ŝuc (prim {Γ} n) ⟶ prim (suc n)
    δ-+̂ : {Γ : Context} → {n m : ℕ}
        → (prim {Γ} n) +̂ (prim m) ⟶ prim (n + m)
    δ-*̂ : {Γ : Context} → {n m : ℕ}
        → (prim {Γ} n) *̂ (prim m) ⟶ prim (n * m)
    -- xi rules (compatibility)
    ξ-·₁ : {Γ : Context} → {A B : Type}
        → {term₁ term₁′ : Γ ⊢ A →̇ B} → {term₂ : Γ ⊢ A}
        → term₁ ⟶ term₁′
        → term₁ · term₂ ⟶ term₁′ · term₂
    ξ-·₂ : {Γ : Context} → {A B : Type}
        → {term₁ : Γ ⊢ A →̇ B} → {term₂ term₂′ : Γ ⊢ A}
        → Value term₁
        → term₂ ⟶ term₂′
        → term₁ · term₂ ⟶ term₁ · term₂′ -- this reduction strategy is done left to right
    ξ-ṡuc : {Γ : Context}
        → {term term′ : Γ ⊢ ℕ̇}
        → term ⟶ term′
        → ṡuc term ⟶ ṡuc term′
    ξ-caseℕ̇ : {Γ : Context} → {A : Type}
        → {term₁ term₁′ : Γ ⊢ ℕ̇} → {term₂ : Γ ⊢ A} → {term₃ : Γ ‚ ℕ̇ ⊢ A}
        → term₁ ⟶ term₁′
        → caseℕ̇ term₁ term₂ term₃ ⟶ caseℕ̇ term₁′ term₂ term₃
    ξ-l̇et : {Γ : Context} → {A B : Type}
        → {term₁ term₁′ : Γ ⊢ A} → {term₂ : Γ ‚ A ⊢ B}
        → term₁ ⟶ term₁′
        → l̇et term₁ term₂ ⟶ l̇et term₁′ term₂
    ξ-ŝuc : {Γ : Context}
        → {term term′ : Γ ⊢ ℕ̂}
        → term ⟶ term′
        → ŝuc term ⟶ ŝuc term′
    ξ-+̂₁ : {Γ : Context}
        → {term₁ term₁′ term₂ : Γ ⊢ ℕ̂}
        → term₁ ⟶ term₁′
        → term₁ +̂ term₂ ⟶ term₁′ +̂ term₂
    ξ-+̂₂ : {Γ : Context}
        → {term₁ term₂ term₂′ : Γ ⊢ ℕ̂}
        → Value term₁
        → term₂ ⟶ term₂′
        → term₁ +̂ term₂ ⟶ term₁ +̂ term₂′
    ξ-*̂₁ : {Γ : Context}
        → {term₁ term₁′ term₂ : Γ ⊢ ℕ̂}
        → term₁ ⟶ term₁′
        → term₁ *̂ term₂ ⟶ term₁′ *̂ term₂
    ξ-*̂₂ : {Γ : Context}
        → {term₁ term₂ term₂′ : Γ ⊢ ℕ̂}
        → Value term₁
        → term₂ ⟶ term₂′
        → term₁ *̂ term₂ ⟶ term₁ *̂ term₂′
    ξ-case𝟘̇ : {Γ : Context} → {A : Type}
        → {term term′ : Γ ⊢ 𝟘̇}
        → term ⟶ term′
        → case𝟘̇ {Γ} {A} term ⟶ case𝟘̇ term′
    ξ-case𝟙̇ : {Γ : Context} → {A : Type}
        → {term₁ term₁′ : Γ ⊢ 𝟙̇} → {term₂ : Γ ⊢ A}
        → term₁ ⟶ term₁′
        → case𝟙̇ term₁ term₂ ⟶ case𝟙̇ term₁′ term₂
    ξ-i̇nj₁ : {Γ : Context} → {A B : Type}
        → {term₁ term₁′ : Γ ⊢ A}
        → term₁ ⟶ term₁′
        → i̇nj₁ {Γ} {A} {B} term₁ ⟶ i̇nj₁ term₁′
    ξ-i̇nj₂ : {Γ : Context} → {A B : Type}
        → {term₂ term₂′ : Γ ⊢ B}
        → term₂ ⟶ term₂′
        → i̇nj₂ {Γ} {A} {B} term₂ ⟶ i̇nj₂ term₂′
    ξ-case+̇ : {Γ : Context} → {A B C : Type}
        → {term₁ term₁′ : Γ ⊢ A +̇ B} → {term₂ : Γ ‚ A ⊢ C} → {term₃ : Γ ‚ B ⊢ C}
        → term₁ ⟶ term₁′
        → case+̇ term₁ term₂ term₃ ⟶ case+̇ term₁′ term₂ term₃
    ξ-,̇₁ : {Γ : Context} → {A B : Type}
        → {term₁ term₁′ : Γ ⊢ A} → {term₂ : Γ ⊢ B}
        → term₁ ⟶ term₁′
        → term₁ ,̇ term₂ ⟶ term₁′ ,̇ term₂
    ξ-,̇₂ : {Γ : Context} → {A B : Type}
        → {term₁ : Γ ⊢ A} → {term₂ term₂′ : Γ ⊢ B}
        → Value term₁
        → term₂ ⟶ term₂′
        → term₁ ,̇ term₂ ⟶ term₁ ,̇ term₂′
    ξ-ṗroj₁ : {Γ : Context} → {A B : Type}
        → {term term′ : Γ ⊢ A ×̇ B}
        → term ⟶ term′
        → ṗroj₁ term ⟶ ṗroj₁ term′
    ξ-ṗroj₂ : {Γ : Context} → {A B : Type}
        → {term term′ : Γ ⊢ A ×̇ B}
        → term ⟶ term′
        → ṗroj₂ term ⟶ ṗroj₂ term′
    ξ-case×̇ : {Γ : Context} → {A B C : Type}
        → {term₁ term₁′ : Γ ⊢ A ×̇ B} → {term₂ : Γ ‚ A ‚ B ⊢ C}
        → term₁ ⟶ term₁′
        → case×̇ term₁ term₂ ⟶ case×̇ term₁′ term₂
    ξ-∷̇₁ : {Γ : Context} → {A : Type}
        → {term₁ term₁′ : Γ ⊢ A} → {term₂ : Γ ⊢ L̇ist A}
        → term₁ ⟶ term₁′
        → term₁ ∷̇ term₂ ⟶ term₁′ ∷̇ term₂
    ξ-∷̇₂ : {Γ : Context} → {A : Type}
        → {term₁ : Γ ⊢ A} → {term₂ term₂′ : Γ ⊢ L̇ist A}
        → Value term₁
        → term₂ ⟶ term₂′
        → term₁ ∷̇ term₂ ⟶ term₁ ∷̇ term₂′
    ξ-caseL̇ist : {Γ : Context} → {A B : Type}
        → {term₁ term₁′ : Γ ⊢ L̇ist A} → {term₂ : Γ ⊢ B} → {term₃ : Γ ‚ A ‚ L̇ist A ⊢ B}
        → term₁ ⟶ term₁′
        → caseL̇ist term₁ term₂ term₃ ⟶ caseL̇ist term₁′ term₂ term₃

infix 2 _⟶⋆_
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3 _∎

data _⟶⋆_ {Γ : Context} {A : Type} : (Γ ⊢ A) → (Γ ⊢ A) → Set where
    _∎ : (term : Γ ⊢ A)
        → term ⟶⋆ term
    _⟶⟨_⟩_ : (term₁ : Γ ⊢ A) → {term₂ term₃ : Γ ⊢ A}
        → term₁ ⟶ term₂
        → term₂ ⟶⋆ term₃
        → term₁ ⟶⋆ term₃

begin_ : {Γ : Context} → {A : Type}
    → {term₁ term₂ : Γ ⊢ A}
    → term₁ ⟶⋆ term₂
    → term₁ ⟶⋆ term₂
begin ps = ps

¬[value×reducible] : {Γ : Context} → {A : Type}
    → {term₁ term₂ : Γ ⊢ A}
    → Value term₁
    → ¬ (term₁ ⟶ term₂)
¬[value×reducible] (value-ṡuc value) (ξ-ṡuc reduction) = ¬[value×reducible] value reduction
¬[value×reducible] (value-i̇nj₁ value) (ξ-i̇nj₁ reduction) = ¬[value×reducible] value reduction
¬[value×reducible] (value-i̇nj₂ value) (ξ-i̇nj₂ reduction) = ¬[value×reducible] value reduction
¬[value×reducible] (value-,̇ value₁ value₂) (ξ-,̇₁ reduction) = ¬[value×reducible] value₁ reduction
¬[value×reducible] (value-,̇ value₁ value₂) (ξ-,̇₂ value₁′ reduction) = ¬[value×reducible] value₂ reduction
¬[value×reducible] (value-∷̇ value₁ value₂) (ξ-∷̇₁ reduction) = ¬[value×reducible] value₁ reduction
¬[value×reducible] (value-∷̇ value₁ value₂) (ξ-∷̇₂ value₁′ reduction) = ¬[value×reducible] value₂ reduction

¬[reducible×value] : {Γ : Context} → {A : Type}
    → {term₁ term₂ : Γ ⊢ A}
    → term₁ ⟶ term₂
    → ¬ Value term₁
¬[reducible×value] = flip ¬[value×reducible]

data Progress {A : Type} (term : [] ⊢ A) : Set where
    step : {term′ : [] ⊢ A}
        → term ⟶ term′
        → Progress term
    done : Value term
        → Progress term

progress : {A : Type}
    → (term : [] ⊢ A)
    → Progress term
progress (λ̇ term) = done value-λ̇
progress (term₁ · term₂) with progress term₁
... | step reduction₁ = step (ξ-·₁ reduction₁)
... | done value-λ̇ with progress term₂
...     | step reduction₂ = step (ξ-·₂ value-λ̇ reduction₂)
...     | done value₂ = step (β-λ̇ value₂)
progress żero = done value-żero
progress (ṡuc term) with progress term
... | step reduction = step (ξ-ṡuc reduction)
... | done value = done (value-ṡuc value)
progress (caseℕ̇ term₁ term₂ term₃) with progress term₁
... | step reduction₁ = step (ξ-caseℕ̇ reduction₁)
... | done value-żero = step β-żero
... | done (value-ṡuc value₁) = step (β-ṡuc value₁)
progress (μ̇ term) = step β-μ̇
progress (l̇et term₁ term₂) with progress term₁
... | step reduction₁ = step (ξ-l̇et reduction₁)
... | done value₁ = step (β-l̇et value₁)
progress (prim n) = done value-prim
progress (ŝuc term) with progress term
... | step reduction = step (ξ-ŝuc reduction)
... | done value-prim = step δ-ŝuc
progress (term₁ +̂ term₂) with progress term₁
... | step reduction₁ = step (ξ-+̂₁ reduction₁)
... | done value-prim with progress term₂
...     | step reduction₂ = step (ξ-+̂₂ value-prim reduction₂)
...     | done value-prim = step δ-+̂
progress (term₁ *̂ term₂) with progress term₁
... | step reduction₁ = step (ξ-*̂₁ reduction₁)
... | done value-prim with progress term₂
...     | step reduction₂ = step (ξ-*̂₂ value-prim reduction₂)
...     | done value-prim = step δ-*̂
progress (case𝟘̇ term) with progress term
... | step reduction = step (ξ-case𝟘̇ reduction)
progress ṫt = done value-ṫt
progress (case𝟙̇ term₁ term₂) with progress term₁
... | step reduction₁ = step (ξ-case𝟙̇ reduction₁)
... | done value-ṫt = step β-case𝟙̇
progress (i̇nj₁ term₁) with progress term₁
... | step reduction₁ = step (ξ-i̇nj₁ reduction₁)
... | done value₁ = done (value-i̇nj₁ value₁)
progress (i̇nj₂ term₂) with progress term₂
... | step reduction₂ = step (ξ-i̇nj₂ reduction₂)
... | done value₂ = done (value-i̇nj₂ value₂)
progress (case+̇ term₁ term₂ term₃) with progress term₁
... | step reduction₁ = step (ξ-case+̇ reduction₁)
... | done (value-i̇nj₁ value₁) = step (β-i̇nj₁ value₁)
... | done (value-i̇nj₂ value₁) = step (β-i̇nj₂ value₁)
progress (term₁ ,̇ term₂) with progress term₁
... | step reduction₁ = step (ξ-,̇₁ reduction₁)
... | done value₁ with progress term₂
...     | step reduction₂ = step (ξ-,̇₂ value₁ reduction₂)
...     | done value₂ = done (value-,̇ value₁ value₂)
progress (ṗroj₁ term) with progress term
... | step reduction = step (ξ-ṗroj₁ reduction)
... | done (value-,̇ value₁ value₂) = step (β-ṗroj₁ value₁ value₂)
progress (ṗroj₂ term) with progress term
... | step reduction = step (ξ-ṗroj₂ reduction)
... | done (value-,̇ value₁ value₂) = step (β-ṗroj₂ value₁ value₂)
progress (case×̇ term₁ term₂) with progress term₁
... | step reduction₁ = step (ξ-case×̇ reduction₁)
... | done (value-,̇ value₁ value₂) = step (β-case×̇ value₁ value₂)
progress [̇] = done value-[̇]
progress (term₁ ∷̇ term₂) with progress term₁
... | step reduction₁ = step (ξ-∷̇₁ reduction₁)
... | done value₁ with progress term₂
...     | step reduction₂ = step (ξ-∷̇₂ value₁ reduction₂)
...     | done value₂ = done (value-∷̇ value₁ value₂)
progress (caseL̇ist term₁ term₂ term₃) with progress term₁
... | step reduction₁ = step (ξ-caseL̇ist reduction₁)
... | done value-[̇] = step β-[̇]
... | done (value-∷̇ value₁ value₂) = step (β-∷̇ value₁ value₂)

value? : {A : Type}
    → (term : [] ⊢ A)
    → Dec (Value term)
value? term with progress term
... | step reduction = no (¬[reducible×value] reduction)
... | done value = yes value
-- value? typing with progress typing
-- ... | step p = no (¬[reducible×value] p)
-- ... | done value = yes value

record Gas : Set where
    constructor gas
    field
        amount : ℕ

data Finished {Γ : Context} {A : Type} (term : Γ ⊢ A) : Set where
    done : Value term → Finished term
    out-of-gas : Finished term

data Steps {A : Type} (term : [] ⊢ A) : Set where
    steps : {term′ : [] ⊢ A}
        → term ⟶⋆ term′
        → Finished term′
        → Steps term

eval : {A : Type} → Gas
    → (term : [] ⊢ A)
    → Steps term
eval (gas zero) term = steps (term ∎) out-of-gas
eval (gas (suc amount)) term with progress term
... | done value = steps (term ∎) (done value)
... | step {term′} reduction with eval (gas amount) term′
...     | steps reductions finished = steps (term ⟶⟨ reduction ⟩ reductions) finished

cube : [] ⊢ ℕ̂ →̇ ℕ̂
cube = λ̇ # 0 *̂ # 0 *̂ # 0

test : [] ⊢ ℕ̂ →̇ ℕ̂ →̇ ℕ̂ →̇ ℕ̂
test = λ̇ λ̇ λ̇ ŝuc (# 2 *̂ # 1 +̂ # 0)

_ : cube · (prim 2) ⟶⋆ (prim 8)
_ = begin
        cube · (prim 2)
    ⟶⟨ β-λ̇ value-prim ⟩
        (prim 2) *̂ (prim 2) *̂ (prim 2)
    ⟶⟨ ξ-*̂₁ δ-*̂ ⟩
        (prim 4) *̂ (prim 2)
    ⟶⟨ δ-*̂ ⟩
        prim 8
    ∎

exp10 : [] ⊢ ℕ̂ →̇ ℕ̂
exp10 = λ̇ (l̇et (# 0 *̂ # 0) (l̇et (# 0 *̂ # 0) (l̇et (# 0 *̂ # 2) (# 0 *̂ # 0))))

_ : exp10 · (prim 2) ⟶⋆ (prim 1024)
_ = begin
        exp10 · prim 2
    ⟶⟨ β-λ̇ value-prim ⟩
        l̇et (prim 2 *̂ prim 2) (l̇et (# 0 *̂ # 0) (l̇et (# 0 *̂ prim 2) (# 0 *̂ # 0)))
    ⟶⟨ ξ-l̇et δ-*̂ ⟩
        l̇et (prim 4) (l̇et (# 0 *̂ # 0) (l̇et (# 0 *̂ prim 2) (# 0 *̂ # 0)))
    ⟶⟨ β-l̇et value-prim ⟩
        l̇et (prim 4 *̂ prim 4) (l̇et (# 0 *̂ prim 2) (# 0 *̂ # 0))
    ⟶⟨ ξ-l̇et δ-*̂ ⟩
        l̇et (prim 16) (l̇et (# 0 *̂ prim 2) (# 0 *̂ # 0))
    ⟶⟨ β-l̇et value-prim ⟩
        l̇et (prim 16 *̂ prim 2) (# 0 *̂ # 0)
    ⟶⟨ ξ-l̇et δ-*̂ ⟩
        l̇et (prim 32) (# 0 *̂ # 0)
    ⟶⟨ β-l̇et value-prim ⟩
        prim 32 *̂ prim 32
    ⟶⟨ δ-*̂ ⟩
        prim 1024
    ∎

swap×̇ : {A B : Type} → [] ⊢ A ×̇ B →̇ B ×̇ A
swap×̇ = λ̇ (ṗroj₂ (# 0) ,̇ ṗroj₁ (# 0))

_ : swap×̇ · (prim 42 ,̇ żero) ⟶⋆ (żero ,̇ prim 42)
_ = begin
        swap×̇ · (prim 42 ,̇ żero)
    ⟶⟨ β-λ̇ (value-,̇ value-prim value-żero) ⟩
        ṗroj₂ (prim 42 ,̇ żero) ,̇ ṗroj₁ (prim 42 ,̇ żero)
    ⟶⟨ ξ-,̇₁ (β-ṗroj₂ value-prim value-żero) ⟩
        żero ,̇ ṗroj₁ (prim 42 ,̇ żero)
    ⟶⟨ ξ-,̇₂ value-żero (β-ṗroj₁ value-prim value-żero) ⟩
        żero ,̇ prim 42
    ∎

swap×̇′ : {A B : Type} → [] ⊢ A ×̇ B →̇ B ×̇ A
swap×̇′ = λ̇ case×̇ (# 0) (# 0 ,̇ # 1)

_ : swap×̇′ · (prim 42 ,̇ żero) ⟶⋆ (żero ,̇ prim 42)
_ = begin
        swap×̇′ · (prim 42 ,̇ żero)
    ⟶⟨ β-λ̇ (value-,̇ value-prim value-żero) ⟩
        case×̇ (prim 42 ,̇ żero) (# 0 ,̇ # 1)
    ⟶⟨ β-case×̇ value-prim value-żero ⟩
        żero ,̇ prim 42
    ∎

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇
_ = # 0

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
_ = # 1

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇
_ = # 1 · # 0

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇
_ = # 1 · (# 1 · # 0)

_ : [] ‚ ℕ̇ →̇ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
_ = λ̇ (# 1 · (# 1 · # 0))

_ : [] ⊢ (ℕ̇ →̇ ℕ̇) →̇ ℕ̇ →̇ ℕ̇
_ = λ̇ λ̇ (# 1 · (# 1 · # 0))

ȯne : {Γ : Context}
    → Γ ⊢ ℕ̇
ȯne = ṡuc żero

ṫwo : {Γ : Context}
    → Γ ⊢ ℕ̇
ṫwo = ṡuc ȯne

ṫhree : {Γ : Context}
    → Γ ⊢ ℕ̇
ṫhree = ṡuc ṫwo

ȧdd : {Γ : Context}
    → Γ ⊢ ℕ̇ →̇ ℕ̇ →̇ ℕ̇
ȧdd = μ̇ λ̇ λ̇ caseℕ̇ (# 1) (# 0) (ṡuc (# 3 · # 0 · # 1))

ṁul : {Γ : Context}
    → Γ ⊢ ℕ̇ →̇ ℕ̇ →̇ ℕ̇
ṁul = μ̇ λ̇ λ̇ caseℕ̇ (# 1) żero (ȧdd · # 1 · (# 3 · # 0 · # 1))

ėxp : {Γ : Context}
    → Γ ⊢ ℕ̇ →̇ ℕ̇ →̇ ℕ̇
ėxp = μ̇ λ̇ λ̇ caseℕ̇ (# 0) ȯne (ṁul · # 2 · (# 3 · # 2 · # 0))

λ̇ṡuc : {Γ : Context}
    → Γ ⊢ ℕ̇ →̇ ℕ̇
λ̇ṡuc = λ̇ ṡuc # 0

2+2 : {Γ : Context}
    → Γ ⊢ ℕ̇
2+2 = ȧdd · ṫwo · ṫwo

2*2 : {Γ : Context}
    → Γ ⊢ ℕ̇
2*2 = ṁul · ṫwo · ṫwo

Church : Type → Type
Church A = (A →̇ A) →̇ (A →̇ A)

żeroᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ Church A
żeroᶜ = λ̇ λ̇ # 0

ȯneᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ Church A
ȯneᶜ = λ̇ λ̇ # 1 · # 0

ṫwoᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ Church A
ṫwoᶜ = λ̇ λ̇ # 1 · (# 1 · # 0)

ṫhreeᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ Church A
ṫhreeᶜ = λ̇ λ̇ # 1 · (# 1 · (# 1 · # 0))

ȧddᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ Church A →̇ Church A →̇ Church A
ȧddᶜ = λ̇ λ̇ λ̇ λ̇ # 3 · # 1 · (# 2 · # 1 · # 0)

ṁulᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ Church A →̇ Church A →̇ Church A
ṁulᶜ = λ̇ λ̇ λ̇ # 2 · (# 1 · # 0)

ėxpᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ Church A →̇ Church (A →̇ A) →̇ Church A
ėxpᶜ = λ̇ λ̇ # 0 · # 1

2+2ᶜ : {Γ : Context}
    → Γ ⊢ ℕ̇
2+2ᶜ = ȧddᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero

2*2ᶜ : {Γ : Context}
    → Γ ⊢ ℕ̇
2*2ᶜ = ṁulᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero

_ : eval (gas 14) (ėxpᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero) ≡ steps
    (-- begin
            (λ̇ (λ̇ ⊢lookup here · ⊢lookup (there here))) · (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇))) ⟩
            (λ̇ ⊢lookup here · (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here)))) · (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
            (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
            (λ̇ (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · ((λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · ⊢lookup here)) · (λ̇ ṡuc ⊢lookup here) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · ((λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here)) · żero
        ⟶⟨ ξ-·₁ (ξ-·₂ value-λ̇ (β-λ̇ value-λ̇)) ⟩
            (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · ⊢lookup here)) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ (λ̇ (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · ⊢lookup here)) · ((λ̇ (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · ⊢lookup here)) · ⊢lookup here)) · żero
        ⟶⟨ β-λ̇ value-żero ⟩
            (λ̇ (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · ⊢lookup here)) · ((λ̇ (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · ⊢lookup here)) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
            (λ̇ (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · ⊢lookup here)) · ((λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
            (λ̇ (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · ⊢lookup here)) · ((λ̇ ṡuc ⊢lookup here) · ṡuc żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
            (λ̇ (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · ⊢lookup here)) · ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ ṡuc ⊢lookup here) · ṡuc (ṡuc (ṡuc żero))
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc (value-ṡuc value-żero))) ⟩
            ṡuc (ṡuc (ṡuc (ṡuc żero)))
        ∎)
    (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
_ = refl

determinism : {Γ : Context} → {A : Type} → {term₁ term₂ term₃ : Γ ⊢ A}
    → term₁ ⟶ term₂ → term₁ ⟶ term₃
    → term₂ ≡ term₃
determinism (β-λ̇ value₁) (β-λ̇ value₂) = refl
determinism (β-λ̇ value₁) (ξ-·₂ value₂ reduction₂) = ⊥-elim (¬[value×reducible] value₁ reduction₂)
determinism β-żero β-żero = refl
determinism (β-ṡuc value₁) (β-ṡuc value₂) = refl
determinism (β-ṡuc value₁) (ξ-caseℕ̇ reduction₂) = ⊥-elim (¬[value×reducible] (value-ṡuc value₁) reduction₂)
determinism β-μ̇ β-μ̇ = refl
determinism (β-l̇et value₁) (β-l̇et value₂) = refl
determinism (β-l̇et value₁) (ξ-l̇et reduction₂) = ⊥-elim (¬[value×reducible] value₁ reduction₂)
determinism β-case𝟙̇ β-case𝟙̇ = refl
determinism (β-i̇nj₁ value₁) (β-i̇nj₁ value₂) = refl
determinism (β-i̇nj₁ value₁) (ξ-case+̇ reduction₂) = ⊥-elim (¬[value×reducible] (value-i̇nj₁ value₁) reduction₂)
determinism (β-i̇nj₂ value₁) (β-i̇nj₂ value₂) = refl
determinism (β-i̇nj₂ value₁) (ξ-case+̇ reduction₂) = ⊥-elim (¬[value×reducible] (value-i̇nj₂ value₁) reduction₂)
determinism (β-ṗroj₁ value₁₁ value₁₂) (β-ṗroj₁ value₂₁ value₂₂) = refl
determinism (β-ṗroj₁ value₁₁ value₁₂) (ξ-ṗroj₁ reduction₂) = ⊥-elim (¬[value×reducible] (value-,̇ value₁₁ value₁₂) reduction₂)
determinism (β-ṗroj₂ value₁₁ value₁₂) (β-ṗroj₂ value₂₁ value₂₂) = refl
determinism (β-ṗroj₂ value₁₁ value₁₂) (ξ-ṗroj₂ reduction₂) = ⊥-elim (¬[value×reducible] (value-,̇ value₁₁ value₁₂) reduction₂)
determinism (β-case×̇ value₁₁ value₁₂) (β-case×̇ value₂₁ value₂₂) = refl
determinism (β-case×̇ value₁₁ value₁₂) (ξ-case×̇ reduction₂) = ⊥-elim (¬[value×reducible] (value-,̇ value₁₁ value₁₂) reduction₂)
determinism β-[̇] β-[̇] = refl
determinism (β-∷̇ value₁₁ value₁₂) (β-∷̇ value₂₁ value₂₂) = refl
determinism (β-∷̇ value₁₁ value₁₂) (ξ-caseL̇ist reduction₂) = ⊥-elim (¬[value×reducible] (value-∷̇ value₁₁ value₁₂) reduction₂)
determinism δ-ŝuc δ-ŝuc = refl
determinism δ-+̂ δ-+̂ = refl
determinism δ-*̂ δ-*̂ = refl
determinism (ξ-·₁ {term₂ = term₂} reduction₁) (ξ-·₁ reduction₂) = cong (_· term₂) (determinism reduction₁ reduction₂)
determinism (ξ-·₁ reduction₁) (ξ-·₂ value₂ reduction₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-·₂ value₁ reduction₁) (β-λ̇ value₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-·₂ value₁ reduction₁) (ξ-·₁ reduction₂) = ⊥-elim (¬[value×reducible] value₁ reduction₂)
determinism (ξ-·₂ {term₁ = term₁} value₁ reduction₁) (ξ-·₂ value₂ reduction₂) = cong (term₁ ·_) (determinism reduction₁ reduction₂)
determinism (ξ-ṡuc reduction₁) (ξ-ṡuc reduction₂) = cong ṡuc_ (determinism reduction₁ reduction₂)
determinism (ξ-caseℕ̇ reduction₁) (β-ṡuc value₂) = ⊥-elim (¬[value×reducible] (value-ṡuc value₂) reduction₁)
determinism (ξ-caseℕ̇ {term₂ = term₂} {term₃ = term₃} reduction₁) (ξ-caseℕ̇ reduction₂) = cong (λ term₁ → caseℕ̇ term₁ term₂ term₃) (determinism reduction₁ reduction₂)
determinism (ξ-l̇et reduction₁) (β-l̇et value₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-l̇et {term₂ = term₂} reduction₁) (ξ-l̇et reduction₂) = cong (λ term₁ → l̇et term₁ term₂) (determinism reduction₁ reduction₂)
determinism (ξ-ŝuc reduction₁) (ξ-ŝuc reduction₂) = cong ŝuc_ (determinism reduction₁ reduction₂)
determinism (ξ-+̂₁ {term₂ = term₂} reduction₁) (ξ-+̂₁ reduction₂) = cong (_+̂ term₂) (determinism reduction₁ reduction₂)
determinism (ξ-+̂₁ reduction₁) (ξ-+̂₂ value₂ reduction₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-+̂₂ value₁ reduction₁) (ξ-+̂₁ reduction₂) = ⊥-elim (¬[value×reducible] value₁ reduction₂)
determinism (ξ-+̂₂ {term₁ = term₁} value₁ reduction₁) (ξ-+̂₂ value₂ reduction₂) = cong (term₁ +̂_) (determinism reduction₁ reduction₂)
determinism (ξ-*̂₁ {term₂ = term₂} reduction₁) (ξ-*̂₁ reduction₂) = cong (_*̂ term₂) (determinism reduction₁ reduction₂)
determinism (ξ-*̂₁ reduction₁) (ξ-*̂₂ value₂ reduction₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-*̂₂ value₁ reduction₁) (ξ-*̂₁ reduction₂) = ⊥-elim (¬[value×reducible] value₁ reduction₂)
determinism (ξ-*̂₂ {term₁ = term₁} value₁ reduction₁) (ξ-*̂₂ value₂ reduction₂) = cong (term₁ *̂_) (determinism reduction₁ reduction₂)
determinism (ξ-case𝟘̇ reduction₁) (ξ-case𝟘̇ reduction₂) = cong case𝟘̇ (determinism reduction₁ reduction₂)
determinism (ξ-case𝟙̇ {term₂ = term₂} reduction₁) (ξ-case𝟙̇ reduction₂) = cong (λ term₁ → case𝟙̇ term₁ term₂) (determinism reduction₁ reduction₂)
determinism (ξ-i̇nj₁ reduction₁) (ξ-i̇nj₁ reduction₂) = cong i̇nj₁ (determinism reduction₁ reduction₂)
determinism (ξ-i̇nj₂ reduction₁) (ξ-i̇nj₂ reduction₂) = cong i̇nj₂ (determinism reduction₁ reduction₂)
determinism (ξ-case+̇ reduction₁) (β-i̇nj₁ value₂) = ⊥-elim (¬[value×reducible] (value-i̇nj₁ value₂) reduction₁)
determinism (ξ-case+̇ reduction₁) (β-i̇nj₂ value₂) = ⊥-elim (¬[value×reducible] (value-i̇nj₂ value₂) reduction₁)
determinism (ξ-case+̇ {term₂ = term₂} {term₃ = term₃} reduction₁) (ξ-case+̇ reduction₂) = cong (λ term₁ → case+̇ term₁ term₂ term₃) (determinism reduction₁ reduction₂)
determinism (ξ-,̇₁ {term₂ = term₂} reduction₁) (ξ-,̇₁ reduction₂) = cong (_,̇ term₂) (determinism reduction₁ reduction₂)
determinism (ξ-,̇₁ reduction₁) (ξ-,̇₂ value₂ reduction₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-,̇₂ value₁ reduction₁) (ξ-,̇₁ reduction₂) = ⊥-elim (¬[value×reducible] value₁ reduction₂)
determinism (ξ-,̇₂ {term₁ = term₁} value₁ reduction₁) (ξ-,̇₂ value₂ reduction₂) = cong (term₁ ,̇_) (determinism reduction₁ reduction₂)
determinism (ξ-ṗroj₁ reduction₁) (β-ṗroj₁ value₂₁ value₂₂) = ⊥-elim (¬[value×reducible] (value-,̇ value₂₁ value₂₂) reduction₁)
determinism (ξ-ṗroj₁ reduction₁) (ξ-ṗroj₁ reduction₂) = cong ṗroj₁ (determinism reduction₁ reduction₂)
determinism (ξ-ṗroj₂ reduction₁) (β-ṗroj₂ value₂₁ value₂₂) = ⊥-elim (¬[value×reducible] (value-,̇ value₂₁ value₂₂) reduction₁)
determinism (ξ-ṗroj₂ reduction₁) (ξ-ṗroj₂ reduction₂) = cong ṗroj₂ (determinism reduction₁ reduction₂)
determinism (ξ-case×̇ reduction₁) (β-case×̇ value₂₁ value₂₂) = ⊥-elim (¬[value×reducible] (value-,̇ value₂₁ value₂₂) reduction₁)
determinism (ξ-case×̇ {term₂ = term₂} reduction₁) (ξ-case×̇ reduction₂) = cong (λ term₁ → case×̇ term₁ term₂) (determinism reduction₁ reduction₂)
determinism (ξ-∷̇₁ {term₂ = term₂} reduction₁) (ξ-∷̇₁ reduction₂) = cong (_∷̇ term₂) (determinism reduction₁ reduction₂)
determinism (ξ-∷̇₁ reduction₁) (ξ-∷̇₂ value₂ reduction₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-∷̇₂ value₁ reduction₁) (ξ-∷̇₁ reduction₂) = ⊥-elim (¬[value×reducible] value₁ reduction₂)
determinism (ξ-∷̇₂ {term₁ = term₁} value₁ reduction₁) (ξ-∷̇₂ value₂ reduction₂) = cong (term₁ ∷̇_) (determinism reduction₁ reduction₂)
determinism (ξ-caseL̇ist reduction₁) (β-∷̇ value₂₁ value₂₂) = ⊥-elim (¬[value×reducible] (value-∷̇ value₂₁ value₂₂) reduction₁)
determinism (ξ-caseL̇ist {term₂ = term₂} {term₃ = term₃} reduction₁) (ξ-caseL̇ist reduction₂) = cong (λ term₁ → caseL̇ist term₁ term₂ term₃) (determinism reduction₁ reduction₂)
