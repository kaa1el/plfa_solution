{-# OPTIONS --without-K #-}

module plfa.part2.More where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _<?_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_)
open import Function using (_∘_; flip)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)

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

infixl 4.5 _‚‚_
_‚‚_ : Context → Context → Context
_‚‚_ = flip _++_

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
    lookup : {Γ : Context} → {A : Type}
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
    ẑero : {Γ : Context} -- primitive natural number zero
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
#_ n {z} = lookup (count (toWitness z))

extend-reindex : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ∋ A)
    → ({A B : Type} → Γ ‚ B ∋ A → Δ ‚ B ∋ A)
extend-reindex ρ here = here
extend-reindex ρ (there index) = there (ρ index)

reindex-to-rebase : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ∋ A)
    → ({A : Type} → Γ ⊢ A → Δ ⊢ A)
reindex-to-rebase ρ (lookup index) = lookup (ρ index)
reindex-to-rebase ρ (λ̇ term) = λ̇ (reindex-to-rebase (extend-reindex ρ) term)
reindex-to-rebase ρ (term₁ · term₂) = (reindex-to-rebase ρ term₁) · (reindex-to-rebase ρ term₂)
reindex-to-rebase ρ żero = żero
reindex-to-rebase ρ (ṡuc term) = ṡuc (reindex-to-rebase ρ term)
reindex-to-rebase ρ (caseℕ̇ term₁ term₂ term₃) = caseℕ̇ (reindex-to-rebase ρ term₁) (reindex-to-rebase ρ term₂) (reindex-to-rebase (extend-reindex ρ) term₃)
reindex-to-rebase ρ (μ̇ term) = μ̇ (reindex-to-rebase (extend-reindex ρ) term)
reindex-to-rebase ρ (l̇et term₁ term₂) = l̇et (reindex-to-rebase ρ term₁) (reindex-to-rebase (extend-reindex ρ) term₂)
reindex-to-rebase ρ (prim n) = prim n
reindex-to-rebase ρ ẑero = ẑero
reindex-to-rebase ρ (ŝuc term) = ŝuc (reindex-to-rebase ρ term)
reindex-to-rebase ρ (term₁ +̂ term₂) = reindex-to-rebase ρ term₁ +̂ reindex-to-rebase ρ term₂
reindex-to-rebase ρ (term₁ *̂ term₂) = reindex-to-rebase ρ term₁ *̂ reindex-to-rebase ρ term₂
reindex-to-rebase ρ (case𝟘̇ term) = case𝟘̇ (reindex-to-rebase ρ term)
reindex-to-rebase ρ ṫt = ṫt
reindex-to-rebase ρ (case𝟙̇ term₁ term₂) = case𝟙̇ (reindex-to-rebase ρ term₁) (reindex-to-rebase ρ term₂)
reindex-to-rebase ρ (i̇nj₁ term) = i̇nj₁ (reindex-to-rebase ρ term)
reindex-to-rebase ρ (i̇nj₂ term) = i̇nj₂ (reindex-to-rebase ρ term)
reindex-to-rebase ρ (case+̇ term₁ term₂ term₃) = case+̇ (reindex-to-rebase ρ term₁) (reindex-to-rebase (extend-reindex ρ) term₂) (reindex-to-rebase (extend-reindex ρ) term₃)
reindex-to-rebase ρ (term₁ ,̇ term₂) = (reindex-to-rebase ρ term₁) ,̇ (reindex-to-rebase ρ term₂)
reindex-to-rebase ρ (ṗroj₁ term) = ṗroj₁ (reindex-to-rebase ρ term)
reindex-to-rebase ρ (ṗroj₂ term) = ṗroj₂ (reindex-to-rebase ρ term)
reindex-to-rebase ρ (case×̇ term₁ term₂) = case×̇ (reindex-to-rebase ρ term₁) (reindex-to-rebase (extend-reindex (extend-reindex ρ)) term₂)
reindex-to-rebase ρ [̇] = [̇]
reindex-to-rebase ρ (term₁ ∷̇ term₂) = reindex-to-rebase ρ term₁ ∷̇ reindex-to-rebase ρ term₂
reindex-to-rebase ρ (caseL̇ist term₁ term₂ term₃) = caseL̇ist (reindex-to-rebase ρ term₁) (reindex-to-rebase ρ term₂) (reindex-to-rebase (extend-reindex (extend-reindex ρ)) term₃)

shift : {Γ : Context} → {A B : Type} → Γ ⊢ A → Γ ‚ B ⊢ A
shift = reindex-to-rebase there

extend : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ⊢ A)
    → ({A B : Type} → Γ ‚ B ∋ A → Δ ‚ B ⊢ A)
extend σ here = lookup here
extend σ (there index) = shift (σ index)

substitute : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ⊢ A)
    → ({A : Type} → Γ ⊢ A → Δ ⊢ A)
substitute σ (lookup index) = σ index
substitute σ (λ̇ term) = λ̇ substitute (extend σ) term
substitute σ (term₁ · term₂) = (substitute σ term₁) · (substitute σ term₂)
substitute σ żero = żero
substitute σ (ṡuc term) = ṡuc substitute σ term
substitute σ (caseℕ̇ term₁ term₂ term₃) = caseℕ̇ (substitute σ term₁) (substitute σ term₂) (substitute (extend σ) term₃)
substitute σ (μ̇ term) = μ̇ substitute (extend σ) term
substitute σ (l̇et term₁ term₂) = l̇et (substitute σ term₁) (substitute (extend σ) term₂)
substitute σ (prim n) = prim n
substitute σ ẑero = ẑero
substitute σ (ŝuc term) = ŝuc (substitute σ term)
substitute σ (term₁ +̂ term₂) = substitute σ term₁ +̂ substitute σ term₂
substitute σ (term₁ *̂ term₂) = substitute σ term₁ *̂ substitute σ term₂
substitute σ (case𝟘̇ term) = case𝟘̇ (substitute σ term)
substitute σ ṫt = ṫt
substitute σ (case𝟙̇ term₁ term₂) = case𝟙̇ (substitute σ term₁) (substitute σ term₂)
substitute σ (i̇nj₁ term) = i̇nj₁ (substitute σ term)
substitute σ (i̇nj₂ term) = i̇nj₂ (substitute σ term)
substitute σ (case+̇ term₁ term₂ term₃) = case+̇ (substitute σ term₁) (substitute (extend σ) term₂) (substitute (extend σ) term₃)
substitute σ (term₁ ,̇ term₂) = (substitute σ term₁) ,̇ (substitute σ term₂)
substitute σ (ṗroj₁ term) = ṗroj₁ (substitute σ term)
substitute σ (ṗroj₂ term) = ṗroj₂ (substitute σ term)
substitute σ (case×̇ term₁ term₂) = case×̇ (substitute σ term₁) (substitute (extend (extend σ)) term₂)
substitute σ [̇] = [̇]
substitute σ (term₁ ∷̇ term₂) = substitute σ term₁ ∷̇ substitute σ term₂
substitute σ (caseL̇ist term₁ term₂ term₃) = caseL̇ist (substitute σ term₁) (substitute σ term₂) (substitute (extend (extend σ)) term₃)

σ₁ : {Γ : Context} → {A B : Type}
    → Γ ⊢ A
    → Γ ‚ A ∋ B
    → Γ ⊢ B
σ₁ term here = term
σ₁ term (there index) = lookup index

_[_] : {Γ : Context} → {A B : Type}
    → Γ ‚ A ⊢ B
    → Γ ⊢ A
    → Γ ⊢ B
_[_] {Γ} {A} {B} term₁ term₂ = substitute {Γ ‚ A} {Γ} (σ₁ term₂) {B} term₁
-- _[_] {Γ} {A} {B} term₁ term₂ = substitute {Γ ‚ A} {Γ} σ term₁ where
--     σ : {B : Type} → Γ ‚ A ∋ B → Γ ⊢ B
--     σ here = term₂
--     σ (there index) = lookup index

σ₂ : {Γ : Context} → {A B C : Type}
    → Γ ⊢ A
    → Γ ⊢ B
    → Γ ‚ A ‚ B ∋ C
    → Γ ⊢ C
σ₂ term₁ term₂ here = term₂
σ₂ term₁ term₂ (there here) = term₁
σ₂ term₁ term₂ (there (there index)) = lookup index

_[_][_] : {Γ : Context} → {A B C : Type}
    → Γ ‚ A ‚ B ⊢ C
    → Γ ⊢ A
    → Γ ⊢ B
    → Γ ⊢ C
_[_][_] {Γ} {A} {B} {C} term₁ term₂ term₃ = substitute {Γ ‚ A ‚ B} {Γ} (σ₂ term₂ term₃) {C} term₁
-- _[_][_] {Γ} {A} {B} {C} term₁ term₂ term₃ = substitute {Γ ‚ A ‚ B} {Γ} σ term₁ where
--     σ : {C : Type} → Γ ‚ A ‚ B ∋ C → Γ ⊢ C
--     σ here = term₃
--     σ (there here) = term₂
--     σ (there (there index)) = lookup index

-- double-substitute : {Γ : Context} → {A B C : Type}
--     → (term₁ : Γ ‚ A ‚ B ⊢ C)
--     → (term₂ : Γ ⊢ A)
--     → (term₃ : Γ ⊢ B)
--     → term₁ [ term₂ ][ term₃ ] ≡ term₁ [ shift term₃ ] [ term₂ ]
-- double-substitute {Γ} {A} {B} {C} term₁ term₂ term₃ = ? -- see DoubleSubstitutionMore.agda

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
    β-l̇et : {Γ : Context} → {A B : Type} -- l̇et term₁ term₂ ~ (λ̇ term₂) · term₁ ⟶ term₂ [ term₁ ]
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
    δ-ẑero : {Γ : Context}
        → ẑero {Γ} ⟶ prim zero
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
progress ẑero = step δ-ẑero
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

test2 : {Γ : Context} → {n : ℕ}
    → ẑero {Γ} *̂ (prim n) ⟶⋆ (prim 0)
test2 {n = n} =
    begin
        ẑero *̂ (prim n)
    ⟶⟨ ξ-*̂₁ δ-ẑero ⟩
        (prim 0) *̂ (prim n)
    ⟶⟨ δ-*̂ ⟩
        prim 0
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
            (λ̇ (λ̇ lookup here · lookup (there here))) · (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇))) ⟩
            (λ̇ lookup here · (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here)))) · (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
            (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
            (λ̇ (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · ((λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · lookup here)) · (λ̇ ṡuc lookup here) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · ((λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here)) · żero
        ⟶⟨ ξ-·₁ (ξ-·₂ value-λ̇ (β-λ̇ value-λ̇)) ⟩
            (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · lookup here)) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ (λ̇ (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · lookup here)) · ((λ̇ (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · lookup here)) · lookup here)) · żero
        ⟶⟨ β-λ̇ value-żero ⟩
            (λ̇ (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · lookup here)) · ((λ̇ (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · lookup here)) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
            (λ̇ (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · lookup here)) · ((λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
            (λ̇ (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · lookup here)) · ((λ̇ ṡuc lookup here) · ṡuc żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
            (λ̇ (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · lookup here)) · ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ ṡuc lookup here) · ṡuc (ṡuc (ṡuc żero))
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
determinism δ-ẑero δ-ẑero = refl
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

-- Bonus: use encode-decode to prove Term-Is-hSet

open import plfa.part1.Equality using (cong₃)
open import plfa.part1.Isomorphism using (_≅_; _≲_; Is-hProp; Is-hSet; Is-hGroupoid; ×-Is-hProp; Σ-Is-hProp; ⊤-Is-hProp; ⊥-Is-hProp; Is-hSet-implies-Is-hGroupoid; hProp-iso; ≅-Is-hProp; ≅-Is-hSet)
open import plfa.part1.Quantifiers using (ℕ-Is-hSet; Tree; leaf; node; Tree-Is-hSet)
open import plfa.part1.Lists using (Membership-Is-hSet)

CodeType : Type → Type → Set
CodeType ℕ̇ ℕ̇ = ⊤
CodeType ℕ̇ ℕ̂ = ⊥
CodeType ℕ̇ 𝟙̇ = ⊥
CodeType ℕ̇ 𝟘̇ = ⊥
CodeType ℕ̇ (B₁ →̇ B₂) = ⊥
CodeType ℕ̇ (B₁ ×̇ B₂) = ⊥
CodeType ℕ̇ (B₁ +̇ B₂) = ⊥
CodeType ℕ̇ (L̇ist B) = ⊥
CodeType ℕ̂ ℕ̇ = ⊥
CodeType ℕ̂ ℕ̂ = ⊤
CodeType ℕ̂ 𝟙̇ = ⊥
CodeType ℕ̂ 𝟘̇ = ⊥
CodeType ℕ̂ (B₁ →̇ B₂) = ⊥
CodeType ℕ̂ (B₁ ×̇ B₂) = ⊥
CodeType ℕ̂ (B₁ +̇ B₂) = ⊥
CodeType ℕ̂ (L̇ist B) = ⊥
CodeType 𝟙̇ ℕ̇ = ⊥
CodeType 𝟙̇ ℕ̂ = ⊥
CodeType 𝟙̇ 𝟙̇ = ⊤
CodeType 𝟙̇ 𝟘̇ = ⊥
CodeType 𝟙̇ (B₁ →̇ B₂) = ⊥
CodeType 𝟙̇ (B₁ ×̇ B₂) = ⊥
CodeType 𝟙̇ (B₁ +̇ B₂) = ⊥
CodeType 𝟙̇ (L̇ist B) = ⊥
CodeType 𝟘̇ ℕ̇ = ⊥
CodeType 𝟘̇ ℕ̂ = ⊥
CodeType 𝟘̇ 𝟙̇ = ⊥
CodeType 𝟘̇ 𝟘̇ = ⊤
CodeType 𝟘̇ (B₁ →̇ B₂) = ⊥
CodeType 𝟘̇ (B₁ ×̇ B₂) = ⊥
CodeType 𝟘̇ (B₁ +̇ B₂) = ⊥
CodeType 𝟘̇ (L̇ist B) = ⊥
CodeType (A₁ →̇ A₂) ℕ̇ = ⊥
CodeType (A₁ →̇ A₂) ℕ̂ = ⊥
CodeType (A₁ →̇ A₂) 𝟙̇ = ⊥
CodeType (A₁ →̇ A₂) 𝟘̇ = ⊥
CodeType (A₁ →̇ A₂) (B₁ →̇ B₂) = CodeType A₁ B₁ × CodeType A₂ B₂
CodeType (A₁ →̇ A₂) (B₁ ×̇ B₂) = ⊥
CodeType (A₁ →̇ A₂) (B₁ +̇ B₂) = ⊥
CodeType (A₁ →̇ A₂) (L̇ist B) = ⊥
CodeType (A₁ ×̇ A₂) ℕ̇ = ⊥
CodeType (A₁ ×̇ A₂) ℕ̂ = ⊥
CodeType (A₁ ×̇ A₂) 𝟙̇ = ⊥
CodeType (A₁ ×̇ A₂) 𝟘̇ = ⊥
CodeType (A₁ ×̇ A₂) (B₁ →̇ B₂) = ⊥
CodeType (A₁ ×̇ A₂) (B₁ ×̇ B₂) = CodeType A₁ B₁ × CodeType A₂ B₂
CodeType (A₁ ×̇ A₂) (B₁ +̇ B₂) = ⊥
CodeType (A₁ ×̇ A₂) (L̇ist B) = ⊥
CodeType (A₁ +̇ A₂) ℕ̇ = ⊥
CodeType (A₁ +̇ A₂) ℕ̂ = ⊥
CodeType (A₁ +̇ A₂) 𝟙̇ = ⊥
CodeType (A₁ +̇ A₂) 𝟘̇ = ⊥
CodeType (A₁ +̇ A₂) (B₁ →̇ B₂) = ⊥
CodeType (A₁ +̇ A₂) (B₁ ×̇ B₂) = ⊥
CodeType (A₁ +̇ A₂) (B₁ +̇ B₂) = CodeType A₁ B₁ × CodeType A₂ B₂
CodeType (A₁ +̇ A₂) (L̇ist B) = ⊥
CodeType (L̇ist A) ℕ̇ = ⊥
CodeType (L̇ist A) ℕ̂ = ⊥
CodeType (L̇ist A) 𝟙̇ = ⊥
CodeType (L̇ist A) 𝟘̇ = ⊥
CodeType (L̇ist A) (B₁ →̇ B₂) = ⊥
CodeType (L̇ist A) (B₁ ×̇ B₂) = ⊥
CodeType (L̇ist A) (B₁ +̇ B₂) = ⊥
CodeType (L̇ist A) (L̇ist B) = CodeType A B

rType : (A : Type) → CodeType A A
rType ℕ̇ = tt
rType ℕ̂ = tt
rType 𝟙̇ = tt
rType 𝟘̇ = tt
rType (A₁ →̇ A₂) = rType A₁ , rType A₂
rType (A₁ ×̇ A₂) = rType A₁ , rType A₂
rType (A₁ +̇ A₂) = rType A₁ , rType A₂
rType (L̇ist A) = rType A

Type-eq≅CodeType : (A B : Type) → A ≡ B ≅ CodeType A B
Type-eq≅CodeType A B = record {
        to = encodeType A B;
        from = decodeType A B;
        from∘to = decodeType-encodeType A B;
        to∘from = encodeType-decodeType A B
    } where
        encodeType : (A B : Type) → A ≡ B → CodeType A B
        encodeType A .A refl = rType A

        decodeType : (A B : Type) → CodeType A B → A ≡ B
        decodeType ℕ̇ ℕ̇ tt = refl
        decodeType ℕ̂ ℕ̂ tt = refl
        decodeType 𝟙̇ 𝟙̇ tt = refl
        decodeType 𝟘̇ 𝟘̇ tt = refl
        decodeType (A₁ →̇ A₂) (B₁ →̇ B₂) (code₁ , code₂) = cong₂ _→̇_ (decodeType A₁ B₁ code₁) (decodeType A₂ B₂ code₂)
        decodeType (A₁ ×̇ A₂) (B₁ ×̇ B₂) (code₁ , code₂) = cong₂ _×̇_ (decodeType A₁ B₁ code₁) (decodeType A₂ B₂ code₂)
        decodeType (A₁ +̇ A₂) (B₁ +̇ B₂) (code₁ , code₂) = cong₂ _+̇_ (decodeType A₁ B₁ code₁) (decodeType A₂ B₂ code₂)
        decodeType (L̇ist A) (L̇ist B) code = cong L̇ist (decodeType A B code)

        decodeType-encodeType : (A B : Type) → (p : A ≡ B) → decodeType A B (encodeType A B p) ≡ p
        decodeType-encodeType ℕ̇ .ℕ̇ refl = refl
        decodeType-encodeType ℕ̂ .ℕ̂ refl = refl
        decodeType-encodeType 𝟙̇ .𝟙̇ refl = refl
        decodeType-encodeType 𝟘̇ .𝟘̇ refl = refl
        decodeType-encodeType (A₁ →̇ A₂) .(A₁ →̇ A₂) refl = cong₂ (cong₂ _→̇_) (decodeType-encodeType A₁ A₁ refl) (decodeType-encodeType A₂ A₂ refl)
        decodeType-encodeType (A₁ ×̇ A₂) .(A₁ ×̇ A₂) refl = cong₂ (cong₂ _×̇_) (decodeType-encodeType A₁ A₁ refl) (decodeType-encodeType A₂ A₂ refl)
        decodeType-encodeType (A₁ +̇ A₂) .(A₁ +̇ A₂) refl = cong₂ (cong₂ _+̇_) (decodeType-encodeType A₁ A₁ refl) (decodeType-encodeType A₂ A₂ refl)
        decodeType-encodeType (L̇ist A) .(L̇ist A) refl = cong (cong L̇ist) (decodeType-encodeType A A refl)

        encodeType-decodeType : (A B : Type) → (code : CodeType A B) → encodeType A B (decodeType A B code) ≡ code
        encodeType-decodeType ℕ̇ ℕ̇ tt = refl
        encodeType-decodeType ℕ̂ ℕ̂ tt = refl
        encodeType-decodeType 𝟙̇ 𝟙̇ tt = refl
        encodeType-decodeType 𝟘̇ 𝟘̇ tt = refl
        encodeType-decodeType (A₁ →̇ A₂) (B₁ →̇ B₂) (code₁ , code₂)
            with
                decodeType A₁ B₁ code₁ |
                decodeType A₂ B₂ code₂ |
                encodeType-decodeType A₁ B₁ code₁ |
                encodeType-decodeType A₂ B₂ code₂
        ... | refl | refl | refl | refl = refl
        encodeType-decodeType (A₁ ×̇ A₂) (B₁ ×̇ B₂) (code₁ , code₂)
            with
                decodeType A₁ B₁ code₁ |
                decodeType A₂ B₂ code₂ |
                encodeType-decodeType A₁ B₁ code₁ |
                encodeType-decodeType A₂ B₂ code₂
        ... | refl | refl | refl | refl = refl
        encodeType-decodeType (A₁ +̇ A₂) (B₁ +̇ B₂) (code₁ , code₂)
            with
                decodeType A₁ B₁ code₁ |
                decodeType A₂ B₂ code₂ |
                encodeType-decodeType A₁ B₁ code₁ |
                encodeType-decodeType A₂ B₂ code₂
        ... | refl | refl | refl | refl = refl
        encodeType-decodeType (L̇ist A) (L̇ist B) code
            with
                decodeType A B code |
                encodeType-decodeType A B code
        ... | refl | refl = refl

CodeType-Is-hProp : (A B : Type) → Is-hProp (CodeType A B)
CodeType-Is-hProp ℕ̇ ℕ̇ = ⊤-Is-hProp
CodeType-Is-hProp ℕ̂ ℕ̂ = ⊤-Is-hProp
CodeType-Is-hProp 𝟙̇ 𝟙̇ = ⊤-Is-hProp
CodeType-Is-hProp 𝟘̇ 𝟘̇ = ⊤-Is-hProp
CodeType-Is-hProp (A₁ →̇ A₂) (B₁ →̇ B₂) = ×-Is-hProp (CodeType-Is-hProp A₁ B₁) (CodeType-Is-hProp A₂ B₂)
CodeType-Is-hProp (A₁ ×̇ A₂) (B₁ ×̇ B₂) = ×-Is-hProp (CodeType-Is-hProp A₁ B₁) (CodeType-Is-hProp A₂ B₂)
CodeType-Is-hProp (A₁ +̇ A₂) (B₁ +̇ B₂) = ×-Is-hProp (CodeType-Is-hProp A₁ B₁) (CodeType-Is-hProp A₂ B₂)
CodeType-Is-hProp (L̇ist A) (L̇ist B) = CodeType-Is-hProp A B

Type-Is-hSet : Is-hSet Type
Type-Is-hSet A B = ≅-Is-hProp (Type-eq≅CodeType A B) (CodeType-Is-hProp A B)

Index≅Membership : {Γ : Context} → {A : Type} → Γ ∋ A ≅ A ∈ Γ
Index≅Membership = record {
        to = to;
        from = from;
        from∘to = from∘to;
        to∘from = to∘from
    } where
        to : {Γ : Context} → {A : Type} → Γ ∋ A → A ∈ Γ
        to here = here refl
        to (there index) = there (to index)

        from : {Γ : Context} → {A : Type} → A ∈ Γ → Γ ∋ A
        from (here refl) = here
        from (there p) = there (from p)

        from∘to : {Γ : Context} → {A : Type} → (index : Γ ∋ A) → from (to index) ≡ index
        from∘to here = refl
        from∘to (there index) = cong there (from∘to index)

        to∘from : {Γ : Context} → {A : Type} → (p : A ∈ Γ) → to (from p) ≡ p
        to∘from (here refl) = refl
        to∘from (there p) = cong there (to∘from p)

Index-Is-hSet : {Γ : Context} → {A : Type} → Is-hSet (Γ ∋ A)
Index-Is-hSet = ≅-Is-hSet Index≅Membership (Membership-Is-hSet (Is-hSet-implies-Is-hGroupoid Type-Is-hSet))

CodeTerm : {Γ : Context} → {A : Type} → (term₁ term₂ : Γ ⊢ A) → Set
CodeTerm (lookup index₁) (lookup index₂) = index₁ ≡ index₂
CodeTerm (lookup index₁) (λ̇ term₂) = ⊥
CodeTerm (lookup index₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (lookup index₁) żero = ⊥
CodeTerm (lookup index₁) (ṡuc term₂) = ⊥
CodeTerm (lookup index₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (lookup index₁) (μ̇ term₂) = ⊥
CodeTerm (lookup index₁) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (lookup index₁) (prim m) = ⊥
CodeTerm (lookup index₁) ẑero = ⊥
CodeTerm (lookup index₁) (ŝuc term₂) = ⊥
CodeTerm (lookup index₁) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (lookup index₁) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (lookup index₁) (case𝟘̇ term₂) = ⊥
CodeTerm (lookup index₁) ṫt = ⊥
CodeTerm (lookup index₁) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (lookup index₁) (i̇nj₁ term₂) = ⊥
CodeTerm (lookup index₁) (i̇nj₂ term₂) = ⊥
CodeTerm (lookup index₁) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (lookup index₁) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (lookup index₁) (ṗroj₁ term₂) = ⊥
CodeTerm (lookup index₁) (ṗroj₂ term₂) = ⊥
CodeTerm (lookup index₁) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (lookup index₁) [̇] = ⊥
CodeTerm (lookup index₁) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (lookup index₁) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (λ̇ term₁) (lookup index₂) = ⊥
CodeTerm (λ̇ term₁) (λ̇ term₂) = CodeTerm term₁ term₂
CodeTerm (λ̇ term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (λ̇ term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (λ̇ term₁) (μ̇ term₂) = ⊥
CodeTerm (λ̇ term₁) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (λ̇ term₁) (case𝟘̇ term₂) = ⊥
CodeTerm (λ̇ term₁) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (λ̇ term₁) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (λ̇ term₁) (ṗroj₁ term₂) = ⊥
CodeTerm (λ̇ term₁) (ṗroj₂ term₂) = ⊥
CodeTerm (λ̇ term₁) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (λ̇ term₁) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ · term₁₂) (lookup index₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (λ̇ term₂) = ⊥
CodeTerm (_·_ {A = A₁} term₁₁ term₁₂) (_·_ {A = A₂} term₂₁ term₂₂) = Σ (A₁ ≡ A₂) (λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ })
CodeTerm (term₁₁ · term₁₂) żero = ⊥
CodeTerm (term₁₁ · term₁₂) (ṡuc term₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ · term₁₂) (μ̇ term₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (prim m) = ⊥
CodeTerm (term₁₁ · term₁₂) ẑero = ⊥
CodeTerm (term₁₁ · term₁₂) (ŝuc term₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (case𝟘̇ term₂) = ⊥
CodeTerm (term₁₁ · term₁₂) ṫt = ⊥
CodeTerm (term₁₁ · term₁₂) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (i̇nj₁ term₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (i̇nj₂ term₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ · term₁₂) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (ṗroj₁ term₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (ṗroj₂ term₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ · term₁₂) [̇] = ⊥
CodeTerm (term₁₁ · term₁₂) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm żero (lookup index₂) = ⊥
CodeTerm żero (term₂₁ · term₂₂) = ⊥
CodeTerm żero żero = ⊤
CodeTerm żero (ṡuc term₂) = ⊥
CodeTerm żero (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm żero (μ̇ term₂) = ⊥
CodeTerm żero (l̇et term₂₁ term₂₂) = ⊥
CodeTerm żero (case𝟘̇ term₂) = ⊥
CodeTerm żero (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm żero (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm żero (ṗroj₁ term₂) = ⊥
CodeTerm żero (ṗroj₂ term₂) = ⊥
CodeTerm żero (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm żero (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ṡuc term₁) (lookup index₂) = ⊥
CodeTerm (ṡuc term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (ṡuc term₁) żero = ⊥
CodeTerm (ṡuc term₁) (ṡuc term₂) = CodeTerm term₁ term₂
CodeTerm (ṡuc term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ṡuc term₁) (μ̇ term₂) = ⊥
CodeTerm (ṡuc term₁) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (ṡuc term₁) (case𝟘̇ term₂) = ⊥
CodeTerm (ṡuc term₁) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (ṡuc term₁) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ṡuc term₁) (ṗroj₁ term₂) = ⊥
CodeTerm (ṡuc term₁) (ṗroj₂ term₂) = ⊥
CodeTerm (ṡuc term₁) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (ṡuc term₁) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (lookup index₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (λ̇ term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (term₂₁ · term₂₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) żero = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (ṡuc term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ × CodeTerm term₁₃ term₂₃
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (μ̇ term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (prim m) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) ẑero = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (ŝuc term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (case𝟘̇ term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) ṫt = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (i̇nj₁ term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (i̇nj₂ term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (ṗroj₁ term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (ṗroj₂ term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) [̇] = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (μ̇ term₁) (lookup index₂) = ⊥
CodeTerm (μ̇ term₁) (λ̇ term₂) = ⊥
CodeTerm (μ̇ term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (μ̇ term₁) żero = ⊥
CodeTerm (μ̇ term₁) (ṡuc term₂) = ⊥
CodeTerm (μ̇ term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (μ̇ term₁) (μ̇ term₂) = CodeTerm term₁ term₂
CodeTerm (μ̇ term₁) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (μ̇ term₁) (prim m) = ⊥
CodeTerm (μ̇ term₁) ẑero = ⊥
CodeTerm (μ̇ term₁) (ŝuc term₂) = ⊥
CodeTerm (μ̇ term₁) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (μ̇ term₁) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (μ̇ term₁) (case𝟘̇ term₂) = ⊥
CodeTerm (μ̇ term₁) ṫt = ⊥
CodeTerm (μ̇ term₁) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (μ̇ term₁) (i̇nj₁ term₂) = ⊥
CodeTerm (μ̇ term₁) (i̇nj₂ term₂) = ⊥
CodeTerm (μ̇ term₁) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (μ̇ term₁) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (μ̇ term₁) (ṗroj₁ term₂) = ⊥
CodeTerm (μ̇ term₁) (ṗroj₂ term₂) = ⊥
CodeTerm (μ̇ term₁) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (μ̇ term₁) [̇] = ⊥
CodeTerm (μ̇ term₁) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (μ̇ term₁) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (lookup index₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (λ̇ term₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (term₂₁ · term₂₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) żero = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (ṡuc term₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (μ̇ term₂) = ⊥
CodeTerm (l̇et {A = A₁} term₁₁ term₁₂) (l̇et {A = A₂} term₂₁ term₂₂) = Σ (A₁ ≡ A₂) λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ }
CodeTerm (l̇et term₁₁ term₁₂) (prim m) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) ẑero = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (ŝuc term₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (case𝟘̇ term₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) ṫt = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (i̇nj₁ term₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (i̇nj₂ term₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (ṗroj₁ term₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (ṗroj₂ term₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) [̇] = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (l̇et term₁₁ term₁₂) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (prim n) (lookup index₂) = ⊥
CodeTerm (prim n) (term₂₁ · term₂₂) = ⊥
CodeTerm (prim n) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (prim n) (μ̇ term₂) = ⊥
CodeTerm (prim n) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (prim n) (prim m) = n ≡ m
CodeTerm (prim n) ẑero = ⊥
CodeTerm (prim n) (ŝuc term₂) = ⊥
CodeTerm (prim n) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (prim n) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (prim n) (case𝟘̇ term₂) = ⊥
CodeTerm (prim n) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (prim n) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (prim n) (ṗroj₁ term₂) = ⊥
CodeTerm (prim n) (ṗroj₂ term₂) = ⊥
CodeTerm (prim n) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (prim n) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm ẑero (lookup index₂) = ⊥
CodeTerm ẑero (term₂₁ · term₂₂) = ⊥
CodeTerm ẑero (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm ẑero (μ̇ term₂) = ⊥
CodeTerm ẑero (l̇et term₂₁ term₂₂) = ⊥
CodeTerm ẑero (prim m) = ⊥
CodeTerm ẑero ẑero = ⊤
CodeTerm ẑero (ŝuc term₂) = ⊥
CodeTerm ẑero (term₂₁ +̂ term₂₂) = ⊥
CodeTerm ẑero (term₂₁ *̂ term₂₂) = ⊥
CodeTerm ẑero (case𝟘̇ term₂) = ⊥
CodeTerm ẑero (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm ẑero (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm ẑero (ṗroj₁ term₂) = ⊥
CodeTerm ẑero (ṗroj₂ term₂) = ⊥
CodeTerm ẑero (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm ẑero (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ŝuc term₁) (lookup index₂) = ⊥
CodeTerm (ŝuc term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (ŝuc term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ŝuc term₁) (μ̇ term₂) = ⊥
CodeTerm (ŝuc term₁) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (ŝuc term₁) (prim m) = ⊥
CodeTerm (ŝuc term₁) ẑero = ⊥
CodeTerm (ŝuc term₁) (ŝuc term₂) = CodeTerm term₁ term₂
CodeTerm (ŝuc term₁) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (ŝuc term₁) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (ŝuc term₁) (case𝟘̇ term₂) = ⊥
CodeTerm (ŝuc term₁) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (ŝuc term₁) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ŝuc term₁) (ṗroj₁ term₂) = ⊥
CodeTerm (ŝuc term₁) (ṗroj₂ term₂) = ⊥
CodeTerm (ŝuc term₁) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (ŝuc term₁) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (lookup index₂) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (term₂₁ · term₂₂) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (μ̇ term₂) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (prim m) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) ẑero = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (ŝuc term₂) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (term₂₁ +̂ term₂₂) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂
CodeTerm (term₁₁ +̂ term₁₂) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (case𝟘̇ term₂) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (ṗroj₁ term₂) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (ṗroj₂ term₂) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ +̂ term₁₂) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (lookup index₂) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (term₂₁ · term₂₂) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (μ̇ term₂) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (prim m) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) ẑero = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (ŝuc term₂) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (term₂₁ *̂ term₂₂) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂
CodeTerm (term₁₁ *̂ term₁₂) (case𝟘̇ term₂) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (ṗroj₁ term₂) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (ṗroj₂ term₂) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ *̂ term₁₂) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (case𝟘̇ term₁) (lookup index₂) = ⊥
CodeTerm (case𝟘̇ term₁) (λ̇ term₂) = ⊥
CodeTerm (case𝟘̇ term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (case𝟘̇ term₁) żero = ⊥
CodeTerm (case𝟘̇ term₁) (ṡuc term₂) = ⊥
CodeTerm (case𝟘̇ term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (case𝟘̇ term₁) (μ̇ term₂) = ⊥
CodeTerm (case𝟘̇ term₁) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (case𝟘̇ term₁) (prim m) = ⊥
CodeTerm (case𝟘̇ term₁) ẑero = ⊥
CodeTerm (case𝟘̇ term₁) (ŝuc term₂) = ⊥
CodeTerm (case𝟘̇ term₁) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (case𝟘̇ term₁) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (case𝟘̇ term₁) (case𝟘̇ term₂) = CodeTerm term₁ term₂
CodeTerm (case𝟘̇ term₁) ṫt = ⊥
CodeTerm (case𝟘̇ term₁) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (case𝟘̇ term₁) (i̇nj₁ term₂) = ⊥
CodeTerm (case𝟘̇ term₁) (i̇nj₂ term₂) = ⊥
CodeTerm (case𝟘̇ term₁) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (case𝟘̇ term₁) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (case𝟘̇ term₁) (ṗroj₁ term₂) = ⊥
CodeTerm (case𝟘̇ term₁) (ṗroj₂ term₂) = ⊥
CodeTerm (case𝟘̇ term₁) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (case𝟘̇ term₁) [̇] = ⊥
CodeTerm (case𝟘̇ term₁) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (case𝟘̇ term₁) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm ṫt (lookup index₂) = ⊥
CodeTerm ṫt (term₂₁ · term₂₂) = ⊥
CodeTerm ṫt (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm ṫt (μ̇ term₂) = ⊥
CodeTerm ṫt (l̇et term₂₁ term₂₂) = ⊥
CodeTerm ṫt (case𝟘̇ term₂) = ⊥
CodeTerm ṫt ṫt = ⊤
CodeTerm ṫt (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm ṫt (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm ṫt (ṗroj₁ term₂) = ⊥
CodeTerm ṫt (ṗroj₂ term₂) = ⊥
CodeTerm ṫt (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm ṫt (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (lookup index₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (λ̇ term₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (term₂₁ · term₂₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) żero = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (ṡuc term₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (μ̇ term₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (prim m) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) ẑero = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (ŝuc term₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (case𝟘̇ term₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) ṫt = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (case𝟙̇ term₂₁ term₂₂) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂
CodeTerm (case𝟙̇ term₁₁ term₁₂) (i̇nj₁ term₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (i̇nj₂ term₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (ṗroj₁ term₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (ṗroj₂ term₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) [̇] = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (case𝟙̇ term₁₁ term₁₂) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (i̇nj₁ term₁) (lookup index₂) = ⊥
CodeTerm (i̇nj₁ term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (i̇nj₁ term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (i̇nj₁ term₁) (μ̇ term₂) = ⊥
CodeTerm (i̇nj₁ term₁) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (i̇nj₁ term₁) (case𝟘̇ term₂) = ⊥
CodeTerm (i̇nj₁ term₁) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (i̇nj₁ term₁) (i̇nj₁ term₂) = CodeTerm term₁ term₂
CodeTerm (i̇nj₁ term₁) (i̇nj₂ term₂) = ⊥
CodeTerm (i̇nj₁ term₁) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (i̇nj₁ term₁) (ṗroj₁ term₂) = ⊥
CodeTerm (i̇nj₁ term₁) (ṗroj₂ term₂) = ⊥
CodeTerm (i̇nj₁ term₁) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (i̇nj₁ term₁) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (i̇nj₂ term₁) (lookup index₂) = ⊥
CodeTerm (i̇nj₂ term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (i̇nj₂ term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (i̇nj₂ term₁) (μ̇ term₂) = ⊥
CodeTerm (i̇nj₂ term₁) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (i̇nj₂ term₁) (case𝟘̇ term₂) = ⊥
CodeTerm (i̇nj₂ term₁) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (i̇nj₂ term₁) (i̇nj₁ term₂) = ⊥
CodeTerm (i̇nj₂ term₁) (i̇nj₂ term₂) = CodeTerm term₁ term₂
CodeTerm (i̇nj₂ term₁) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (i̇nj₂ term₁) (ṗroj₁ term₂) = ⊥
CodeTerm (i̇nj₂ term₁) (ṗroj₂ term₂) = ⊥
CodeTerm (i̇nj₂ term₁) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (i̇nj₂ term₁) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (lookup index₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (λ̇ term₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (term₂₁ · term₂₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) żero = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (ṡuc term₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃₄) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (μ̇ term₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (prim m) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) ẑero = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (ŝuc term₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (case𝟘̇ term₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) ṫt = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (i̇nj₁ term₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (i̇nj₂ term₂) = ⊥
CodeTerm (case+̇ {A = A₁} {B = B₁} term₁₁ term₁₂ term₁₃) (case+̇ {A = A₂} {B = B₂} term₂₁ term₂₂ term₂₃) = Σ (A₁ ≡ A₂) λ { refl → Σ (B₁ ≡ B₂) λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ × CodeTerm term₁₃ term₂₃ } }
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (ṗroj₁ term₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (ṗroj₂ term₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) [̇] = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (lookup index₂) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (term₂₁ · term₂₂) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (μ̇ term₂) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (case𝟘̇ term₂) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (term₂₁ ,̇ term₂₂) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂
CodeTerm (term₁₁ ,̇ term₁₂) (ṗroj₁ term₂) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (ṗroj₂ term₂) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ ,̇ term₁₂) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ṗroj₁ term₁) (lookup index₂) = ⊥
CodeTerm (ṗroj₁ term₁) (λ̇ term₂) = ⊥
CodeTerm (ṗroj₁ term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (ṗroj₁ term₁) żero = ⊥
CodeTerm (ṗroj₁ term₁) (ṡuc term₂) = ⊥
CodeTerm (ṗroj₁ term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ṗroj₁ term₁) (μ̇ term₂) = ⊥
CodeTerm (ṗroj₁ term₁) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (ṗroj₁ term₁) (prim m) = ⊥
CodeTerm (ṗroj₁ term₁) ẑero = ⊥
CodeTerm (ṗroj₁ term₁) (ŝuc term₂) = ⊥
CodeTerm (ṗroj₁ term₁) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (ṗroj₁ term₁) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (ṗroj₁ term₁) (case𝟘̇ term₂) = ⊥
CodeTerm (ṗroj₁ term₁) ṫt = ⊥
CodeTerm (ṗroj₁ term₁) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (ṗroj₁ term₁) (i̇nj₁ term₂) = ⊥
CodeTerm (ṗroj₁ term₁) (i̇nj₂ term₂) = ⊥
CodeTerm (ṗroj₁ term₁) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ṗroj₁ term₁) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (ṗroj₁ {B = B₁} term₁) (ṗroj₁ {B = B₂} term₂) = Σ (B₁ ≡ B₂) λ { refl → CodeTerm term₁ term₂ }
CodeTerm (ṗroj₁ term₁) (ṗroj₂ term₂) = ⊥
CodeTerm (ṗroj₁ term₁) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (ṗroj₁ term₁) [̇] = ⊥
CodeTerm (ṗroj₁ term₁) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (ṗroj₁ term₁) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ṗroj₂ term₁) (lookup index₂) = ⊥
CodeTerm (ṗroj₂ term₁) (λ̇ term₂) = ⊥
CodeTerm (ṗroj₂ term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (ṗroj₂ term₁) żero = ⊥
CodeTerm (ṗroj₂ term₁) (ṡuc term₂) = ⊥
CodeTerm (ṗroj₂ term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ṗroj₂ term₁) (μ̇ term₂) = ⊥
CodeTerm (ṗroj₂ term₁) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (ṗroj₂ term₁) (prim m) = ⊥
CodeTerm (ṗroj₂ term₁) ẑero = ⊥
CodeTerm (ṗroj₂ term₁) (ŝuc term₂) = ⊥
CodeTerm (ṗroj₂ term₁) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (ṗroj₂ term₁) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (ṗroj₂ term₁) (case𝟘̇ term₂) = ⊥
CodeTerm (ṗroj₂ term₁) ṫt = ⊥
CodeTerm (ṗroj₂ term₁) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (ṗroj₂ term₁) (i̇nj₁ term₂) = ⊥
CodeTerm (ṗroj₂ term₁) (i̇nj₂ term₂) = ⊥
CodeTerm (ṗroj₂ term₁) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ṗroj₂ term₁) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (ṗroj₂ term₁) (ṗroj₁ term₂) = ⊥
CodeTerm (ṗroj₂ {A = A₁} term₁) (ṗroj₂ {A = A₂} term₂) = Σ (A₁ ≡ A₂) λ { refl → CodeTerm term₁ term₂ }
CodeTerm (ṗroj₂ term₁) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (ṗroj₂ term₁) [̇] = ⊥
CodeTerm (ṗroj₂ term₁) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (ṗroj₂ term₁) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (lookup index₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (λ̇ term₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (term₂₁ · term₂₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) żero = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (ṡuc term₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (μ̇ term₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (prim m) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) ẑero = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (ŝuc term₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (case𝟘̇ term₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) ṫt = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (i̇nj₁ term₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (i̇nj₂ term₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (ṗroj₁ term₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (ṗroj₂ term₂) = ⊥
CodeTerm (case×̇ {A = A₁} {B = B₁} term₁₁ term₁₂) (case×̇ {A = A₂} {B = B₂} term₂₁ term₂₂) = Σ (A₁ ≡ A₂) λ { refl → Σ (B₁ ≡ B₂) λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ } }
CodeTerm (case×̇ term₁₁ term₁₂) [̇] = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (case×̇ term₁₁ term₁₂) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm [̇] (lookup index₂) = ⊥
CodeTerm [̇] (term₂₁ · term₂₂) = ⊥
CodeTerm [̇] (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm [̇] (μ̇ term₂) = ⊥
CodeTerm [̇] (l̇et term₂₁ term₂₂) = ⊥
CodeTerm [̇] (case𝟘̇ term₂) = ⊥
CodeTerm [̇] (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm [̇] (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm [̇] (ṗroj₁ term₂) = ⊥
CodeTerm [̇] (ṗroj₂ term₂) = ⊥
CodeTerm [̇] (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm [̇] [̇] = ⊤
CodeTerm [̇] (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm [̇] (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (lookup index₂) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (term₂₁ · term₂₂) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (μ̇ term₂) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (case𝟘̇ term₂) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (ṗroj₁ term₂) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (ṗroj₂ term₂) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) [̇] = ⊥
CodeTerm (term₁₁ ∷̇ term₁₂) (term₂₁ ∷̇ term₂₂) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂
CodeTerm (term₁₁ ∷̇ term₁₂) (caseL̇ist term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (lookup index₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (λ̇ term₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (term₂₁ · term₂₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) żero = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (ṡuc term₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (μ̇ term₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (l̇et term₂₁ term₂₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (prim m) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) ẑero = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (ŝuc term₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (term₂₁ +̂ term₂₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (term₂₁ *̂ term₂₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (case𝟘̇ term₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) ṫt = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (case𝟙̇ term₂₁ term₂₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (i̇nj₁ term₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (i̇nj₂ term₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (case+̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (term₂₁ ,̇ term₂₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (ṗroj₁ term₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (ṗroj₂ term₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (case×̇ term₂₁ term₂₂) = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) [̇] = ⊥
CodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (term₂₁ ∷̇ term₂₂) = ⊥
CodeTerm (caseL̇ist {A = A₁} term₁₁ term₁₂ term₁₃) (caseL̇ist {A = A₂} term₂₁ term₂₂ term₂₃) = Σ (A₁ ≡ A₂) λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ × CodeTerm term₁₃ term₂₃ }

-- CodeTerm : {Γ : Context} → {A : Type} → (term₁ term₂ : Γ ⊢ A) → Set
-- CodeTerm (lookup index₁) (lookup index₂) = index₁ ≡ index₂
-- CodeTerm (λ̇ term₁) (λ̇ term₂) = CodeTerm term₁ term₂
-- CodeTerm (_·_ {A = A₁} term₁₁ term₁₂) (_·_ {A = A₂} term₂₁ term₂₂) = Σ (A₁ ≡ A₂) (λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ })
-- CodeTerm żero żero = ⊤
-- CodeTerm (ṡuc term₁) (ṡuc term₂) = CodeTerm term₁ term₂
-- CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ × CodeTerm term₁₃ term₂₃
-- CodeTerm (μ̇ term₁) (μ̇ term₂) = CodeTerm term₁ term₂
-- CodeTerm (l̇et {A = A₁} term₁₁ term₁₂) (l̇et {A = A₂} term₂₁ term₂₂) = Σ (A₁ ≡ A₂) λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ }
-- CodeTerm (prim n) (prim m) = n ≡ m
-- CodeTerm ẑero ẑero = ⊤
-- CodeTerm (ŝuc term₁) (ŝuc term₂) = CodeTerm term₁ term₂
-- CodeTerm (term₁₁ +̂ term₁₂) (term₂₁ +̂ term₂₂) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂
-- CodeTerm (term₁₁ *̂ term₁₂) (term₂₁ *̂ term₂₂) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂
-- CodeTerm (case𝟘̇ term₁) (case𝟘̇ term₂) = CodeTerm term₁ term₂
-- CodeTerm ṫt ṫt = ⊤
-- CodeTerm (case𝟙̇ term₁₁ term₁₂) (case𝟙̇ term₂₁ term₂₂) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂
-- CodeTerm (i̇nj₁ term₁) (i̇nj₁ term₂) = CodeTerm term₁ term₂
-- CodeTerm (i̇nj₂ term₁) (i̇nj₂ term₂) = CodeTerm term₁ term₂
-- CodeTerm (case+̇ {A = A₁} {B = B₁} term₁₁ term₁₂ term₁₃) (case+̇ {A = A₂} {B = B₂} term₂₁ term₂₂ term₂₃) = Σ (A₁ ≡ A₂) λ { refl → Σ (B₁ ≡ B₂) λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ × CodeTerm term₁₃ term₂₃ } }
-- CodeTerm (term₁₁ ,̇ term₁₂) (term₂₁ ,̇ term₂₂) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂
-- CodeTerm (ṗroj₁ {B = B₁} term₁) (ṗroj₁ {B = B₂} term₂) = Σ (B₁ ≡ B₂) λ { refl → CodeTerm term₁ term₂ }
-- CodeTerm (ṗroj₂ {A = A₁} term₁) (ṗroj₂ {A = A₂} term₂) = Σ (A₁ ≡ A₂) λ { refl → CodeTerm term₁ term₂ }
-- CodeTerm (case×̇ {A = A₁} {B = B₁} term₁₁ term₁₂) (case×̇ {A = A₂} {B = B₂} term₂₁ term₂₂) = Σ (A₁ ≡ A₂) λ { refl → Σ (B₁ ≡ B₂) λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ } }
-- CodeTerm [̇] [̇] = ⊤
-- CodeTerm (term₁₁ ∷̇ term₁₂) (term₂₁ ∷̇ term₂₂) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂
-- CodeTerm (caseL̇ist {A = A₁} term₁₁ term₁₂ term₁₃) (caseL̇ist {A = A₂} term₂₁ term₂₂ term₂₃) = Σ (A₁ ≡ A₂) λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ × CodeTerm term₁₃ term₂₃ }
-- CodeTerm _ _ = ⊥

rTerm : {Γ : Context} → {A : Type} → (term : Γ ⊢ A) → CodeTerm term term
rTerm (lookup index) = refl
rTerm (λ̇ term) = rTerm term
rTerm (term₁ · term₂) = refl , rTerm term₁ , rTerm term₂
rTerm żero = tt
rTerm (ṡuc term) = rTerm term
rTerm (caseℕ̇ term₁ term₂ term₃) = rTerm term₁ , rTerm term₂ , rTerm term₃
rTerm (μ̇ term) = rTerm term
rTerm (l̇et term₁ term₂) = refl , rTerm term₁ , rTerm term₂
rTerm (prim n) = refl
rTerm ẑero = tt
rTerm (ŝuc term) = rTerm term
rTerm (term₁ +̂ term₂) = rTerm term₁ , rTerm term₂
rTerm (term₁ *̂ term₂) = rTerm term₁ , rTerm term₂
rTerm (case𝟘̇ term) = rTerm term
rTerm ṫt = tt
rTerm (case𝟙̇ term₁ term₂) = rTerm term₁ , rTerm term₂
rTerm (i̇nj₁ term) = rTerm term
rTerm (i̇nj₂ term) = rTerm term
rTerm (case+̇ term₁ term₂ term₃) = refl , refl , rTerm term₁ , rTerm term₂ , rTerm term₃
rTerm (term₁ ,̇ term₂) = rTerm term₁ , rTerm term₂
rTerm (ṗroj₁ term) = refl , rTerm term
rTerm (ṗroj₂ term) = refl , rTerm term
rTerm (case×̇ term₁ term₂) = refl , refl , rTerm term₁ , rTerm term₂
rTerm [̇] = tt
rTerm (term₁ ∷̇ term₂) = rTerm term₁ , rTerm term₂
rTerm (caseL̇ist term₁ term₂ term₃) = refl , rTerm term₁ , rTerm term₂ , rTerm term₃

Term-eq≅CodeTerm : {Γ : Context} → {A : Type}
    → (term₁ term₂ : Γ ⊢ A)
    → term₁ ≡ term₂ ≅ CodeTerm term₁ term₂
Term-eq≅CodeTerm term₁ term₂ = record {
        to = encodeTerm term₁ term₂;
        from = decodeTerm term₁ term₂;
        from∘to = decodeTerm-encodeTerm term₁ term₂;
        to∘from = encodeTerm-decodeTerm term₁ term₂
    } where
        encodeTerm : {Γ : Context} → {A : Type}
            → (term₁ term₂ : Γ ⊢ A)
            → term₁ ≡ term₂ → CodeTerm term₁ term₂
        encodeTerm term₁ .term₁ refl = rTerm term₁

        decodeTerm : {Γ : Context} → {A : Type}
            → (term₁ term₂ : Γ ⊢ A)
            → CodeTerm term₁ term₂ → term₁ ≡ term₂
        decodeTerm (lookup index₁) (lookup .index₁) refl = refl
        decodeTerm (λ̇ term₁) (λ̇ term₂) code = cong λ̇_ (decodeTerm term₁ term₂ code)
        decodeTerm (term₁₁ · term₁₂) (term₂₁ · term₂₂) (refl , code₁ , code₂) = cong₂ _·_ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂)
        decodeTerm żero żero tt = refl
        decodeTerm (ṡuc term₁) (ṡuc term₂) code = cong ṡuc_ (decodeTerm term₁ term₂ code)
        decodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) (code₁ , code₂ , code₃) = cong₃ caseℕ̇ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (decodeTerm term₁₃ term₂₃ code₃)
        decodeTerm (μ̇ term₁) (μ̇ term₂) code = cong μ̇_ (decodeTerm term₁ term₂ code)
        decodeTerm (l̇et term₁₁ term₁₂) (l̇et term₂₁ term₂₂) (refl , code₁ , code₂) = cong₂ l̇et (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂)
        decodeTerm (prim n) (prim .n) refl = refl
        decodeTerm ẑero ẑero tt = refl
        decodeTerm (ŝuc term₁) (ŝuc term₂) code = cong ŝuc_ (decodeTerm term₁ term₂ code)
        decodeTerm (term₁₁ +̂ term₁₂) (term₂₁ +̂ term₂₂) (code₁ , code₂) = cong₂ _+̂_ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂)
        decodeTerm (term₁₁ *̂ term₁₂) (term₂₁ *̂ term₂₂) (code₁ , code₂) = cong₂ _*̂_ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂)
        decodeTerm (case𝟘̇ term₁) (case𝟘̇ term₂) code = cong case𝟘̇ (decodeTerm term₁ term₂ code)
        decodeTerm ṫt ṫt tt = refl
        decodeTerm (case𝟙̇ term₁₁ term₁₂) (case𝟙̇ term₂₁ term₂₂) (code₁ , code₂) = cong₂ case𝟙̇ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂)
        decodeTerm (i̇nj₁ term₁) (i̇nj₁ term₂) code = cong i̇nj₁ (decodeTerm term₁ term₂ code)
        decodeTerm (i̇nj₂ term₁) (i̇nj₂ term₂) code = cong i̇nj₂ (decodeTerm term₁ term₂ code)
        decodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (case+̇ term₂₁ term₂₂ term₂₃) (refl , refl , code₁ , code₂ , code₃) = cong₃ case+̇ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (decodeTerm term₁₃ term₂₃ code₃)
        decodeTerm (term₁₁ ,̇ term₁₂) (term₂₁ ,̇ term₂₂) (code₁ , code₂) = cong₂ _,̇_ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂)
        decodeTerm (ṗroj₁ term₁) (ṗroj₁ term₂) (refl , code) = cong ṗroj₁ (decodeTerm term₁ term₂ code)
        decodeTerm (ṗroj₂ term₁) (ṗroj₂ term₂) (refl , code) = cong ṗroj₂ (decodeTerm term₁ term₂ code)
        decodeTerm (case×̇ term₁₁ term₁₂) (case×̇ term₂₁ term₂₂) (refl , refl , code₁ , code₂) = cong₂ case×̇ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂)
        decodeTerm [̇] [̇] tt = refl
        decodeTerm (term₁₁ ∷̇ term₁₂) (term₂₁ ∷̇ term₂₂) (code₁ , code₂) = cong₂ _∷̇_ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂)
        decodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (caseL̇ist term₂₁ term₂₂ term₂₃) (refl , code₁ , code₂ , code₃) = cong₃ caseL̇ist (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (decodeTerm term₁₃ term₂₃ code₃)

        decodeTerm-encodeTerm : {Γ : Context} → {A : Type}
            → (term₁ term₂ : Γ ⊢ A)
            → (p : term₁ ≡ term₂) → decodeTerm term₁ term₂ (encodeTerm term₁ term₂ p) ≡ p
        decodeTerm-encodeTerm (lookup index₁) .(lookup index₁) refl = refl
        decodeTerm-encodeTerm (λ̇ term₁) .(λ̇ term₁) refl = cong (cong λ̇_) (decodeTerm-encodeTerm term₁ term₁ refl)
        decodeTerm-encodeTerm (term₁₁ · term₁₂) .(term₁₁ · term₁₂) refl = cong₂ (cong₂ _·_) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl)
        decodeTerm-encodeTerm żero .żero refl = refl
        decodeTerm-encodeTerm (ṡuc term₁) .(ṡuc term₁) refl = cong (cong ṡuc_) (decodeTerm-encodeTerm term₁ term₁ refl)
        decodeTerm-encodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) .(caseℕ̇ term₁₁ term₁₂ term₁₃) refl = cong₃ (cong₃ caseℕ̇) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl) (decodeTerm-encodeTerm term₁₃ term₁₃ refl)
        decodeTerm-encodeTerm (μ̇ term₁) .(μ̇ term₁) refl = cong (cong μ̇_) (decodeTerm-encodeTerm term₁ term₁ refl)
        decodeTerm-encodeTerm (l̇et term₁₁ term₁₂) .(l̇et term₁₁ term₁₂) refl = cong₂ (cong₂ l̇et) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl)
        decodeTerm-encodeTerm (prim n) .(prim n) refl = refl
        decodeTerm-encodeTerm ẑero .ẑero refl = refl
        decodeTerm-encodeTerm (ŝuc term₁) .(ŝuc term₁) refl = cong (cong ŝuc_) (decodeTerm-encodeTerm term₁ term₁ refl)
        decodeTerm-encodeTerm (term₁₁ +̂ term₁₂) .(term₁₁ +̂ term₁₂) refl = cong₂ (cong₂ _+̂_) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl)
        decodeTerm-encodeTerm (term₁₁ *̂ term₁₂) .(term₁₁ *̂ term₁₂) refl = cong₂ (cong₂ _*̂_) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl)
        decodeTerm-encodeTerm (case𝟘̇ term₁) .(case𝟘̇ term₁) refl = cong (cong case𝟘̇) (decodeTerm-encodeTerm term₁ term₁ refl)
        decodeTerm-encodeTerm ṫt .ṫt refl = refl
        decodeTerm-encodeTerm (case𝟙̇ term₁₁ term₁₂) .(case𝟙̇ term₁₁ term₁₂) refl = cong₂ (cong₂ case𝟙̇) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl)
        decodeTerm-encodeTerm (i̇nj₁ term₁) .(i̇nj₁ term₁) refl = cong (cong i̇nj₁) (decodeTerm-encodeTerm term₁ term₁ refl)
        decodeTerm-encodeTerm (i̇nj₂ term₁) .(i̇nj₂ term₁) refl = cong (cong i̇nj₂) (decodeTerm-encodeTerm term₁ term₁ refl)
        decodeTerm-encodeTerm (case+̇ term₁₁ term₁₂ term₁₃) .(case+̇ term₁₁ term₁₂ term₁₃) refl = cong₃ (cong₃ case+̇) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl) (decodeTerm-encodeTerm term₁₃ term₁₃ refl)
        decodeTerm-encodeTerm (term₁₁ ,̇ term₁₂) .(term₁₁ ,̇ term₁₂) refl = cong₂ (cong₂ _,̇_) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl)
        decodeTerm-encodeTerm (ṗroj₁ term₁) .(ṗroj₁ term₁) refl = cong (cong ṗroj₁) (decodeTerm-encodeTerm term₁ term₁ refl)
        decodeTerm-encodeTerm (ṗroj₂ term₁) .(ṗroj₂ term₁) refl = cong (cong ṗroj₂) (decodeTerm-encodeTerm term₁ term₁ refl)
        decodeTerm-encodeTerm (case×̇ term₁₁ term₁₂) .(case×̇ term₁₁ term₁₂) refl = cong₂ (cong₂ case×̇) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl)
        decodeTerm-encodeTerm [̇] .[̇] refl = refl
        decodeTerm-encodeTerm (term₁₁ ∷̇ term₁₂) .(term₁₁ ∷̇ term₁₂) refl = cong₂ (cong₂ _∷̇_) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl)
        decodeTerm-encodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) .(caseL̇ist term₁₁ term₁₂ term₁₃) refl = cong₃ (cong₃ caseL̇ist) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl) (decodeTerm-encodeTerm term₁₃ term₁₃ refl)

        encodeTerm-decodeTerm : {Γ : Context} → {A : Type}
            → (term₁ term₂ : Γ ⊢ A)
            → (code : CodeTerm term₁ term₂) → encodeTerm term₁ term₂ (decodeTerm term₁ term₂ code) ≡ code
        encodeTerm-decodeTerm (lookup index₁) (lookup .index₁) refl = refl
        encodeTerm-decodeTerm (λ̇ term₁) (λ̇ term₂) code with decodeTerm term₁ term₂ code | encodeTerm-decodeTerm term₁ term₂ code
        ... | refl | refl = refl
        encodeTerm-decodeTerm (term₁₁ · term₁₂) (term₂₁ · term₂₂) (refl , code₁ , code₂)
            with
                decodeTerm term₁₁ term₂₁ code₁ |
                decodeTerm term₁₂ term₂₂ code₂ |
                encodeTerm-decodeTerm term₁₁ term₂₁ code₁ |
                encodeTerm-decodeTerm term₁₂ term₂₂ code₂
        ... | refl | refl | refl | refl = refl
        encodeTerm-decodeTerm żero żero tt = refl
        encodeTerm-decodeTerm (ṡuc term₁) (ṡuc term₂) code with decodeTerm term₁ term₂ code | encodeTerm-decodeTerm term₁ term₂ code
        ... | refl | refl = refl
        encodeTerm-decodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) (code₁ , code₂ , code₃)
            with
                decodeTerm term₁₁ term₂₁ code₁ |
                decodeTerm term₁₂ term₂₂ code₂ |
                decodeTerm term₁₃ term₂₃ code₃ |
                encodeTerm-decodeTerm term₁₁ term₂₁ code₁ |
                encodeTerm-decodeTerm term₁₂ term₂₂ code₂ |
                encodeTerm-decodeTerm term₁₃ term₂₃ code₃
        ... | refl | refl | refl | refl | refl | refl = refl
        encodeTerm-decodeTerm (μ̇ term₁) (μ̇ term₂) code with decodeTerm term₁ term₂ code | encodeTerm-decodeTerm term₁ term₂ code
        ... | refl | refl = refl
        encodeTerm-decodeTerm (l̇et term₁₁ term₁₂) (l̇et term₂₁ term₂₂) (refl , code₁ , code₂)
            with
                decodeTerm term₁₁ term₂₁ code₁ |
                decodeTerm term₁₂ term₂₂ code₂ |
                encodeTerm-decodeTerm term₁₁ term₂₁ code₁ |
                encodeTerm-decodeTerm term₁₂ term₂₂ code₂
        ... | refl | refl | refl | refl = refl
        encodeTerm-decodeTerm (prim n) (prim .n) refl = refl
        encodeTerm-decodeTerm ẑero ẑero tt = refl
        encodeTerm-decodeTerm (ŝuc term₁) (ŝuc term₂) code with decodeTerm term₁ term₂ code | encodeTerm-decodeTerm term₁ term₂ code
        ... | refl | refl = refl
        encodeTerm-decodeTerm (term₁₁ +̂ term₁₂) (term₂₁ +̂ term₂₂) (code₁ , code₂)
            with
                decodeTerm term₁₁ term₂₁ code₁ |
                decodeTerm term₁₂ term₂₂ code₂ |
                encodeTerm-decodeTerm term₁₁ term₂₁ code₁ |
                encodeTerm-decodeTerm term₁₂ term₂₂ code₂
        ... | refl | refl | refl | refl = refl
        encodeTerm-decodeTerm (term₁₁ *̂ term₁₂) (term₂₁ *̂ term₂₂) (code₁ , code₂)
            with
                decodeTerm term₁₁ term₂₁ code₁ |
                decodeTerm term₁₂ term₂₂ code₂ |
                encodeTerm-decodeTerm term₁₁ term₂₁ code₁ |
                encodeTerm-decodeTerm term₁₂ term₂₂ code₂
        ... | refl | refl | refl | refl = refl
        encodeTerm-decodeTerm (case𝟘̇ term₁) (case𝟘̇ term₂) code with decodeTerm term₁ term₂ code | encodeTerm-decodeTerm term₁ term₂ code
        ... | refl | refl = refl
        encodeTerm-decodeTerm ṫt ṫt tt = refl
        encodeTerm-decodeTerm (case𝟙̇ term₁₁ term₁₂) (case𝟙̇ term₂₁ term₂₂) (code₁ , code₂)
            with
                decodeTerm term₁₁ term₂₁ code₁ |
                decodeTerm term₁₂ term₂₂ code₂ |
                encodeTerm-decodeTerm term₁₁ term₂₁ code₁ |
                encodeTerm-decodeTerm term₁₂ term₂₂ code₂
        ... | refl | refl | refl | refl = refl
        encodeTerm-decodeTerm (i̇nj₁ term₁) (i̇nj₁ term₂) code with decodeTerm term₁ term₂ code | encodeTerm-decodeTerm term₁ term₂ code
        ... | refl | refl = refl
        encodeTerm-decodeTerm (i̇nj₂ term₁) (i̇nj₂ term₂) code with decodeTerm term₁ term₂ code | encodeTerm-decodeTerm term₁ term₂ code
        ... | refl | refl = refl
        encodeTerm-decodeTerm (case+̇ term₁₁ term₁₂ term₁₃) (case+̇ term₂₁ term₂₂ term₂₃) (refl , refl , code₁ , code₂ , code₃)
            with
                decodeTerm term₁₁ term₂₁ code₁ |
                decodeTerm term₁₂ term₂₂ code₂ |
                decodeTerm term₁₃ term₂₃ code₃ |
                encodeTerm-decodeTerm term₁₁ term₂₁ code₁ |
                encodeTerm-decodeTerm term₁₂ term₂₂ code₂ |
                encodeTerm-decodeTerm term₁₃ term₂₃ code₃
        ... | refl | refl | refl | refl | refl | refl = refl
        encodeTerm-decodeTerm (term₁₁ ,̇ term₁₂) (term₂₁ ,̇ term₂₂) (code₁ , code₂)
            with
                decodeTerm term₁₁ term₂₁ code₁ |
                decodeTerm term₁₂ term₂₂ code₂ |
                encodeTerm-decodeTerm term₁₁ term₂₁ code₁ |
                encodeTerm-decodeTerm term₁₂ term₂₂ code₂
        ... | refl | refl | refl | refl = refl
        encodeTerm-decodeTerm (ṗroj₁ term₁) (ṗroj₁ term₂) (refl , code) with decodeTerm term₁ term₂ code | encodeTerm-decodeTerm term₁ term₂ code
        ... | refl | refl = refl
        encodeTerm-decodeTerm (ṗroj₂ term₁) (ṗroj₂ term₂) (refl , code) with decodeTerm term₁ term₂ code | encodeTerm-decodeTerm term₁ term₂ code
        ... | refl | refl = refl
        encodeTerm-decodeTerm (case×̇ term₁₁ term₁₂) (case×̇ term₂₁ term₂₂) (refl , refl , code₁ , code₂)
            with
                decodeTerm term₁₁ term₂₁ code₁ |
                decodeTerm term₁₂ term₂₂ code₂ |
                encodeTerm-decodeTerm term₁₁ term₂₁ code₁ |
                encodeTerm-decodeTerm term₁₂ term₂₂ code₂
        ... | refl | refl | refl | refl = refl
        encodeTerm-decodeTerm [̇] [̇] tt = refl
        encodeTerm-decodeTerm (term₁₁ ∷̇ term₁₂) (term₂₁ ∷̇ term₂₂) (code₁ , code₂)
            with
                decodeTerm term₁₁ term₂₁ code₁ |
                decodeTerm term₁₂ term₂₂ code₂ |
                encodeTerm-decodeTerm term₁₁ term₂₁ code₁ |
                encodeTerm-decodeTerm term₁₂ term₂₂ code₂
        ... | refl | refl | refl | refl = refl
        encodeTerm-decodeTerm (caseL̇ist term₁₁ term₁₂ term₁₃) (caseL̇ist term₂₁ term₂₂ term₂₃) (refl , code₁ , code₂ , code₃)
            with
                decodeTerm term₁₁ term₂₁ code₁ |
                decodeTerm term₁₂ term₂₂ code₂ |
                decodeTerm term₁₃ term₂₃ code₃ |
                encodeTerm-decodeTerm term₁₁ term₂₁ code₁ |
                encodeTerm-decodeTerm term₁₂ term₂₂ code₂ |
                encodeTerm-decodeTerm term₁₃ term₂₃ code₃
        ... | refl | refl | refl | refl | refl | refl = refl

CodeTerm-Is-hProp : {Γ : Context} → {A : Type}
    → (term₁ term₂ : Γ ⊢ A)
    → Is-hProp (CodeTerm term₁ term₂)
CodeTerm-Is-hProp (lookup index₁) (lookup index₂) = Index-Is-hSet index₁ index₂
CodeTerm-Is-hProp (λ̇ term₁) (λ̇ term₂) = CodeTerm-Is-hProp term₁ term₂
CodeTerm-Is-hProp (_·_ {A = A₁} term₁₁ term₁₂) (_·_ {A = A₂} term₂₁ term₂₂) = Σ-Is-hProp (Type-Is-hSet A₁ A₂) λ { refl → ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (CodeTerm-Is-hProp term₁₂ term₂₂) }
CodeTerm-Is-hProp żero żero = ⊤-Is-hProp
CodeTerm-Is-hProp (ṡuc term₁) (ṡuc term₂) = CodeTerm-Is-hProp term₁ term₂
CodeTerm-Is-hProp (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (×-Is-hProp (CodeTerm-Is-hProp term₁₂ term₂₂) (CodeTerm-Is-hProp term₁₃ term₂₃))
CodeTerm-Is-hProp (μ̇ term₁) (μ̇ term₂) = CodeTerm-Is-hProp term₁ term₂
CodeTerm-Is-hProp (l̇et {A = A₁} term₁₁ term₁₂) (l̇et {A = A₂} term₂₁ term₂₂) = Σ-Is-hProp (Type-Is-hSet A₁ A₂) λ { refl → ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (CodeTerm-Is-hProp term₁₂ term₂₂) }
CodeTerm-Is-hProp (prim n) (prim m) = ℕ-Is-hSet n m
CodeTerm-Is-hProp ẑero ẑero = ⊤-Is-hProp
CodeTerm-Is-hProp (ŝuc term₁) (ŝuc term₂) = CodeTerm-Is-hProp term₁ term₂
CodeTerm-Is-hProp (term₁₁ +̂ term₁₂) (term₂₁ +̂ term₂₂) = ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (CodeTerm-Is-hProp term₁₂ term₂₂)
CodeTerm-Is-hProp (term₁₁ *̂ term₁₂) (term₂₁ *̂ term₂₂) = ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (CodeTerm-Is-hProp term₁₂ term₂₂)
CodeTerm-Is-hProp (case𝟘̇ term₁) (case𝟘̇ term₂) = CodeTerm-Is-hProp term₁ term₂
CodeTerm-Is-hProp ṫt ṫt = ⊤-Is-hProp
CodeTerm-Is-hProp (case𝟙̇ term₁₁ term₁₂) (case𝟙̇ term₂₁ term₂₂) = ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (CodeTerm-Is-hProp term₁₂ term₂₂)
CodeTerm-Is-hProp (i̇nj₁ term₁) (i̇nj₁ term₂) = CodeTerm-Is-hProp term₁ term₂
CodeTerm-Is-hProp (i̇nj₂ term₁) (i̇nj₂ term₂) = CodeTerm-Is-hProp term₁ term₂
CodeTerm-Is-hProp (case+̇ {A = A₁} {B = B₁} term₁₁ term₁₂ term₁₃) (case+̇ {A = A₂} {B = B₂} term₂₁ term₂₂ term₂₃) = Σ-Is-hProp (Type-Is-hSet A₁ A₂) λ { refl → Σ-Is-hProp (Type-Is-hSet B₁ B₂) λ { refl → ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (×-Is-hProp (CodeTerm-Is-hProp term₁₂ term₂₂) (CodeTerm-Is-hProp term₁₃ term₂₃)) } }
CodeTerm-Is-hProp (term₁₁ ,̇ term₁₂) (term₂₁ ,̇ term₂₂) = ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (CodeTerm-Is-hProp term₁₂ term₂₂)
CodeTerm-Is-hProp (ṗroj₁ {B = B₁} term₁) (ṗroj₁ {B = B₂} term₂) = Σ-Is-hProp (Type-Is-hSet B₁ B₂) λ { refl → CodeTerm-Is-hProp term₁ term₂ }
CodeTerm-Is-hProp (ṗroj₂ {A = A₁} term₁) (ṗroj₂ {A = A₂} term₂) = Σ-Is-hProp (Type-Is-hSet A₁ A₂) λ { refl → CodeTerm-Is-hProp term₁ term₂ }
CodeTerm-Is-hProp (case×̇ {A = A₁} {B = B₁} term₁₁ term₁₂) (case×̇ {A = A₂} {B = B₂} term₂₁ term₂₂) = Σ-Is-hProp (Type-Is-hSet A₁ A₂) λ { refl → Σ-Is-hProp (Type-Is-hSet B₁ B₂) λ { refl → ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (CodeTerm-Is-hProp term₁₂ term₂₂) } }
CodeTerm-Is-hProp [̇] [̇] = ⊤-Is-hProp
CodeTerm-Is-hProp (term₁₁ ∷̇ term₁₂) (term₂₁ ∷̇ term₂₂) = ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (CodeTerm-Is-hProp term₁₂ term₂₂)
CodeTerm-Is-hProp (caseL̇ist {A = A₁} term₁₁ term₁₂ term₁₃) (caseL̇ist {A = A₂} term₂₁ term₂₂ term₂₃) = Σ-Is-hProp (Type-Is-hSet A₁ A₂) λ { refl → ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (×-Is-hProp (CodeTerm-Is-hProp term₁₂ term₂₂) (CodeTerm-Is-hProp term₁₃ term₂₃)) }

Term-Is-hSet : {Γ : Context} → {A : Type} → Is-hSet (Γ ⊢ A)
Term-Is-hSet term₁ term₂ = ≅-Is-hProp (Term-eq≅CodeTerm term₁ term₂) (CodeTerm-Is-hProp term₁ term₂)
