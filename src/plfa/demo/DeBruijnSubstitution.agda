{-# OPTIONS --without-K #-}

module plfa.demo.DeBruijnSubstitution where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (T; not)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _<_; _<?_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; flip)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import plfa.part2.DeBruijn

-- useful congruences

cong₃ : {A B C D : Set}
    → (f : A → B → C → D)
    → {x₁ x₂ : A}
    → {y₁ y₂ : B}
    → {z₁ z₂ : C}
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → z₁ ≡ z₂
    → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
cong₃ f refl refl refl = refl

cong-extend : {Γ Δ : Context}
    → {σ₁ σ₂ : {A : Type} → Γ ∋ A → Δ ⊢ A}
    → (p : {A : Type} → (index : Γ ∋ A) → σ₁ index ≡ σ₂ index)
    → ({A B : Type} → (index : Γ ‚ B ∋ A) → extend σ₁ index ≡ extend σ₂ index)
cong-extend p here = refl
cong-extend p (there index) = cong shift (p index)

cong-substitute : {Γ Δ : Context}
    → {σ₁ σ₂ : {A : Type} → Γ ∋ A → Δ ⊢ A}
    → (p : {A : Type} → (index : Γ ∋ A) → σ₁ index ≡ σ₂ index)
    → {A : Type}
    → (term : Γ ⊢ A)
    → substitute σ₁ term ≡ substitute σ₂ term
cong-substitute p (lookup index) = p index
cong-substitute p (λ̇ term) = cong λ̇_ (cong-substitute (cong-extend p) term)
cong-substitute p (term₁ · term₂) = cong₂ _·_ (cong-substitute p term₁) (cong-substitute p term₂)
cong-substitute p żero = refl
cong-substitute p (ṡuc term) = cong ṡuc_ (cong-substitute p term)
cong-substitute p (caseℕ̇ term₁ term₂ term₃) = cong₃ caseℕ̇ (cong-substitute p term₁) (cong-substitute p term₂) (cong-substitute (cong-extend p) term₃)
cong-substitute p (μ̇ term) = cong μ̇_ (cong-substitute (cong-extend p) term)

-- lemma 1: substitute-shift

extend-compose : {Γ Δ Ε : Context}
    → {ρ : {A : Type} → Γ ∋ A → Δ ∋ A}
    → {σ : {A : Type} → Δ ∋ A → Ε ⊢ A}
    → {A B : Type}
    → (index : Γ ‚ B ∋ A)
    → ((extend σ) ∘ (extend-reindex ρ)) index ≡ extend (σ ∘ ρ) index
extend-compose here = refl
extend-compose (there index) = refl

substitute-compose : {Γ Δ Ε : Context}
    → {ρ : {A : Type} → Γ ∋ A → Δ ∋ A}
    → {σ : {A : Type} → Δ ∋ A → Ε ⊢ A}
    → {A : Type}
    → (term : Γ ⊢ A)
    → substitute σ (reindex-to-rebase ρ term) ≡ substitute (σ ∘ ρ) term
substitute-compose (lookup index) = refl
substitute-compose (λ̇ term) = cong λ̇_ (trans (substitute-compose term) (cong-substitute extend-compose term))
substitute-compose (term₁ · term₂) = cong₂ _·_ (substitute-compose term₁) (substitute-compose term₂)
substitute-compose żero = refl
substitute-compose (ṡuc term) = cong ṡuc_ (substitute-compose term)
substitute-compose (caseℕ̇ term₁ term₂ term₃) = cong₃ caseℕ̇ (substitute-compose term₁) (substitute-compose term₂) (trans (substitute-compose term₃) (cong-substitute extend-compose term₃))
substitute-compose (μ̇ term) = cong μ̇_ (trans (substitute-compose term) (cong-substitute extend-compose term))

extend-lookup : {Γ : Context} → {A B : Type}
    → (index : Γ ‚ B ∋ A)
    → extend lookup index ≡ lookup index
extend-lookup here = refl
extend-lookup (there index) = refl

substitute-lookup : {Γ : Context} → {A : Type}
    → (term : Γ ⊢ A)
    → substitute lookup term ≡ term
substitute-lookup (lookup index) = refl
substitute-lookup (λ̇ term) = cong λ̇_ (trans (cong-substitute extend-lookup term) (substitute-lookup term))
substitute-lookup (term₁ · term₂) = cong₂ _·_ (substitute-lookup term₁) (substitute-lookup term₂)
substitute-lookup żero = refl
substitute-lookup (ṡuc term) = cong ṡuc_ (substitute-lookup term)
substitute-lookup (caseℕ̇ term₁ term₂ term₃) = cong₃ caseℕ̇ (substitute-lookup term₁) (substitute-lookup term₂) (trans (cong-substitute extend-lookup term₃) (substitute-lookup term₃))
substitute-lookup (μ̇ term) = cong μ̇_ (trans (cong-substitute extend-lookup term) (substitute-lookup term))

substitute-shift : {Γ : Context} → {A B : Type}
    → (term₁ : Γ ⊢ A)
    → (term₂ : Γ ⊢ B)
    → (shift term₁) [ term₂ ] ≡ term₁
substitute-shift term₁ term₂ = trans (substitute-compose term₁) (substitute-lookup term₁)

-- lemma 2: substitute-substitute-compose
-- uses repeated extend-reindex and extend

extends-reindex : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ∋ A)
    → ({A : Type} → {Ε : Context} → Γ ‚‚ Ε ∋ A → Δ ‚‚ Ε ∋ A)
extends-reindex ρ {Ε = []} = ρ
extends-reindex ρ {Ε = Ε ‚ B} = extend-reindex (extends-reindex ρ)

extends : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ⊢ A)
    → ({A : Type} → {Ε : Context} → Γ ‚‚ Ε ∋ A → Δ ‚‚ Ε ⊢ A)
extends σ {Ε = []} = σ
extends σ {Ε = Ε ‚ B} = extend (extends σ)

insert-twice-index : {Γ Δ Ε : Context}
    → {A B C : Type}
    → (index : Γ ‚‚ Δ ‚‚ Ε ∋ A)
    → extends-reindex (there {B = C}) {Ε = Ε} (extends-reindex (extends-reindex (there {B = B}) {Ε = Δ}) {Ε = Ε} index) ≡ extends-reindex (extend-reindex (extends-reindex there)) (extends-reindex there index) -- (Γ ‚ B ‚‚ Δ) ‚ C ‚‚ Ε ∋ A
insert-twice-index {Ε = []} index = refl
insert-twice-index {Ε = Ε ‚ D} here = refl
insert-twice-index {Ε = Ε ‚ D} (there index) = cong there (insert-twice-index index)

insert-twice : {Γ Δ Ε : Context}
    → {A B C : Type}
    → (term : Γ ‚‚ Δ ‚‚ Ε ⊢ A)
    → reindex-to-rebase (extends-reindex (there {B = C}) {Ε = Ε}) (reindex-to-rebase (extends-reindex (extends-reindex (there {B = B}) {Ε = Δ}) {Ε = Ε}) term) ≡ reindex-to-rebase (extends-reindex (extend-reindex (extends-reindex there))) (reindex-to-rebase (extends-reindex there) term) -- (Γ ‚ B ‚‚ Δ) ‚ C ‚‚ Ε ⊢ A
insert-twice (lookup index) = cong lookup (insert-twice-index index)
insert-twice {Ε = Ε} {A = A₁ →̇ A₂} (λ̇ term) = cong λ̇_ (insert-twice {Ε = Ε ‚ A₁} term)
insert-twice (term₁ · term₂) = cong₂ _·_ (insert-twice term₁) (insert-twice term₂)
insert-twice żero = refl
insert-twice (ṡuc term) = cong ṡuc_ (insert-twice term)
insert-twice {Ε = Ε} {A = A} (caseℕ̇ term₁ term₂ term₃) = cong₃ caseℕ̇ (insert-twice term₁) (insert-twice term₂) (insert-twice {Ε = Ε ‚ ℕ̇} term₃)
insert-twice {Ε = Ε} {A = A} (μ̇ term) = cong μ̇_ (insert-twice {Ε = Ε ‚ A} term)

insert-substitute-index : {Γ Δ Ε : Context}
    → {A B : Type}
    → {σ : {A : Type} → Γ ∋ A → Δ ⊢ A}
    → (index : Γ ‚‚ Ε ∋ A)
    → extends (extend σ {B = B}) {Ε = Ε} (extends-reindex there index) ≡ reindex-to-rebase (extends-reindex there) (extends σ index) -- Δ ‚ B ‚‚ Ε ⊢ A
insert-substitute-index {Ε = []} index = refl
insert-substitute-index {Ε = Ε ‚ C} here = refl
insert-substitute-index {Ε = Ε ‚ C} {σ = σ} (there index) = trans (cong shift (insert-substitute-index index)) (insert-twice {Ε = []} (extends σ index))

insert-substitute : {Γ Δ Ε : Context}
    → {A B : Type}
    → {σ : {A : Type} → Γ ∋ A → Δ ⊢ A}
    → (term : Γ ‚‚ Ε ⊢ A)
    → substitute (extends (extend σ {B = B}) {Ε = Ε}) (reindex-to-rebase (extends-reindex there) term) ≡ reindex-to-rebase (extends-reindex there) (substitute (extends σ) term) -- Δ ‚ B ‚‚ Ε ⊢ A
insert-substitute (lookup index) = insert-substitute-index index
insert-substitute {Ε = Ε} {A = A₁ →̇ A₂} {B} {σ} (λ̇ term) = cong λ̇_ (insert-substitute {Ε = Ε ‚ A₁} term)
insert-substitute (term₁ · term₂) = cong₂ _·_ (insert-substitute term₁) (insert-substitute term₂)
insert-substitute żero = refl
insert-substitute (ṡuc term) = cong ṡuc_ (insert-substitute term)
insert-substitute {Ε = Ε} {A = A} (caseℕ̇ term₁ term₂ term₃) = cong₃ caseℕ̇ (insert-substitute term₁) (insert-substitute term₂) (insert-substitute {Ε = Ε ‚ ℕ̇} term₃)
insert-substitute {Ε = Ε} {A = A} (μ̇ term) = cong μ̇_ (insert-substitute {Ε = Ε ‚ A} term)

shift-substitute : {Γ Δ : Context}
    → {A B : Type}
    → {σ : {A : Type} → Γ ∋ A → Δ ⊢ A}
    → (term : Γ ⊢ A)
    → substitute (extend σ {B = B}) (shift term) ≡ shift (substitute σ term) -- Δ ‚ B ⊢ A
shift-substitute = insert-substitute {Ε = []}

extend-substitute-compose : {Γ Δ Ε : Context}
    → {σ₁ : {A : Type} → Γ ∋ A → Δ ⊢ A}
    → {σ₂ : {A : Type} → Δ ∋ A → Ε ⊢ A}
    → {A B : Type}
    → (index : Γ ‚ A ∋ B)
    → ((substitute (extend σ₂)) ∘ extend σ₁) index ≡ extend ((substitute σ₂) ∘ σ₁) index
extend-substitute-compose here = refl
extend-substitute-compose {σ₁ = σ₁} {σ₂ = σ₂} (there index) = shift-substitute (σ₁ index)

substitute-substitute-compose : {Γ Δ Ε : Context}
    → {σ₁ : {A : Type} → Γ ∋ A → Δ ⊢ A}
    → {σ₂ : {A : Type} → Δ ∋ A → Ε ⊢ A}
    → {A : Type}
    → (term : Γ ⊢ A)
    → substitute σ₂ (substitute σ₁ term) ≡ substitute ((substitute σ₂) ∘ σ₁) term
substitute-substitute-compose (lookup index) = refl
substitute-substitute-compose (λ̇ term) = cong λ̇_ (trans (substitute-substitute-compose term) (cong-substitute extend-substitute-compose term))
substitute-substitute-compose (term₁ · term₂) = cong₂ _·_ (substitute-substitute-compose term₁) (substitute-substitute-compose term₂)
substitute-substitute-compose żero = refl
substitute-substitute-compose (ṡuc term) = cong ṡuc_ (substitute-substitute-compose term)
substitute-substitute-compose (caseℕ̇ term₁ term₂ term₃) = cong₃ caseℕ̇ (substitute-substitute-compose term₁) (substitute-substitute-compose term₂) (trans (substitute-substitute-compose term₃) (cong-substitute extend-substitute-compose term₃))
substitute-substitute-compose (μ̇ term) = cong μ̇_ (trans (substitute-substitute-compose term) (cong-substitute extend-substitute-compose term))

-- lemma 3: equalities regarding σ₁ and σ₂

extend-σ₁-there : {Γ : Context} → {A B C : Type}
    → (term : Γ ⊢ A)
    → (index : Γ ‚ B ∋ C)
    → extend (σ₁ term ∘ there) index ≡ (σ₁ (shift term) ∘ there) index
extend-σ₁-there term here = refl
extend-σ₁-there term (there index) = refl

substitute-σ₁-there : {Γ : Context} → {A B : Type}
    → (term₁ : Γ ⊢ A)
    → (term₂ : Γ ⊢ B)
    → substitute (σ₁ term₂ ∘ there) term₁ ≡ term₁
substitute-σ₁-there (lookup index) term₂ = refl
substitute-σ₁-there {Γ} {A₁ →̇ A₂} {B} (λ̇ term₁) term₂ = cong λ̇_ (trans (cong-substitute (extend-σ₁-there term₂) term₁) (substitute-σ₁-there {Γ ‚ A₁} term₁ (shift term₂)))
substitute-σ₁-there (term₁₁ · term₁₂) term₂ = cong₂ _·_ (substitute-σ₁-there term₁₁ term₂) (substitute-σ₁-there term₁₂ term₂)
substitute-σ₁-there żero term₂ = refl
substitute-σ₁-there (ṡuc term₁) term₂ = cong ṡuc_ (substitute-σ₁-there term₁ term₂)
substitute-σ₁-there {Γ} (caseℕ̇ term₁₁ term₁₂ term₁₃) term₂ = cong₃ caseℕ̇ (substitute-σ₁-there term₁₁ term₂) (substitute-σ₁-there term₁₂ term₂) (trans (cong-substitute (extend-σ₁-there term₂) term₁₃) (substitute-σ₁-there {Γ ‚ ℕ̇} term₁₃ (shift term₂)))
substitute-σ₁-there {Γ} {A} {B} (μ̇ term₁) term₂ = cong μ̇_ (trans (cong-substitute (extend-σ₁-there term₂) term₁) (substitute-σ₁-there {Γ ‚ A} term₁ (shift term₂)))

extend-σ₂ : {Γ : Context} → {A B C D : Type}
    → (term₁ : Γ ⊢ A)
    → (term₂ : Γ ⊢ B)
    → (index : Γ ‚ A ‚ B ‚ C ∋ D)
    → (substitute (extend (σ₁ term₁)) ∘ extend (σ₁ (shift term₂))) index ≡ extend (σ₂ term₁ term₂) index
extend-σ₂ term₁ term₂ here = refl
extend-σ₂ term₁ term₂ (there here) =
    trans
        ((extend-substitute-compose {σ₁ = σ₁ (shift term₂)} {σ₂ = σ₁ term₁} (there here)))
        (cong shift (trans
            (substitute-compose term₂)
            (substitute-σ₁-there term₂ term₁)))
extend-σ₂ term₁ term₂ (there (there here)) =
    trans
        ((extend-substitute-compose {σ₁ = σ₁ (shift term₂)} {σ₂ = σ₁ term₁} (there (there here))))
        (cong shift refl)
extend-σ₂ term₁ term₂ (there (there (there index))) = refl

double-substitute : {Γ : Context} → {A B C : Type}
    → (term₁ : Γ ‚ A ‚ B ⊢ C)
    → (term₂ : Γ ⊢ A)
    → (term₃ : Γ ⊢ B)
    → term₁ [ term₂ ][ term₃ ] ≡ term₁ [ shift term₃ ] [ term₂ ]
double-substitute (lookup here) term₂ term₃ = sym (substitute-shift term₃ term₂)
double-substitute (lookup (there here)) term₂ term₃ = refl
double-substitute (lookup (there (there index₁))) term₂ term₃ = refl
double-substitute (λ̇ term₁) term₂ term₃ = cong λ̇_ (sym (trans (substitute-substitute-compose term₁) (cong-substitute (extend-σ₂ term₂ term₃) term₁)))
double-substitute (term₁₁ · term₁₂) term₂ term₃ = cong₂ _·_ (double-substitute term₁₁ term₂ term₃) (double-substitute term₁₂ term₂ term₃)
double-substitute żero term₂ term₃ = refl
double-substitute (ṡuc term₁) term₂ term₃ = cong ṡuc_ (double-substitute term₁ term₂ term₃)
double-substitute (caseℕ̇ term₁₁ term₁₂ term₁₃) term₂ term₃ = cong₃ caseℕ̇ (double-substitute term₁₁ term₂ term₃) (double-substitute term₁₂ term₂ term₃) (sym (trans (substitute-substitute-compose term₁₃) (cong-substitute (extend-σ₂ term₂ term₃) term₁₃)))
double-substitute (μ̇ term₁) term₂ term₃ = cong μ̇_ (sym (trans (substitute-substitute-compose term₁) (cong-substitute (extend-σ₂ term₂ term₃) term₁)))
