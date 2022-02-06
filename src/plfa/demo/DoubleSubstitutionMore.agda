{-# OPTIONS --without-K #-}

module plfa.demo.DoubleSubstitutionMore where

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

open import plfa.part1.Equality using (cong₃)
open import plfa.part2.More

-- useful congruences

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
cong-substitute p (l̇et term₁ term₂) = cong₂ l̇et (cong-substitute p term₁) (cong-substitute (cong-extend p) term₂)
cong-substitute p (prim n) = refl
cong-substitute p ẑero = refl
cong-substitute p (ŝuc term) = cong ŝuc_ (cong-substitute p term)
cong-substitute p (term₁ +̂ term₂) = cong₂ _+̂_ (cong-substitute p term₁) (cong-substitute p term₂)
cong-substitute p (term₁ *̂ term₂) = cong₂ _*̂_ (cong-substitute p term₁) (cong-substitute p term₂)
cong-substitute p (case𝟘̇ term) = cong case𝟘̇ (cong-substitute p term)
cong-substitute p ṫt = refl
cong-substitute p (case𝟙̇ term₁ term₂) = cong₂ case𝟙̇ (cong-substitute p term₁) (cong-substitute p term₂)
cong-substitute p (i̇nj₁ term) = cong i̇nj₁ (cong-substitute p term)
cong-substitute p (i̇nj₂ term) = cong i̇nj₂ (cong-substitute p term)
cong-substitute p (case+̇ term₁ term₂ term₃) = cong₃ case+̇ (cong-substitute p term₁) (cong-substitute (cong-extend p) term₂) (cong-substitute (cong-extend p) term₃)
cong-substitute p (term₁ ,̇ term₂) = cong₂ _,̇_ (cong-substitute p term₁) (cong-substitute p term₂)
cong-substitute p (ṗroj₁ term) = cong ṗroj₁ (cong-substitute p term)
cong-substitute p (ṗroj₂ term) = cong ṗroj₂ (cong-substitute p term)
cong-substitute p (case×̇ term₁ term₂) = cong₂ case×̇ (cong-substitute p term₁) (cong-substitute (cong-extend (cong-extend p)) term₂)
cong-substitute p [̇] = refl
cong-substitute p (term₁ ∷̇ term₂) = cong₂ _∷̇_ (cong-substitute p term₁) (cong-substitute p term₂)
cong-substitute p (caseL̇ist term₁ term₂ term₃) = cong₃ caseL̇ist (cong-substitute p term₁) (cong-substitute p term₂) (cong-substitute (cong-extend (cong-extend p)) term₃)

-- repeated extend-reindex (extends-reindex) and repeated extend (extends)

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

-- lemma 1: substitute-shift

extend-compose : {Γ Δ Ε : Context}
    → {ρ : {A : Type} → Γ ∋ A → Δ ∋ A}
    → {σ : {A : Type} → Δ ∋ A → Ε ⊢ A}
    → {A B : Type}
    → (index : Γ ‚ B ∋ A)
    → ((extend σ) ∘ (extend-reindex ρ)) index ≡ extend (σ ∘ ρ) index
extend-compose here = refl
extend-compose (there index) = refl

extends-compose : {Γ Δ Ε : Context}
    → {ρ : {A : Type} → Γ ∋ A → Δ ∋ A}
    → {σ : {A : Type} → Δ ∋ A → Ε ⊢ A}
    → {A : Type} → {Ζ : Context}
    → (index : Γ ‚‚ Ζ ∋ A)
    → ((extends σ) ∘ (extends-reindex ρ)) index ≡ extends (σ ∘ ρ) index
extends-compose {Ζ = []} index = refl
extends-compose {Ζ = Ζ ‚ B} here = refl
extends-compose {ρ = ρ} {σ = σ} {Ζ = Ζ ‚ B} (there index) = trans (extend-compose {ρ = extends-reindex ρ} {σ = extends σ} (there index)) (cong shift (extends-compose {ρ = ρ} {σ = σ} index))

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
substitute-compose (l̇et term₁ term₂) = cong₂ l̇et (substitute-compose term₁) (trans (substitute-compose term₂) (cong-substitute extend-compose term₂))
substitute-compose (prim n) = refl
substitute-compose ẑero = refl
substitute-compose (ŝuc term) = cong ŝuc_ (substitute-compose term)
substitute-compose (term₁ +̂ term₂) = cong₂ _+̂_ (substitute-compose term₁) (substitute-compose term₂)
substitute-compose (term₁ *̂ term₂) = cong₂ _*̂_ (substitute-compose term₁) (substitute-compose term₂)
substitute-compose (case𝟘̇ term) = cong case𝟘̇ (substitute-compose term)
substitute-compose ṫt = refl
substitute-compose (case𝟙̇ term₁ term₂) = cong₂ case𝟙̇ (substitute-compose term₁) (substitute-compose term₂)
substitute-compose (i̇nj₁ term) = cong i̇nj₁ (substitute-compose term)
substitute-compose (i̇nj₂ term) = cong i̇nj₂ (substitute-compose term)
substitute-compose (case+̇ term₁ term₂ term₃) = cong₃ case+̇ (substitute-compose term₁) (trans (substitute-compose term₂) (cong-substitute extend-compose term₂)) (trans (substitute-compose term₃) (cong-substitute extend-compose term₃))
substitute-compose (term₁ ,̇ term₂) = cong₂ _,̇_ (substitute-compose term₁) (substitute-compose term₂)
substitute-compose (ṗroj₁ term) = cong ṗroj₁ (substitute-compose term)
substitute-compose (ṗroj₂ term) = cong ṗroj₂ (substitute-compose term)
substitute-compose (case×̇ {A = A} {B = B} term₁ term₂) = cong₂ case×̇ (substitute-compose term₁) (trans (substitute-compose term₂) (cong-substitute (extends-compose {Ζ = [] ‚ A ‚ B}) term₂))
substitute-compose [̇] = refl
substitute-compose (term₁ ∷̇ term₂) = cong₂ _∷̇_ (substitute-compose term₁) (substitute-compose term₂)
substitute-compose (caseL̇ist {A = A} term₁ term₂ term₃) = cong₃ caseL̇ist (substitute-compose term₁) (substitute-compose term₂) (trans (substitute-compose term₃) (cong-substitute (extends-compose {Ζ = [] ‚ A ‚ L̇ist A}) term₃))

extend-lookup : {Γ : Context} → {A B : Type}
    → (index : Γ ‚ B ∋ A)
    → extend lookup index ≡ lookup index
extend-lookup here = refl
extend-lookup (there index) = refl

extends-lookup : {Γ Δ : Context} → {A : Type}
    → (index : Γ ‚‚ Δ ∋ A)
    → extends (lookup {Γ = Γ}) index ≡ lookup index
extends-lookup {Δ = []} index = refl
extends-lookup {Δ = Δ ‚ B} here = refl
extends-lookup {Δ = Δ ‚ B} (there index) = cong shift (extends-lookup {Δ = Δ} index)

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
substitute-lookup (l̇et term₁ term₂) = cong₂ l̇et (substitute-lookup term₁) (trans (cong-substitute extend-lookup term₂) (substitute-lookup term₂))
substitute-lookup (prim n) = refl
substitute-lookup ẑero = refl
substitute-lookup (ŝuc term) = cong ŝuc_ (substitute-lookup term)
substitute-lookup (term₁ +̂ term₂) = cong₂ _+̂_ (substitute-lookup term₁) (substitute-lookup term₂)
substitute-lookup (term₁ *̂ term₂) = cong₂ _*̂_ (substitute-lookup term₁) (substitute-lookup term₂)
substitute-lookup (case𝟘̇ term) = cong case𝟘̇ (substitute-lookup term)
substitute-lookup ṫt = refl
substitute-lookup (case𝟙̇ term₁ term₂) = cong₂ case𝟙̇ (substitute-lookup term₁) (substitute-lookup term₂)
substitute-lookup (i̇nj₁ term) = cong i̇nj₁ (substitute-lookup term)
substitute-lookup (i̇nj₂ term) = cong i̇nj₂ (substitute-lookup term)
substitute-lookup (case+̇ term₁ term₂ term₃) = cong₃ case+̇ (substitute-lookup term₁) (trans (cong-substitute extend-lookup term₂) (substitute-lookup term₂)) (trans (cong-substitute extend-lookup term₃) (substitute-lookup term₃))
substitute-lookup (term₁ ,̇ term₂) = cong₂ _,̇_ (substitute-lookup term₁) (substitute-lookup term₂)
substitute-lookup (ṗroj₁ term) = cong ṗroj₁ (substitute-lookup term)
substitute-lookup (ṗroj₂ term) = cong ṗroj₂ (substitute-lookup term)
substitute-lookup (case×̇ {A = A} {B = B} term₁ term₂) = cong₂ case×̇ (substitute-lookup term₁) (trans (cong-substitute (extends-lookup {Δ = [] ‚ A ‚ B}) term₂) (substitute-lookup term₂))
substitute-lookup [̇] = refl
substitute-lookup (term₁ ∷̇ term₂) = cong₂ _∷̇_ (substitute-lookup term₁) (substitute-lookup term₂)
substitute-lookup (caseL̇ist {A = A} term₁ term₂ term₃) = cong₃ caseL̇ist (substitute-lookup term₁) (substitute-lookup term₂) (trans (cong-substitute (extends-lookup {Δ = [] ‚ A ‚ L̇ist A}) term₃) (substitute-lookup term₃))

substitute-shift : {Γ : Context} → {A B : Type}
    → (term₁ : Γ ⊢ A)
    → (term₂ : Γ ⊢ B)
    → (shift term₁) [ term₂ ] ≡ term₁
substitute-shift term₁ term₂ = trans (substitute-compose term₁) (substitute-lookup term₁)

-- lemma 2: substitute-substitute-compose

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
insert-twice {Ε = Ε} (caseℕ̇ term₁ term₂ term₃) = cong₃ caseℕ̇ (insert-twice term₁) (insert-twice term₂) (insert-twice {Ε = Ε ‚ ℕ̇} term₃)
insert-twice {Ε = Ε} {A = A} (μ̇ term) = cong μ̇_ (insert-twice {Ε = Ε ‚ A} term)
insert-twice {Ε = Ε} (l̇et {A = A} term₁ term₂) = cong₂ l̇et (insert-twice term₁) (insert-twice {Ε = Ε ‚ A} term₂)
insert-twice (prim n) = refl
insert-twice ẑero = refl
insert-twice (ŝuc term) = cong ŝuc_ (insert-twice term)
insert-twice (term₁ +̂ term₂) = cong₂ _+̂_ (insert-twice term₁) (insert-twice term₂)
insert-twice (term₁ *̂ term₂) = cong₂ _*̂_ (insert-twice term₁) (insert-twice term₂)
insert-twice (case𝟘̇ term) = cong case𝟘̇ (insert-twice term)
insert-twice ṫt = refl
insert-twice (case𝟙̇ term₁ term₂) = cong₂ case𝟙̇ (insert-twice term₁) (insert-twice term₂)
insert-twice (i̇nj₁ term) = cong i̇nj₁ (insert-twice term)
insert-twice (i̇nj₂ term) = cong i̇nj₂ (insert-twice term)
insert-twice {Ε = Ε} (case+̇ {A = A} {B = B} term₁ term₂ term₃) = cong₃ case+̇ (insert-twice term₁) (insert-twice {Ε = Ε ‚ A} term₂) (insert-twice {Ε = Ε ‚ B} term₃)
insert-twice (term₁ ,̇ term₂) = cong₂ _,̇_ (insert-twice term₁) (insert-twice term₂)
insert-twice (ṗroj₁ term) = cong ṗroj₁ (insert-twice term)
insert-twice (ṗroj₂ term) = cong ṗroj₂ (insert-twice term)
insert-twice {Ε = Ε} (case×̇ {A = A} {B = B} term₁ term₂) = cong₂ case×̇ (insert-twice term₁) (insert-twice {Ε = Ε ‚ A ‚ B} term₂)
insert-twice [̇] = refl
insert-twice (term₁ ∷̇ term₂) = cong₂ _∷̇_ (insert-twice term₁) (insert-twice term₂)
insert-twice {Ε = Ε} (caseL̇ist {A = A} term₁ term₂ term₃) = cong₃ caseL̇ist (insert-twice term₁) (insert-twice term₂) (insert-twice {Ε = Ε ‚ A ‚ L̇ist A} term₃)

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
insert-substitute {Ε = Ε} {A = A₁ →̇ A₂} (λ̇ term) = cong λ̇_ (insert-substitute {Ε = Ε ‚ A₁} term)
insert-substitute (term₁ · term₂) = cong₂ _·_ (insert-substitute term₁) (insert-substitute term₂)
insert-substitute żero = refl
insert-substitute (ṡuc term) = cong ṡuc_ (insert-substitute term)
insert-substitute {Ε = Ε} (caseℕ̇ term₁ term₂ term₃) = cong₃ caseℕ̇ (insert-substitute term₁) (insert-substitute term₂) (insert-substitute {Ε = Ε ‚ ℕ̇} term₃)
insert-substitute {Ε = Ε} {A = A} (μ̇ term) = cong μ̇_ (insert-substitute {Ε = Ε ‚ A} term)
insert-substitute {Ε = Ε} (l̇et {A = A} term₁ term₂) = cong₂ l̇et (insert-substitute term₁) (insert-substitute {Ε = Ε ‚ A} term₂)
insert-substitute (prim n) = refl
insert-substitute ẑero = refl
insert-substitute (ŝuc term) = cong ŝuc_ (insert-substitute term)
insert-substitute (term₁ +̂ term₂) = cong₂ _+̂_ (insert-substitute term₁) (insert-substitute term₂)
insert-substitute (term₁ *̂ term₂) = cong₂ _*̂_ (insert-substitute term₁) (insert-substitute term₂)
insert-substitute (case𝟘̇ term) = cong case𝟘̇ (insert-substitute term)
insert-substitute ṫt = refl
insert-substitute (case𝟙̇ term₁ term₂) = cong₂ case𝟙̇ (insert-substitute term₁) (insert-substitute term₂)
insert-substitute (i̇nj₁ term) = cong i̇nj₁ (insert-substitute term)
insert-substitute (i̇nj₂ term) = cong i̇nj₂ (insert-substitute term)
insert-substitute {Ε = Ε} (case+̇ {A = A} {B = B} term₁ term₂ term₃) = cong₃ case+̇ (insert-substitute term₁) (insert-substitute {Ε = Ε ‚ A} term₂) (insert-substitute {Ε = Ε ‚ B} term₃)
insert-substitute (term₁ ,̇ term₂) = cong₂ _,̇_ (insert-substitute term₁) (insert-substitute term₂)
insert-substitute (ṗroj₁ term) = cong ṗroj₁ (insert-substitute term)
insert-substitute (ṗroj₂ term) = cong ṗroj₂ (insert-substitute term)
insert-substitute {Ε = Ε} (case×̇ {A = A} {B = B} term₁ term₂) = cong₂ case×̇ (insert-substitute term₁) (insert-substitute {Ε = Ε ‚ A ‚ B} term₂)
insert-substitute [̇] = refl
insert-substitute (term₁ ∷̇ term₂) = cong₂ _∷̇_ (insert-substitute term₁) (insert-substitute term₂)
insert-substitute {Ε = Ε} (caseL̇ist {A = A} term₁ term₂ term₃) = cong₃ caseL̇ist (insert-substitute term₁) (insert-substitute term₂) (insert-substitute {Ε = Ε ‚ A ‚ L̇ist A} term₃)

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
    → (index : Γ ‚ B ∋ A)
    → ((substitute (extend σ₂)) ∘ extend σ₁) index ≡ extend ((substitute σ₂) ∘ σ₁) index
extend-substitute-compose here = refl
extend-substitute-compose {σ₁ = σ₁} (there index) = shift-substitute (σ₁ index)

extends-substitute-compose : {Γ Δ Ε : Context}
    → {σ₁ : {A : Type} → Γ ∋ A → Δ ⊢ A}
    → {σ₂ : {A : Type} → Δ ∋ A → Ε ⊢ A}
    → {A : Type} → {Ζ : Context}
    → (index : Γ ‚‚ Ζ ∋ A)
    → ((substitute (extends σ₂)) ∘ extends σ₁) index ≡ extends ((substitute σ₂) ∘ σ₁) index
extends-substitute-compose {Ζ = []} index = refl
extends-substitute-compose {Ζ = Ζ ‚ B} here = refl
extends-substitute-compose {σ₁ = σ₁} {Ζ = Ζ ‚ B} (there index) = trans (extend-substitute-compose {σ₁ = extends σ₁} (there index)) (cong shift (extends-substitute-compose {σ₁ = σ₁} index))

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
substitute-substitute-compose (l̇et term₁ term₂) = cong₂ l̇et (substitute-substitute-compose term₁) (trans (substitute-substitute-compose term₂) (cong-substitute extend-substitute-compose term₂))
substitute-substitute-compose (prim n) = refl
substitute-substitute-compose ẑero = refl
substitute-substitute-compose (ŝuc term) = cong ŝuc_ (substitute-substitute-compose term)
substitute-substitute-compose (term₁ +̂ term₂) = cong₂ _+̂_ (substitute-substitute-compose term₁) (substitute-substitute-compose term₂)
substitute-substitute-compose (term₁ *̂ term₂) = cong₂ _*̂_ (substitute-substitute-compose term₁) (substitute-substitute-compose term₂)
substitute-substitute-compose (case𝟘̇ term) = cong case𝟘̇ (substitute-substitute-compose term)
substitute-substitute-compose ṫt = refl
substitute-substitute-compose (case𝟙̇ term₁ term₂) = cong₂ case𝟙̇ (substitute-substitute-compose term₁) (substitute-substitute-compose term₂)
substitute-substitute-compose (i̇nj₁ term) = cong i̇nj₁ (substitute-substitute-compose term)
substitute-substitute-compose (i̇nj₂ term) = cong i̇nj₂ (substitute-substitute-compose term)
substitute-substitute-compose (case+̇ term₁ term₂ term₃) = cong₃ case+̇ (substitute-substitute-compose term₁) (trans (substitute-substitute-compose term₂) (cong-substitute extend-substitute-compose term₂)) (trans (substitute-substitute-compose term₃) (cong-substitute extend-substitute-compose term₃))
substitute-substitute-compose (term₁ ,̇ term₂) = cong₂ _,̇_ (substitute-substitute-compose term₁) (substitute-substitute-compose term₂)
substitute-substitute-compose (ṗroj₁ term) = cong ṗroj₁ (substitute-substitute-compose term)
substitute-substitute-compose (ṗroj₂ term) = cong ṗroj₂ (substitute-substitute-compose term)
substitute-substitute-compose (case×̇ {A = A} {B = B} term₁ term₂) = cong₂ case×̇ (substitute-substitute-compose term₁) (trans (substitute-substitute-compose term₂) (cong-substitute (extends-substitute-compose {Ζ = [] ‚ A ‚ B}) term₂))
substitute-substitute-compose [̇] = refl
substitute-substitute-compose (term₁ ∷̇ term₂) = cong₂ _∷̇_ (substitute-substitute-compose term₁) (substitute-substitute-compose term₂)
substitute-substitute-compose (caseL̇ist {A = A} term₁ term₂ term₃) = cong₃ caseL̇ist (substitute-substitute-compose term₁) (substitute-substitute-compose term₂) (trans (substitute-substitute-compose term₃) (cong-substitute (extends-substitute-compose {Ζ = [] ‚ A ‚ L̇ist A}) term₃))

-- lemma 3: equalities regarding σ₁ and σ₂

extend-σ₂ : {Γ : Context} → {A B C D : Type}
    → (term₁ : Γ ⊢ A)
    → (term₂ : Γ ⊢ B)
    → (index : Γ ‚ A ‚ B ‚ D ∋ C)
    → (substitute (extend (σ₁ term₁)) ∘ extend (σ₁ (shift term₂))) index ≡ extend (σ₂ term₁ term₂) index
extend-σ₂ term₁ term₂ here = refl
extend-σ₂ term₁ term₂ (there here) =
    trans
        ((extend-substitute-compose {σ₁ = σ₁ (shift term₂)} {σ₂ = σ₁ term₁} (there here)))
        (cong shift (substitute-shift term₂ term₁))
extend-σ₂ term₁ term₂ (there (there here)) =
    trans
        ((extend-substitute-compose {σ₁ = σ₁ (shift term₂)} {σ₂ = σ₁ term₁} (there (there here))))
        (cong shift refl)
extend-σ₂ term₁ term₂ (there (there (there index))) = refl

extends-σ₂ : {Γ Δ : Context} → {A B C : Type}
    → (term₁ : Γ ⊢ A)
    → (term₂ : Γ ⊢ B)
    → (index : Γ ‚ A ‚ B ‚‚ Δ ∋ C)
    → (substitute (extends (σ₁ term₁)) ∘ extends (σ₁ (shift term₂))) index ≡ extends (σ₂ term₁ term₂) index
extends-σ₂ {Δ = []} term₁ term₂ here = substitute-shift term₂ term₁
extends-σ₂ {Δ = []} term₁ term₂ (there here) = refl
extends-σ₂ {Δ = []} term₁ term₂ (there (there index)) = refl
extends-σ₂ {Δ = Δ ‚ D} term₁ term₂ here = refl
extends-σ₂ {Δ = Δ ‚ D} term₁ term₂ (there index) = trans (extend-substitute-compose {σ₁ = extends (σ₁ (shift term₂))} (there index)) (cong shift (extends-σ₂ term₁ term₂ index))

-- double substitution

double-substitute : {Γ : Context} → {A B C : Type}
    → (term₁ : Γ ‚ A ‚ B ⊢ C)
    → (term₂ : Γ ⊢ A)
    → (term₃ : Γ ⊢ B)
    → term₁ [ shift term₃ ] [ term₂ ] ≡ term₁ [ term₂ ][ term₃ ]
double-substitute (lookup index) term₂ term₃ = extends-σ₂ term₂ term₃ index
double-substitute (λ̇ term₁) term₂ term₃ = cong λ̇_ (trans (substitute-substitute-compose term₁) (cong-substitute (extend-σ₂ term₂ term₃) term₁))
double-substitute (term₁₁ · term₁₂) term₂ term₃ = cong₂ _·_ (double-substitute term₁₁ term₂ term₃) (double-substitute term₁₂ term₂ term₃)
double-substitute żero term₂ term₃ = refl
double-substitute (ṡuc term₁) term₂ term₃ = cong ṡuc_ (double-substitute term₁ term₂ term₃)
double-substitute (caseℕ̇ term₁₁ term₁₂ term₁₃) term₂ term₃ = cong₃ caseℕ̇ (double-substitute term₁₁ term₂ term₃) (double-substitute term₁₂ term₂ term₃) (trans (substitute-substitute-compose term₁₃) (cong-substitute (extend-σ₂ term₂ term₃) term₁₃))
double-substitute (μ̇ term₁) term₂ term₃ = cong μ̇_ (trans (substitute-substitute-compose term₁) (cong-substitute (extend-σ₂ term₂ term₃) term₁))
double-substitute (l̇et term₁₁ term₁₂) term₂ term₃ = cong₂ l̇et (double-substitute term₁₁ term₂ term₃) (trans (substitute-substitute-compose term₁₂) (cong-substitute (extend-σ₂ term₂ term₃) term₁₂))
double-substitute (prim n) term₂ term₃ = refl
double-substitute ẑero term₂ term₃ = refl
double-substitute (ŝuc term₁) term₂ term₃ = cong ŝuc_ (double-substitute term₁ term₂ term₃)
double-substitute (term₁₁ +̂ term₁₂) term₂ term₃ = cong₂ _+̂_ (double-substitute term₁₁ term₂ term₃) (double-substitute term₁₂ term₂ term₃)
double-substitute (term₁₁ *̂ term₁₂) term₂ term₃ = cong₂ _*̂_ (double-substitute term₁₁ term₂ term₃) (double-substitute term₁₂ term₂ term₃)
double-substitute (case𝟘̇ term₁) term₂ term₃ = cong case𝟘̇ (double-substitute term₁ term₂ term₃)
double-substitute ṫt term₂ term₃ = refl
double-substitute (case𝟙̇ term₁₁ term₁₂) term₂ term₃ = cong₂ case𝟙̇ (double-substitute term₁₁ term₂ term₃) (double-substitute term₁₂ term₂ term₃)
double-substitute (i̇nj₁ term₁) term₂ term₃ = cong i̇nj₁ (double-substitute term₁ term₂ term₃)
double-substitute (i̇nj₂ term₁) term₂ term₃ = cong i̇nj₂ (double-substitute term₁ term₂ term₃)
double-substitute (case+̇ term₁₁ term₁₂ term₁₃) term₂ term₃ = cong₃ case+̇ (double-substitute term₁₁ term₂ term₃) (trans (substitute-substitute-compose term₁₂) (cong-substitute (extend-σ₂ term₂ term₃) term₁₂)) (trans (substitute-substitute-compose term₁₃) (cong-substitute (extend-σ₂ term₂ term₃) term₁₃))
double-substitute (term₁₁ ,̇ term₁₂) term₂ term₃ = cong₂ _,̇_ (double-substitute term₁₁ term₂ term₃) (double-substitute term₁₂ term₂ term₃)
double-substitute (ṗroj₁ term₁) term₂ term₃ = cong ṗroj₁ (double-substitute term₁ term₂ term₃)
double-substitute (ṗroj₂ term₁) term₂ term₃ = cong ṗroj₂ (double-substitute term₁ term₂ term₃)
double-substitute (case×̇ term₁₁ term₁₂) term₂ term₃ = cong₂ case×̇ (double-substitute term₁₁ term₂ term₃) (trans (substitute-substitute-compose term₁₂) (cong-substitute (extends-σ₂ term₂ term₃) term₁₂))
double-substitute [̇] term₂ term₃ = refl
double-substitute (term₁₁ ∷̇ term₁₂) term₂ term₃ = cong₂ _∷̇_ (double-substitute term₁₁ term₂ term₃) (double-substitute term₁₂ term₂ term₃)
double-substitute (caseL̇ist term₁₁ term₁₂ term₁₃) term₂ term₃ = cong₃ caseL̇ist (double-substitute term₁₁ term₂ term₃) (double-substitute term₁₂ term₂ term₃) (trans (substitute-substitute-compose term₁₃) (cong-substitute (extends-σ₂ term₂ term₃) term₁₃))
