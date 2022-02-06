{-# OPTIONS --without-K #-}

module plfa.part2.DeBruijn where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _<_; _<?_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; flip)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

infixr 7 _→̇_

data Type : Set where
    ℕ̇ : Type
    _→̇_ : Type → Type → Type

Context : Set
Context = List Type -- a context is just a list of types, but written right-to-left

-- '‚': U+201A
infixl 5 _‚_
pattern _‚_ Γ A = A ∷ Γ

-- _‚_ : Context → Type → Context
-- _‚_ = flip _∷_

infixl 4.5 _‚‚_
_‚‚_ : Context → Context → Context
_‚‚_ = flip _++_

infix 4 _∋_
-- pattern _∋_ Γ A = A ∈ Γ

-- _∋_ : Context → Type → Set
-- _∋_ = flip _∈_

data _∋_ : Context → Type → Set where
    here : {Γ : Context} → {A : Type}
        → Γ ‚ A ∋ A
    there : {Γ : Context} → {A B : Type}
        → Γ ∋ A
        → Γ ‚ B ∋ A

_ : Context
_ = [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ∋ ℕ̇
_ = here

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ∋ ℕ̇ →̇ ℕ̇
_ = there here

infix 4 _⊢_
infix 5 λ̇_
infix 5 μ̇_
infixl 7 _·_
infix 8 ṡuc_

-- Intrinsic typing (this chapter) is Church style
-- Extrinsic typing (previous chapter) is Curry style

data _⊢_ : Context → Type → Set where
    lookup : {Γ : Context} → {A : Type}
        → Γ ∋ A
        → Γ ⊢ A
    λ̇_ : {Γ : Context} → {A B : Type}
        → Γ ‚ A ⊢ B
        → Γ ⊢ A →̇ B
    _·_ : {Γ : Context} → {A B : Type}
        → Γ ⊢ A →̇ B
        → Γ ⊢ A
        → Γ ⊢ B
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
    μ̇_ : {Γ : Context} → {A : Type}
        → Γ ‚ A ⊢ A
        → Γ ⊢ A

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇
_ = lookup here

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
_ = lookup (there here)

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇
_ = lookup (there here) · lookup here

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇
_ = lookup (there here) · (lookup (there here) · lookup here)

_ : [] ‚ ℕ̇ →̇ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
_ = λ̇ (lookup (there here) · (lookup (there here) · lookup here))

_ : [] ⊢ (ℕ̇ →̇ ℕ̇) →̇ ℕ̇ →̇ ℕ̇
_ = λ̇ λ̇ (lookup (there here) · (lookup (there here) · lookup here))

-- Abbreviating de Bruijn indices

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

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇
_ = # 0

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
_ = # 1

-- _ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
-- _ = # 2 -- this will not work

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

-- Renaming (Reindexing to Rebasing)

extend-reindex : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ∋ A) -- ρ (reindex) maps each variable (index) of type A in context Γ to a variable of type A in context Δ, i.e., Γ is a subset of Δ (Γ ⊆ Δ)
    → ({A B : Type} → Γ ‚ B ∋ A → Δ ‚ B ∋ A) -- ρ lifts to a map (reindex) (by shifting 1) from variables of type A in context Γ extended by B to variables of type A in context Δ extended by B
extend-reindex ρ here = here
extend-reindex ρ (there index) = there (ρ index)

-- the same proof but using general list, note we need to write refl for here

-- extend-reindex : {A : Set} → {xs ys : List A}
--     → ({x : A} → x ∈ xs → x ∈ ys)
--     → ({x y : A} → x ∈ y ∷ xs → x ∈ y ∷ ys)
-- extend-reindex ρ (here refl) = here refl
-- extend-reindex ρ (there index) = there (ρ index)

-- "index" (intrinsic) == "lookup" (extrinsic) or loosely variables (Id)
-- "term" (intrinsic) == "typing" (extrinsic)

reindex-to-rebase : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ∋ A) -- ρ (reindex) maps each variable (index) of type A in context Γ to a variable of type A in context Δ
    → ({A : Type} → Γ ⊢ A → Δ ⊢ A) -- ρ lifts to a map (rebase) from terms of type A in context Γ to terms of type A in context Γ
reindex-to-rebase ρ (lookup index) = lookup (ρ index)
reindex-to-rebase ρ (λ̇ term) = λ̇ (reindex-to-rebase (extend-reindex ρ) term)
reindex-to-rebase ρ (term₁ · term₂) = (reindex-to-rebase ρ term₁) · (reindex-to-rebase ρ term₂)
reindex-to-rebase ρ żero = żero
reindex-to-rebase ρ (ṡuc term) = ṡuc (reindex-to-rebase ρ term)
reindex-to-rebase ρ (caseℕ̇ term₁ term₂ term₃) = caseℕ̇ (reindex-to-rebase ρ term₁) (reindex-to-rebase ρ term₂) (reindex-to-rebase (extend-reindex ρ) term₃)
reindex-to-rebase ρ (μ̇ term) = μ̇ (reindex-to-rebase (extend-reindex ρ) term)

term₁ : [] ‚ ℕ̇ →̇ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
term₁ = λ̇ # 1 · (# 1 · # 0) -- ∅ , "f" ⦂ ℕ̇ →̇ ℕ̇ ⊢ λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇) ⦂ ℕ̇ →̇ ℕ̇

term₂ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
term₂ = λ̇ # 2 · (# 2 · # 0)

shift : {Γ : Context} → {A B : Type} → Γ ⊢ A → Γ ‚ B ⊢ A
shift = reindex-to-rebase there

_ : shift term₁ ≡ term₂
_ = refl

-- Simultaneous Substitution (with built-in typing preservation)

extend : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ⊢ A) -- σ (substitution) maps each variable (index) of type A in context Γ to a term of type A in context Δ, i.e., a list of terms Δ ⊢ A for each variable A in Γ
    → ({A B : Type} → Γ ‚ B ∋ A → Δ ‚ B ⊢ A) -- σ lifts to a map (substitution) (by shifting 1) from variables of type A in context Γ extended by B to terms of type A in context Δ extended by B
extend σ here = lookup here
extend σ (there index) = shift (σ index)

substitute : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ⊢ A) -- σ (substitution) maps each variable (index) of type A in context Γ to a term of type A in context Δ
    → ({A : Type} → Γ ⊢ A → Δ ⊢ A) -- σ lifts to a map (rebase) from terms of type A in context Γ to terms of type A in context Δ
substitute σ (lookup index) = σ index
substitute σ (λ̇ term) = λ̇ substitute (extend σ) term
substitute σ (term₁ · term₂) = (substitute σ term₁) · (substitute σ term₂)
substitute σ żero = żero
substitute σ (ṡuc term) = ṡuc substitute σ term
substitute σ (caseℕ̇ term₁ term₂ term₃) = caseℕ̇ (substitute σ term₁) (substitute σ term₂) (substitute (extend σ) term₃)
substitute σ (μ̇ term) = μ̇ substitute (extend σ) term

-- personal note:

-- in literature such as [Cubical Type Theory: a constructive interpretation of the univalence axiom](https://arxiv.org/abs/1611.02108)
-- the substitution is written:
-- Δ ⊢ σ : Γ
-- defined inductively as:
-- base: Δ ⊢ [] : []
-- induction: Δ ⊢ σ, x := t : Γ, x : A if Δ ⊢ σ : Γ and Δ ⊢ t : Aσ (Aσ is for dependent typed languages, here it is just A)
-- e.g.,
-- Δ ⊢ [x := t] : [], x : A
-- Δ ⊢ [x := t, y := s] : [], x : A, y : B
-- we have substitution lemma: Γ ⊢ t : A and Δ ⊢ σ : Γ implies Δ ⊢ tσ : Aσ
-- substitution lemma is exactly the substitute function above

-- Single Substitution

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

-- _[_] : {Γ : Context} → {A B : Type}
--     → Γ ‚ A ⊢ B
--     → Γ ⊢ A
--     → Γ ⊢ B
-- _[_] {Γ} {A} {B} term₁ term₂ = substitute {Γ ‚ A} {Γ}
--     (λ {
--         here → term₂;
--         (there index) → lookup index })
--     term₁

t1 : [] ‚ ℕ̇ →̇ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
t1 = λ̇ # 1 · (# 1 · # 0) -- λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇)

s1 : [] ⊢ ℕ̇ →̇ ℕ̇
s1 = λ̇ ṡuc # 0 -- λ̇ṡuc = λ̇ "n" ⇒ ṡuc "n"

t1[s1] : [] ⊢ ℕ̇ →̇ ℕ̇
t1[s1] = λ̇ (λ̇ ṡuc # 0) · ((λ̇ ṡuc # 0) · # 0) -- λ̇ "x" ⇒ λ̇ṡuc · (λ̇ṡuc · "x"̇)

_ : t1 [ s1 ] ≡ t1[s1]
_ = refl

t2 : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ (ℕ̇ →̇ ℕ̇) →̇ ℕ̇
t2 = λ̇ # 0 · # 1 -- λ̇ "f" ⇒ "f"̇ · "x"̇

s2 : [] ‚ ℕ̇ →̇ ℕ̇ ⊢ ℕ̇
s2 = # 0 · żero -- "f"̇ · żero

t2[s2] : [] ‚ ℕ̇ →̇ ℕ̇ ⊢ (ℕ̇ →̇ ℕ̇) →̇ ℕ̇
t2[s2] = λ̇ # 0 · (# 1 · żero) -- λ̇ "g" ⇒ "g"̇ · ("f"̇ · żero) now we can finally substitute open terms

_ : t2 [ s2 ] ≡ t2[s2]
_ = refl

-- Double Substitution

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

-- _[_][_] : {Γ : Context} → {A B C : Type}
--     → Γ ‚ A ‚ B ⊢ C
--     → Γ ⊢ A
--     → Γ ⊢ B
--     → Γ ⊢ C
-- _[_][_] {Γ} {A} {B} {C} term₁ term₂ term₃ = substitute {Γ ‚ A ‚ B} {Γ}
--     (λ {
--         here → term₃;
--         (there here) → term₂;
--         (there (there index)) → lookup index })
--     term₁

t3 : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇
t3 = # 1 · # 0

s3 : [] ⊢ ℕ̇ →̇ ℕ̇
s3 = λ̇ ṡuc # 0

r3 : [] ⊢ ℕ̇
r3 = żero

t3[s3][r3] : [] ⊢ ℕ̇
t3[s3][r3] = (λ̇ ṡuc # 0) · żero

_ : t3 [ s3 ][ r3 ] ≡ t3[s3][r3]
_ = refl

_ : t3 [ shift r3 ] [ s3 ] ≡ t3[s3][r3]
_ = refl

-- double-substitute : {Γ : Context} → {A B C : Type}
--     → (term₁ : Γ ‚ A ‚ B ⊢ C)
--     → (term₂ : Γ ⊢ A)
--     → (term₃ : Γ ⊢ B)
--     → term₁ [ term₂ ][ term₃ ] ≡ term₁ [ shift term₃ ] [ term₂ ]
-- double-substitute {Γ} {A} {B} {C} term₁ term₂ term₃ = ? -- see DoubleSubstitutionDeBruijn.agda

-- Values (Canonical forms i.e., extrinsic value and typed)

data Value : {Γ : Context} → {A : Type} → Γ ⊢ A → Set where
    value-λ̇ : {Γ : Context} → {A B : Type} → {term : Γ ‚ A ⊢ B}
        → Value (λ̇ term)
    value-żero : {Γ : Context}
        → Value (żero {Γ})
    value-ṡuc : {Γ : Context} → {term : Γ ⊢ ℕ̇}
        → Value term
        → Value (ṡuc term)

value-ȯne : {Γ : Context} → Value {Γ} (ȯne)
value-ȯne = value-ṡuc (value-żero)

value-ṫwo : {Γ : Context} → Value {Γ} (ṫwo)
value-ṫwo = value-ṡuc (value-ȯne)

value-ṫhree : {Γ : Context} → Value {Γ} (ṫhree)
value-ṫhree = value-ṡuc (value-ṫwo)

-- Reduction (with built-in typing preservation)

infix 2 _⟶_

data _⟶_ : {Γ : Context} → {A : Type} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
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
    ξ-·₁ : {Γ : Context} → {A B : Type}
        → {term₁ term₁′ : Γ ⊢ A →̇ B} → {term₂ : Γ ⊢ A}
        → term₁ ⟶ term₁′
        → term₁ · term₂ ⟶ term₁′ · term₂ -- ξ's are compatibility rules
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

-- Reflexive and transitive closure

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
begin reductions = reductions

_ : ṫwoᶜ · λ̇ṡuc · żero {[]} ⟶⋆ ṡuc ṡuc żero
_ = begin
        ṫwoᶜ · λ̇ṡuc · żero
    ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
        (λ̇ λ̇ṡuc · (λ̇ṡuc · # 0)) · żero
    ⟶⟨ β-λ̇ value-żero ⟩
        λ̇ṡuc · (λ̇ṡuc · żero)
    ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
        λ̇ṡuc · (ṡuc żero)
    ⟶⟨ β-λ̇ (value-ṡuc value-żero) ⟩
        ṡuc ṡuc żero
    ∎

_ : ȧdd · ṫwo · ṫwo ⟶⋆ ṡuc ṡuc ṡuc ṡuc żero {[]}
_ = begin
        ȧdd · ṫwo · ṫwo
    ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
        (λ̇ λ̇ caseℕ̇ (# 1) (# 0) (ṡuc (ȧdd · # 0 · # 1))) · ṫwo · ṫwo
    ⟶⟨ ξ-·₁ (β-λ̇ value-ṫwo) ⟩
        (λ̇ caseℕ̇ ṫwo (# 0) (ṡuc (ȧdd · # 0 · # 1))) · ṫwo
    ⟶⟨ β-λ̇ value-ṫwo ⟩
        caseℕ̇ ṫwo ṫwo (ṡuc (ȧdd · # 0 · ṫwo))
    ⟶⟨ β-ṡuc value-ȯne ⟩
        ṡuc (ȧdd · ȯne · ṫwo)
    ⟶⟨ ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
        ṡuc ((λ̇ λ̇ caseℕ̇ (# 1) (# 0) (ṡuc (ȧdd · # 0 · # 1))) · ȯne · ṫwo)
    ⟶⟨ ξ-ṡuc (ξ-·₁ (β-λ̇ value-ȯne)) ⟩
        ṡuc ((λ̇ caseℕ̇ ȯne (# 0) (ṡuc (ȧdd · # 0 · # 1))) · ṫwo)
    ⟶⟨ ξ-ṡuc (β-λ̇ value-ṫwo) ⟩
        ṡuc (caseℕ̇ ȯne ṫwo (ṡuc (ȧdd · # 0 · ṫwo)))
    ⟶⟨ ξ-ṡuc (β-ṡuc value-żero) ⟩
        ṡuc ṡuc (ȧdd · żero · ṫwo)
    ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
        ṡuc ṡuc ((λ̇ λ̇ caseℕ̇ (# 1) (# 0) (ṡuc (ȧdd · # 0 · # 1))) · żero · ṫwo)
    ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
        ṡuc ṡuc ((λ̇ caseℕ̇ żero (# 0) (ṡuc (ȧdd · # 0 · # 1))) · ṫwo)
    ⟶⟨ ξ-ṡuc (ξ-ṡuc (β-λ̇ value-ṫwo)) ⟩
        ṡuc ṡuc (caseℕ̇ żero ṫwo (ṡuc (ȧdd · # 0 · ṫwo)))
    ⟶⟨ ξ-ṡuc (ξ-ṡuc β-żero) ⟩
        ṡuc ṡuc ṡuc ṡuc żero
    ∎

_ : ȧddᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero ⟶⋆ ṡuc ṡuc ṡuc ṡuc żero {[]}
_ =
    begin
        ȧddᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero
    ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇))) ⟩
        (λ̇ λ̇ λ̇ ṫwoᶜ · # 1 · (# 2 · # 1 · # 0)) · ṫwoᶜ · λ̇ṡuc · żero
    ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
        (λ̇ λ̇ ṫwoᶜ · # 1 · (ṫwoᶜ · # 1 · # 0)) · λ̇ṡuc · żero
    ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
        (λ̇ ṫwoᶜ · λ̇ṡuc · (ṫwoᶜ · λ̇ṡuc · # 0)) · żero
    ⟶⟨ β-λ̇ value-żero ⟩
        ṫwoᶜ · λ̇ṡuc · (ṫwoᶜ · λ̇ṡuc · żero)
    ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
        (λ̇ λ̇ṡuc · (λ̇ṡuc · # 0)) · (ṫwoᶜ · λ̇ṡuc · żero)
    ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
        (λ̇ λ̇ṡuc · (λ̇ṡuc · # 0)) · ((λ̇ λ̇ṡuc · (λ̇ṡuc · # 0)) · żero)
    ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
        (λ̇ λ̇ṡuc · (λ̇ṡuc · # 0)) · (λ̇ṡuc · (λ̇ṡuc · żero))
    ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
        (λ̇ λ̇ṡuc · (λ̇ṡuc · # 0)) · (λ̇ṡuc · (ṡuc żero))
    ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-ȯne) ⟩
        (λ̇ λ̇ṡuc · (λ̇ṡuc · # 0)) · (ṡuc ṡuc żero)
    ⟶⟨ β-λ̇ value-ṫwo ⟩
        λ̇ṡuc · (λ̇ṡuc · (ṡuc ṡuc żero))
    ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-ṫwo) ⟩
        λ̇ṡuc · (ṡuc ṡuc ṡuc żero)
    ⟶⟨ β-λ̇ value-ṫhree ⟩
        ṡuc ṡuc ṡuc ṡuc żero
    ∎

¬[value×reducible] : {Γ : Context} → {A : Type}
    → {term₁ term₂ : Γ ⊢ A}
    → Value term₁
    → ¬ (term₁ ⟶ term₂)
¬[value×reducible] value-λ̇ ()
¬[value×reducible] value-żero ()
¬[value×reducible] (value-ṡuc value) (ξ-ṡuc reduction) = ¬[value×reducible] value reduction

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

value? : {A : Type}
    → (term : [] ⊢ A)
    → Dec (Value term)
value? term with progress term
... | step reduction = no (¬[reducible×value] reduction)
... | done value = yes value

-- Evaluation

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

μ̇ṡuc : [] ⊢ ℕ̇
μ̇ṡuc = μ̇ ṡuc # 0

_ : eval (gas 3) μ̇ṡuc ≡ steps
    (-- begin
            μ̇ ṡuc lookup here
        ⟶⟨ β-μ̇ ⟩
            ṡuc (μ̇ ṡuc lookup here)
        ⟶⟨ ξ-ṡuc β-μ̇ ⟩
            ṡuc (ṡuc (μ̇ ṡuc lookup here))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc β-μ̇) ⟩
            ṡuc (ṡuc (ṡuc (μ̇ ṡuc lookup here)))
        ∎)
    out-of-gas
_ = refl

_ : eval (gas 100) (ṫwoᶜ · λ̇ṡuc · żero) ≡ steps
    (-- begin
            (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · lookup here)) · żero
        ⟶⟨ β-λ̇ value-żero ⟩
            (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
            (λ̇ ṡuc lookup here) · ṡuc żero
        ⟶⟨ β-λ̇ (value-ṡuc value-żero) ⟩
            ṡuc (ṡuc żero)
        ∎)
    (done (value-ṡuc (value-ṡuc value-żero)))
_ = refl

_ : eval (gas 13) (ȧdd · ṫwo · ṫwo) ≡ steps
    (-- begin
            (μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
        ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
            (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
        ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            caseℕ̇ (ṡuc (ṡuc żero)) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero)))
        ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
            ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
            ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
            ṡuc ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            ṡuc caseℕ̇ (ṡuc żero) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (β-ṡuc value-żero) ⟩
            ṡuc (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
            ṡuc (ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
            ṡuc (ṡuc ((λ̇ caseℕ̇ żero (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
            ṡuc (ṡuc caseℕ̇ żero (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero))))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc β-żero) ⟩
            ṡuc (ṡuc (ṡuc (ṡuc żero)))
        ∎)
    (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
_ = refl

_ : eval (gas 13) (ȧddᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero) ≡ steps
    (-- begin
            (λ̇ (λ̇ (λ̇ (λ̇ lookup (there (there (there here))) · lookup (there here) · (lookup (there (there here)) · lookup (there here) · lookup here))))) · (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇))) ⟩
            (λ̇ (λ̇ (λ̇ (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · lookup (there here) · (lookup (there (there here)) · lookup (there here) · lookup here)))) · (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
            (λ̇ (λ̇ (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · lookup (there here) · ((λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · ((λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · lookup here)) · żero
        ⟶⟨ β-λ̇ value-żero ⟩
            (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · ((λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · żero)
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ (λ̇ ṡuc lookup here) · ((λ̇ ṡuc lookup here) · lookup here)) · ((λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
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

_ : eval (gas 37) (ṁul · ṫwo · ṫwo) ≡ steps
    (-- begin
            (μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
        ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
            (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
        ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero)))
        ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
            (μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
            (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-żero))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero))))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ (ṡuc (ṡuc żero)) żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc (value-ṡuc value-żero)) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc żero · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ value-żero)) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc caseℕ̇ (ṡuc żero) żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-ṡuc value-żero)) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · żero · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero)))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc ((λ̇ caseℕ̇ żero (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (β-λ̇ value-żero))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc caseℕ̇ żero żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc β-żero)) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            caseℕ̇ (ṡuc (ṡuc żero)) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero)))
        ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
            ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
            ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
            ṡuc ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            ṡuc caseℕ̇ (ṡuc żero) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (β-ṡuc value-żero) ⟩
            ṡuc (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
            ṡuc (ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
            ṡuc (ṡuc ((λ̇ caseℕ̇ żero (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
            ṡuc (ṡuc caseℕ̇ żero (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero))))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc β-żero) ⟩
            ṡuc (ṡuc (ṡuc (ṡuc żero)))
        ∎)
    (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
_ = refl

_ : eval (gas 13) (ṁulᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero) ≡ steps
    (-- begin
            (λ̇ (λ̇ (λ̇ lookup (there (there here)) · (lookup (there here) · lookup here)))) · (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇))) ⟩
            (λ̇ (λ̇ (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (lookup (there here) · lookup here))) · (λ̇ (λ̇ lookup (there here) · (lookup (there here) · lookup here))) · (λ̇ ṡuc lookup here) · żero
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
    (done(value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
_ = refl

-- _ : eval (gas 77) (ėxp · ṫwo · ṫwo) ≡ steps
--     (-- begin
--             (μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
--         ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
--             (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · lookup (there (there here)) · lookup here)))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
--         ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · lookup here))) · ṡuc (ṡuc żero)
--         ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
--             caseℕ̇ (ṡuc (ṡuc żero)) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · lookup here))
--         ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
--             (μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
--             (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · lookup (there (there here)) · lookup here)))) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · lookup here))) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ (ṡuc żero) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · lookup here))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · lookup (there (there here)) · lookup here)))) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · lookup here))) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ żero (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there (there here)) · (lookup (there (there (there here))) · lookup (there (there here)) · lookup here))))) · ṡuc (ṡuc żero) · lookup here)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc (value-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc żero))))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ (ṡuc żero) żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((λ̇ caseℕ̇ żero (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc caseℕ̇ żero żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc β-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ (ṡuc żero) (ṡuc żero) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · żero · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((λ̇ caseℕ̇ żero (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc caseℕ̇ żero (ṡuc żero) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc β-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero)
--         ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
--             caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
--             (μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
--             (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup (there here) · (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero))))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · caseℕ̇ (ṡuc (ṡuc żero)) żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc (value-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc żero · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc caseℕ̇ (ṡuc żero) żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc ((λ̇ caseℕ̇ żero (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (β-λ̇ value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc caseℕ̇ żero żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc β-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero)
--         ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
--             caseℕ̇ (ṡuc (ṡuc żero)) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
--             ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             ṡuc ((λ̇ caseℕ̇ (ṡuc żero) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             ṡuc caseℕ̇ (ṡuc żero) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (β-ṡuc value-żero) ⟩
--             ṡuc (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             ṡuc (ṡuc ((λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
--             ṡuc (ṡuc ((λ̇ caseℕ̇ żero (lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · lookup (there here)))) · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             ṡuc (ṡuc caseℕ̇ żero (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (lookup (there here)) (lookup here) (ṡuc (lookup (there (there (there here))) · lookup here · lookup (there here)))))) · lookup here · ṡuc (ṡuc żero))))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc β-żero) ⟩
--             ṡuc (ṡuc (ṡuc (ṡuc żero)))
--         ∎)
--     (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
-- _ = refl

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
determinism (ξ-·₁ {term₂ = term₂} reduction₁) (ξ-·₁ reduction₂) = cong (_· term₂) (determinism reduction₁ reduction₂)
determinism (ξ-·₁ reduction₁) (ξ-·₂ value₂ reduction₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-·₂ value₁ reduction₁) (β-λ̇ value₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-·₂ value₁ reduction₁) (ξ-·₁ reduction₂) = ⊥-elim (¬[value×reducible] value₁ reduction₂)
determinism (ξ-·₂ {term₁ = term₁} value₁ reduction₁) (ξ-·₂ value₂ reduction₂) = cong (term₁ ·_) (determinism reduction₁ reduction₂)
determinism (ξ-ṡuc reduction₁) (ξ-ṡuc reduction₂) = cong ṡuc_ (determinism reduction₁ reduction₂)
determinism (ξ-caseℕ̇ reduction₁) (β-ṡuc value₂) = ⊥-elim (¬[value×reducible] (value-ṡuc value₂) reduction₁)
determinism (ξ-caseℕ̇ {term₂ = term₂} {term₃ = term₃} reduction₁) (ξ-caseℕ̇ reduction₂) = cong (λ term₁ → caseℕ̇ term₁ term₂ term₃) (determinism reduction₁ reduction₂)

-- Bonus: use encode-decode to prove Term-Is-hSet

-- open Relation.Binary.PropositionalEquality.≡-Reasoning

open import plfa.part1.Equality using (cong₃; subst-cong; subst₂; subst-cong₂; subst₂≡subst×subst; subst₂≡id×subst₂; subst₃; subst-cong₃; subst₃≡subst×subst×subst)
open import plfa.part1.Isomorphism using (_≅_; _≲_; Is-hProp; Is-hSet; Is-hGroupoid; ×-Is-hProp; Σ-Is-hProp; ⊤-Is-hProp; ⊥-Is-hProp; Is-hSet-implies-Is-hGroupoid; hProp-iso; ≅-Is-hProp; ≅-Is-hSet)
open import plfa.part1.Quantifiers using (Tree; leaf; node; Tree-Is-hSet)
open import plfa.part1.Lists using (Membership-Is-hSet)

Type≅Tree : Type ≅ Tree
Type≅Tree = record {
        to = to;
        from = from;
        from∘to = from∘to;
        to∘from = to∘from
    } where
        to : Type → Tree
        to ℕ̇ = leaf
        to (A →̇ B) = node (to A) (to B)

        from : Tree → Type
        from leaf = ℕ̇
        from (node tree₁ tree₂) = (from tree₁) →̇ (from tree₂)

        from∘to : (A : Type) → from (to A) ≡ A
        from∘to ℕ̇ = refl
        from∘to (A →̇ B) = cong₂ _→̇_ (from∘to A) (from∘to B)

        to∘from : (tree : Tree) → to (from tree) ≡ tree
        to∘from leaf = refl
        to∘from (node tree₁ tree₂) = cong₂ node (to∘from tree₁) (to∘from tree₂)

Type-Is-hSet : Is-hSet Type
Type-Is-hSet = ≅-Is-hSet Type≅Tree Tree-Is-hSet

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
CodeTerm (λ̇ term₁) (lookup index₂) = ⊥
CodeTerm (λ̇ term₁) (λ̇ term₂) = CodeTerm term₁ term₂
CodeTerm (λ̇ term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (λ̇ term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (λ̇ term₁) (μ̇ term₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (lookup index₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (λ̇ term₂) = ⊥
CodeTerm (_·_ {A = A₁} term₁₁ term₁₂) (_·_ {A = A₂} term₂₁ term₂₂) =
    Σ (A₁ ≡ A₂) λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ } -- use with-abstraction so that we can use pattern-matching lambda definition anyway?!
-- CodeTerm {Γ} (_·_ {A = A₁} {B = B₁} term₁₁ term₁₂) (_·_ {A = A₂} {B = .B₁} term₂₁ term₂₂) =
    -- Σ (A₁ ≡ A₂) λ p → CodeTerm (subst (λ A₁ → Γ ⊢ A₁ →̇ B₁) p term₁₁) term₂₁ × CodeTerm (subst (Γ ⊢_) p term₁₂) term₂₂ -- use Σ type to force the domain of both term₁₁ and term₂₁ to be equal!
-- CodeTerm (_·_ {A = A₁} term₁₁ term₁₂) (_·_ {A = A₂} term₂₁ term₂₂) =
--     Σ (A₁ ≡ A₂) λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ } -- this is wrong, it will cause encodeTerm-decodeTerm to stuck at Σ (A₁ ≡ A₁), must define on all paths p
CodeTerm (term₁₁ · term₁₂) żero = ⊥
CodeTerm (term₁₁ · term₁₂) (ṡuc term₂) = ⊥
CodeTerm (term₁₁ · term₁₂) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (term₁₁ · term₁₂) (μ̇ term₂) = ⊥
CodeTerm żero (lookup index₂) = ⊥
CodeTerm żero (term₂₁ · term₂₂) = ⊥
CodeTerm żero żero = ⊤
CodeTerm żero (ṡuc term₂) = ⊥
CodeTerm żero (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm żero (μ̇ term₂) = ⊥
CodeTerm (ṡuc term₁) (lookup index₂) = ⊥
CodeTerm (ṡuc term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (ṡuc term₁) żero = ⊥
CodeTerm (ṡuc term₁) (ṡuc term₂) = CodeTerm term₁ term₂
CodeTerm (ṡuc term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (ṡuc term₁) (μ̇ term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (lookup index₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (λ̇ term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (term₂₁ · term₂₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) żero = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (ṡuc term₂) = ⊥
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ × CodeTerm term₁₃ term₂₃
CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (μ̇ term₂) = ⊥
CodeTerm (μ̇ term₁) (lookup index₂) = ⊥
CodeTerm (μ̇ term₁) (λ̇ term₂) = ⊥
CodeTerm (μ̇ term₁) (term₂₁ · term₂₂) = ⊥
CodeTerm (μ̇ term₁) żero = ⊥
CodeTerm (μ̇ term₁) (ṡuc term₂) = ⊥
CodeTerm (μ̇ term₁) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ⊥
CodeTerm (μ̇ term₁) (μ̇ term₂) = CodeTerm term₁ term₂

-- CodeTerm : {Γ : Context} → {A : Type} → (term₁ term₂ : Γ ⊢ A) → Set
-- CodeTerm (lookup index₁) (lookup index₂) = index₁ ≡ index₂
-- CodeTerm (λ̇ term₁) (λ̇ term₂) = CodeTerm term₁ term₂
-- CodeTerm (_·_ {A = A₁} term₁₁ term₁₂) (_·_ {A = A₂} term₂₁ term₂₂) = Σ (A₁ ≡ A₂) (λ { refl → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ })
-- CodeTerm żero żero = ⊤
-- CodeTerm (ṡuc term₁) (ṡuc term₂) = CodeTerm term₁ term₂
-- CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) = CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ × CodeTerm term₁₃ term₂₃
-- CodeTerm (μ̇ term₁) (μ̇ term₂) = CodeTerm term₁ term₂
-- CodeTerm _ _ = ⊥

rTerm : {Γ : Context} → {A : Type} → (term : Γ ⊢ A) → CodeTerm term term
rTerm (lookup index) = refl
rTerm (λ̇ term) = rTerm term
rTerm (term₁ · term₂) = refl , rTerm term₁ , rTerm term₂
rTerm żero = tt
rTerm (ṡuc term) = rTerm term
rTerm (caseℕ̇ term₁ term₂ term₃) = rTerm term₁ , rTerm term₂ , rTerm term₃
rTerm (μ̇ term) = rTerm term

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
        -- encodeTerm term₁ term₂ p = subst (CodeTerm term₁) p (rTerm term₁)

        decodeTerm : {Γ : Context} → {A : Type}
            → (term₁ term₂ : Γ ⊢ A)
            → CodeTerm term₁ term₂ → term₁ ≡ term₂
        decodeTerm (lookup index₁) (lookup .index₁) refl = refl
        decodeTerm (λ̇ term₁) (λ̇ term₂) code = cong λ̇_ (decodeTerm term₁ term₂ code)
        -- decodeTerm {Γ} (_·_ {A = A₁} term₁₁ term₁₂) (_·_ {A = A₂} term₂₁ term₂₂) (p , code₁ , code₂) = ?
        decodeTerm (term₁₁ · term₁₂) (term₂₁ · term₂₂) (refl , code₁ , code₂) = cong₂ _·_ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂)
        decodeTerm żero żero tt = refl
        decodeTerm (ṡuc term₁) (ṡuc term₂) code = cong ṡuc_ (decodeTerm term₁ term₂ code)
        decodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) (code₁ , code₂ , code₃) = cong₃ caseℕ̇ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (decodeTerm term₁₃ term₂₃ code₃)
        decodeTerm (μ̇ term₁) (μ̇ term₂) code = cong μ̇_ (decodeTerm term₁ term₂ code)

        decodeTerm-encodeTerm : {Γ : Context} → {A : Type}
            → (term₁ term₂ : Γ ⊢ A)
            → (p : term₁ ≡ term₂) → decodeTerm term₁ term₂ (encodeTerm term₁ term₂ p) ≡ p
        decodeTerm-encodeTerm (lookup index₁) .(lookup index₁) refl = refl
        decodeTerm-encodeTerm (λ̇ term₁) .(λ̇ term₁) refl = cong (cong λ̇_) (decodeTerm-encodeTerm term₁ term₁ refl)
        -- decodeTerm-encodeTerm {Γ} (_·_ {A = A₁} term₁₁ term₁₂) (_·_ {A = A₂} term₂₁ term₂₂) p = ?
        decodeTerm-encodeTerm (term₁₁ · term₁₂) .(term₁₁ · term₁₂) refl = cong₂ (cong₂ _·_) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl)
        decodeTerm-encodeTerm żero .żero refl = refl
        decodeTerm-encodeTerm (ṡuc term₁) .(ṡuc term₁) refl = cong (cong ṡuc_) (decodeTerm-encodeTerm term₁ term₁ refl)
        decodeTerm-encodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) .(caseℕ̇ term₁₁ term₁₂ term₁₃) refl = cong₃ (cong₃ caseℕ̇) (decodeTerm-encodeTerm term₁₁ term₁₁ refl) (decodeTerm-encodeTerm term₁₂ term₁₂ refl) (decodeTerm-encodeTerm term₁₃ term₁₃ refl)
        decodeTerm-encodeTerm (μ̇ term₁) .(μ̇ term₁) refl = cong (cong μ̇_) (decodeTerm-encodeTerm term₁ term₁ refl)

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

        -- encodeTerm-decodeTerm : {Γ : Context} → {A : Type}
        --     → (term₁ term₂ : Γ ⊢ A)
        --     → (code : CodeTerm term₁ term₂) → encodeTerm term₁ term₂ (decodeTerm term₁ term₂ code) ≡ code
        -- encodeTerm-decodeTerm (lookup index₁) (lookup .index₁) refl = refl
        -- encodeTerm-decodeTerm (λ̇ term₁) (λ̇ term₂) code = trans (subst-cong (CodeTerm (λ̇ term₁)) (decodeTerm term₁ term₂ code)) (encodeTerm-decodeTerm term₁ term₂ code)
        -- -- encodeTerm-decodeTerm {Γ} (_·_ {A = A₁} {B = B₁} term₁₁ term₁₂) (_·_ {A = A₂} {B = .B₁} term₂₁ term₂₂) (p , code₁ , code₂) = ?
        -- encodeTerm-decodeTerm {Γ} (_·_ {A = A₁} {B = B₁} term₁₁ term₁₂) (_·_ {A = .A₁} {B = .B₁} term₂₁ term₂₂) (refl , code₁ , code₂) =
        --     begin
        --         encodeTerm (term₁₁ · term₁₂) (term₂₁ · term₂₂) (decodeTerm (term₁₁ · term₁₂) (term₂₁ · term₂₂) (refl , code₁ , code₂))
        --     ≡⟨⟩
        --         encodeTerm (term₁₁ · term₁₂) (term₂₁ · term₂₂) (cong₂ _·_ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂))
        --     ≡⟨⟩
        --         subst (CodeTerm (term₁₁ · term₁₂)) (cong₂ _·_ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂)) (refl , rTerm term₁₁ , rTerm term₁₂)
        --     ≡⟨ subst-cong₂ (CodeTerm (term₁₁ · term₁₂)) (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) ⟩
        --         subst₂ (λ term₂₁ term₂₂ → CodeTerm (term₁₁ · term₁₂) (term₂₁ · term₂₂)) (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (refl , rTerm term₁₁ , rTerm term₁₂)
        --     ≡⟨⟩
        --         subst₂ (λ term₂₁ term₂₂ → Σ (A₁ ≡ A₁) (λ p → CodeTerm (subst (λ A₁ → Γ ⊢ A₁ →̇ B₁) p term₁₁) term₂₁ × CodeTerm (subst (Γ ⊢_) p term₁₂) term₂₂)) (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (refl , rTerm term₁₁ , rTerm term₁₂)
        --         -- subst₂ (λ term₂₁ term₂₂ → Σ (A₁ ≡ A₁) ?) (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (refl , rTerm term₁₁ , rTerm term₁₂) -- this is where it stucks if we use the pattern match definition
        --     ≡⟨ subst₂≡id×subst₂ (A₁ ≡ A₁) (λ term₂₁ term₂₂ p → CodeTerm (subst (λ A₁ → Γ ⊢ A₁ →̇ B₁) p term₁₁) term₂₁ × CodeTerm (subst (Γ ⊢_) p term₁₂) term₂₂) (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) ⟩
        --         refl , subst₂ (λ term₂₁ term₂₂ → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂) (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (rTerm term₁₁ , rTerm term₁₂)
        --     ≡⟨ cong (refl ,_) (subst₂≡subst×subst (CodeTerm term₁₁) (CodeTerm term₁₂) (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂)) ⟩
        --         refl , subst (CodeTerm term₁₁) (decodeTerm term₁₁ term₂₁ code₁) (rTerm term₁₁) , subst (CodeTerm term₁₂) (decodeTerm term₁₂ term₂₂ code₂) (rTerm term₁₂)
        --     ≡⟨⟩
        --         refl , encodeTerm term₁₁ term₂₁ (decodeTerm term₁₁ term₂₁ code₁) , encodeTerm term₁₂ term₂₂ (decodeTerm term₁₂ term₂₂ code₂)
        --     ≡⟨ cong₂ (λ x y → refl , x , y) (encodeTerm-decodeTerm term₁₁ term₂₁ code₁) (encodeTerm-decodeTerm term₁₂ term₂₂ code₂) ⟩
        --         refl , code₁ , code₂
        --     ∎
        -- encodeTerm-decodeTerm żero żero tt = refl
        -- encodeTerm-decodeTerm (ṡuc term₁) (ṡuc term₂) code = trans (subst-cong (CodeTerm (ṡuc term₁)) (decodeTerm term₁ term₂ code)) (encodeTerm-decodeTerm term₁ term₂ code)
        -- encodeTerm-decodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) (code₁ , code₂ , code₃) =
        --     begin
        --         encodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) (decodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) (code₁ , code₂ , code₃))
        --     ≡⟨⟩
        --         encodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) (cong₃ caseℕ̇ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (decodeTerm term₁₃ term₂₃ code₃))
        --     ≡⟨⟩
        --         subst (CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃)) (cong₃ caseℕ̇ (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (decodeTerm term₁₃ term₂₃ code₃)) (rTerm term₁₁ , rTerm term₁₂ , rTerm term₁₃)
        --     ≡⟨ subst-cong₃ (CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃)) (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (decodeTerm term₁₃ term₂₃ code₃) ⟩
        --         subst₃ (λ term₂₁ term₂₂ term₂₃ → CodeTerm (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃)) (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (decodeTerm term₁₃ term₂₃ code₃) (rTerm term₁₁ , rTerm term₁₂ , rTerm term₁₃)
        --     ≡⟨⟩
        --         subst₃ (λ term₂₁ term₂₂ term₂₃ → CodeTerm term₁₁ term₂₁ × CodeTerm term₁₂ term₂₂ × CodeTerm term₁₃ term₂₃) (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (decodeTerm term₁₃ term₂₃ code₃) (rTerm term₁₁ , rTerm term₁₂ , rTerm term₁₃)
        --     ≡⟨ subst₃≡subst×subst×subst (CodeTerm term₁₁) (CodeTerm term₁₂) (CodeTerm term₁₃) (decodeTerm term₁₁ term₂₁ code₁) (decodeTerm term₁₂ term₂₂ code₂) (decodeTerm term₁₃ term₂₃ code₃) ⟩
        --         subst (CodeTerm term₁₁) (decodeTerm term₁₁ term₂₁ code₁) (rTerm term₁₁) , subst (CodeTerm term₁₂) (decodeTerm term₁₂ term₂₂ code₂) (rTerm term₁₂) , subst (CodeTerm term₁₃) (decodeTerm term₁₃ term₂₃ code₃) (rTerm term₁₃)
        --     ≡⟨⟩
        --         encodeTerm term₁₁ term₂₁ (decodeTerm term₁₁ term₂₁ code₁) , encodeTerm term₁₂ term₂₂ (decodeTerm term₁₂ term₂₂ code₂) , encodeTerm term₁₃ term₂₃ (decodeTerm term₁₃ term₂₃ code₃)
        --     ≡⟨ cong₃ (λ x y z → x , y , z) (encodeTerm-decodeTerm term₁₁ term₂₁ code₁) (encodeTerm-decodeTerm term₁₂ term₂₂ code₂) (encodeTerm-decodeTerm term₁₃ term₂₃ code₃) ⟩
        --         code₁ , code₂ , code₃
        --     ∎
        -- encodeTerm-decodeTerm (μ̇ term₁) (μ̇ term₂) code = trans (subst-cong (CodeTerm (μ̇ term₁)) (decodeTerm term₁ term₂ code)) (encodeTerm-decodeTerm term₁ term₂ code)

CodeTerm-Is-hProp : {Γ : Context} → {A : Type}
    → (term₁ term₂ : Γ ⊢ A)
    → Is-hProp (CodeTerm term₁ term₂)
CodeTerm-Is-hProp (lookup index₁) (lookup index₂) = Index-Is-hSet index₁ index₂
CodeTerm-Is-hProp (λ̇ term₁) (λ̇ term₂) = CodeTerm-Is-hProp term₁ term₂
CodeTerm-Is-hProp (_·_ {A = A₁} term₁₁ term₁₂) (_·_ {A = A₂} term₂₁ term₂₂) =
    Σ-Is-hProp (Type-Is-hSet A₁ A₂) λ { refl → ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (CodeTerm-Is-hProp term₁₂ term₂₂) }
-- CodeTerm-Is-hProp {Γ} (_·_ {A = A₁} {B = B₁} term₁₁ term₁₂) (_·_ {A = A₂} {B = .B₁} term₂₁ term₂₂) =
--     Σ-Is-hProp (Type-Is-hSet A₁ A₂) (λ p → ×-Is-hProp
--         (CodeTerm-Is-hProp (subst (λ A₁ → Γ ⊢ A₁ →̇ B₁) p term₁₁) term₂₁)
--         (CodeTerm-Is-hProp (subst (Γ ⊢_) p term₁₂) term₂₂))
CodeTerm-Is-hProp żero żero = ⊤-Is-hProp
CodeTerm-Is-hProp (ṡuc term₁) (ṡuc term₂) = CodeTerm-Is-hProp term₁ term₂
CodeTerm-Is-hProp (caseℕ̇ term₁₁ term₁₂ term₁₃) (caseℕ̇ term₂₁ term₂₂ term₂₃) = ×-Is-hProp (CodeTerm-Is-hProp term₁₁ term₂₁) (×-Is-hProp (CodeTerm-Is-hProp term₁₂ term₂₂) (CodeTerm-Is-hProp term₁₃ term₂₃))
CodeTerm-Is-hProp (μ̇ term₁) (μ̇ term₂) = CodeTerm-Is-hProp term₁ term₂

Term-Is-hSet : {Γ : Context} → {A : Type} → Is-hSet (Γ ⊢ A)
Term-Is-hSet term₁ term₂ = ≅-Is-hProp (Term-eq≅CodeTerm term₁ term₂) (CodeTerm-Is-hProp term₁ term₂)
