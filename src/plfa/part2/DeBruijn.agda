{-# OPTIONS --without-K #-}

module plfa.part2.DeBruijn where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (T; not)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _<_; _<?_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; flip)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import plfa.part1.Isomorphism using (_≅_; _≲_)

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
    ⊢lookup : {Γ : Context} → {A : Type}
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
_ = ⊢lookup here

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
_ = ⊢lookup (there here)

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇
_ = ⊢lookup (there here) · ⊢lookup here

_ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇
_ = ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here)

_ : [] ‚ ℕ̇ →̇ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
_ = λ̇ (⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))

_ : [] ⊢ (ℕ̇ →̇ ℕ̇) →̇ ℕ̇ →̇ ℕ̇
_ = λ̇ λ̇ (⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))

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
#_ n {z} = ⊢lookup (count (toWitness z))

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

-- Renaming

extend : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ∋ A) -- ρ maps each variable (index) of type A in context Γ to a variable of type A in context Δ
    → ({A B : Type} → Γ ‚ B ∋ A → Δ ‚ B ∋ A) -- ρ lifts to a map (by shifting 1) from variables of type A in context Γ extended by B to variables of type A in context Δ extended by B
extend ρ here = here
extend ρ (there index) = there (ρ index)

-- the same proof but using general list, note we need to write refl for here

-- extend : {A : Set} → {xs ys : List A}
--     → ({x : A} → x ∈ xs → x ∈ ys)
--     → ({x y : A} → x ∈ y ∷ xs → x ∈ y ∷ ys)
-- extend ρ (here refl) = here refl
-- extend ρ (there index) = there (ρ index)

-- "index" (intrinsic) == "lookup" (extrinsic) or loosely variables (Id)
-- "term" (intrinsic) == "typing" (extrinsic)

reindex : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ∋ A) -- ρ maps each variable (index) of type A in context Γ to a variable of type A in context Δ
    → ({A : Type} → Γ ⊢ A → Δ ⊢ A) -- ρ lifts to a map from terms of type A in context Γ to terms of type A in context Γ
reindex ρ (⊢lookup index) = ⊢lookup (ρ index)
reindex ρ (λ̇ term) = λ̇ (reindex (extend ρ) term)
reindex ρ (term₁ · term₂) = (reindex ρ term₁) · (reindex ρ term₂)
reindex ρ żero = żero
reindex ρ (ṡuc term) = ṡuc (reindex ρ term)
reindex ρ (caseℕ̇ term₁ term₂ term₃) = caseℕ̇ (reindex ρ term₁) (reindex ρ term₂) (reindex (extend ρ) term₃)
reindex ρ (μ̇ term) = μ̇ (reindex (extend ρ) term)

term₁ : [] ‚ ℕ̇ →̇ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
term₁ = λ̇ # 1 · (# 1 · # 0) -- ∅ , "f" ⦂ ℕ̇ →̇ ℕ̇ ⊢ λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇) ⦂ ℕ̇ →̇ ℕ̇

term₂ : [] ‚ ℕ̇ →̇ ℕ̇ ‚ ℕ̇ ⊢ ℕ̇ →̇ ℕ̇
term₂ = λ̇ # 2 · (# 2 · # 0)

_ : reindex there term₁ ≡ term₂
_ = refl

-- Simultaneous Substitution (with built-in typing preservation)

⊢extend : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ⊢ A) -- σ maps each variable (index) of type A in context Γ to a term of type A in context Δ
    → ({A B : Type} → Γ ‚ B ∋ A → Δ ‚ B ⊢ A) -- σ lifts to a map (by shifting 1) from variables of type A in context Γ extended by B to terms of type A in context Δ extended by B
⊢extend σ here = ⊢lookup here
⊢extend σ (there index) = reindex there (σ index)

substitute : {Γ Δ : Context}
    → ({A : Type} → Γ ∋ A → Δ ⊢ A) -- σ maps each variable (index) of type A in context Γ to a term of type A in context Δ
    → ({A : Type} → Γ ⊢ A → Δ ⊢ A) -- σ lifts to a map from terms of type A in context Γ to terms of type A in context Δ
substitute σ (⊢lookup index) = σ index
substitute σ (λ̇ term) = λ̇ substitute (⊢extend σ) term
substitute σ (term₁ · term₂) = (substitute σ term₁) · (substitute σ term₂)
substitute σ żero = żero
substitute σ (ṡuc term) = ṡuc substitute σ term
substitute σ (caseℕ̇ term₁ term₂ term₃) = caseℕ̇ (substitute σ term₁) (substitute σ term₂) (substitute (⊢extend σ) term₃)
substitute σ (μ̇ term) = μ̇ substitute (⊢extend σ) term

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
σ₁ term (there index) = ⊢lookup index

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
--         (there index) → ⊢lookup index })
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
σ₂ term₁ term₂ (there (there index)) = ⊢lookup index

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
--         (there (there index)) → ⊢lookup index })
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

_ : t3 [ reindex there r3 ] [ s3 ] ≡ t3[s3][r3]
_ = refl

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
            μ̇ ṡuc ⊢lookup here
        ⟶⟨ β-μ̇ ⟩
            ṡuc (μ̇ ṡuc ⊢lookup here)
        ⟶⟨ ξ-ṡuc β-μ̇ ⟩
            ṡuc (ṡuc (μ̇ ṡuc ⊢lookup here))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc β-μ̇) ⟩
            ṡuc (ṡuc (ṡuc (μ̇ ṡuc ⊢lookup here)))
        ∎)
    out-of-gas
_ = refl

_ : eval (gas 100) (ṫwoᶜ · λ̇ṡuc · żero) ≡ steps
    (-- begin
            (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · ⊢lookup here)) · żero
        ⟶⟨ β-λ̇ value-żero ⟩
            (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
            (λ̇ ṡuc ⊢lookup here) · ṡuc żero
        ⟶⟨ β-λ̇ (value-ṡuc value-żero) ⟩
            ṡuc (ṡuc żero)
        ∎)
    (done (value-ṡuc (value-ṡuc value-żero)))
_ = refl

_ : eval (gas 13) (ȧdd · ṫwo · ṫwo) ≡ steps
    (-- begin
            (μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
        ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
            (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
        ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            caseℕ̇ (ṡuc (ṡuc żero)) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero)))
        ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
            ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
            ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
            ṡuc ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            ṡuc caseℕ̇ (ṡuc żero) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (β-ṡuc value-żero) ⟩
            ṡuc (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
            ṡuc (ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
            ṡuc (ṡuc ((λ̇ caseℕ̇ żero (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
            ṡuc (ṡuc caseℕ̇ żero (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero))))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc β-żero) ⟩
            ṡuc (ṡuc (ṡuc (ṡuc żero)))
        ∎)
    (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
_ = refl

_ : eval (gas 13) (ȧddᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero) ≡ steps
    (-- begin
            (λ̇ (λ̇ (λ̇ (λ̇ ⊢lookup (there (there (there here))) · ⊢lookup (there here) · (⊢lookup (there (there here)) · ⊢lookup (there here) · ⊢lookup here))))) · (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇))) ⟩
            (λ̇ (λ̇ (λ̇ (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · ⊢lookup (there here) · (⊢lookup (there (there here)) · ⊢lookup (there here) · ⊢lookup here)))) · (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
            (λ̇ (λ̇ (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · ⊢lookup (there here) · ((λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · ⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · ((λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · ⊢lookup here)) · żero
        ⟶⟨ β-λ̇ value-żero ⟩
            (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · ((λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · żero)
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ (λ̇ ṡuc ⊢lookup here) · ((λ̇ ṡuc ⊢lookup here) · ⊢lookup here)) · ((λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
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

-- _ : eval (gas 37) (ṁul · ṫwo · ṫwo) ≡ steps
--     (-- begin
--             (μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
--         ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
--             (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
--         ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero)
--         ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
--             caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
--             (μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
--             (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero))))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ (ṡuc (ṡuc żero)) żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc (value-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc żero · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc caseℕ̇ (ṡuc żero) żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc ((λ̇ caseℕ̇ żero (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (β-λ̇ value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc caseℕ̇ żero żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc β-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero)
--         ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
--             caseℕ̇ (ṡuc (ṡuc żero)) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
--             ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             ṡuc ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             ṡuc caseℕ̇ (ṡuc żero) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (β-ṡuc value-żero) ⟩
--             ṡuc (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             ṡuc (ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
--             ṡuc (ṡuc ((λ̇ caseℕ̇ żero (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             ṡuc (ṡuc caseℕ̇ żero (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero))))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc β-żero) ⟩
--             ṡuc (ṡuc (ṡuc (ṡuc żero)))
--         ∎)
--     (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
-- _ = refl

_ : eval (gas 13) (ṁulᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero) ≡ steps
    (-- begin
            (λ̇ (λ̇ (λ̇ ⊢lookup (there (there here)) · (⊢lookup (there here) · ⊢lookup here)))) · (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇))) ⟩
            (λ̇ (λ̇ (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ (λ̇ ⊢lookup (there here) · (⊢lookup (there here) · ⊢lookup here))) · (λ̇ ṡuc ⊢lookup here) · żero
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
    (done(value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
_ = refl

-- _ : eval (gas 77) (ėxp · ṫwo · ṫwo) ≡ steps
--     (-- begin
--             (μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
--         ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
--             (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ⊢lookup (there (there here)) · ⊢lookup here)))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
--         ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · ⊢lookup here))) · ṡuc (ṡuc żero)
--         ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
--             caseℕ̇ (ṡuc (ṡuc żero)) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · ⊢lookup here))
--         ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
--             (μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
--             (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ⊢lookup (there (there here)) · ⊢lookup here)))) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · ⊢lookup here))) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ (ṡuc żero) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · ⊢lookup here))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ⊢lookup (there (there here)) · ⊢lookup here)))) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · ⊢lookup here))) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ żero (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup here) (ṡuc żero) ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there (there here)) · (⊢lookup (there (there (there here))) · ⊢lookup (there (there here)) · ⊢lookup here))))) · ṡuc (ṡuc żero) · ⊢lookup here)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc (value-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc żero))))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ (ṡuc żero) żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((λ̇ caseℕ̇ żero (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc caseℕ̇ żero żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc β-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ (ṡuc żero) (ṡuc żero) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · żero · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((λ̇ caseℕ̇ żero (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc caseℕ̇ żero (ṡuc żero) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc β-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero)
--         ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
--             caseℕ̇ (ṡuc (ṡuc żero)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
--             (μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
--             (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ (ṡuc żero) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ żero żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc (ṡuc żero) · ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) żero ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup (there here) · (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero))))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ((λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · caseℕ̇ (ṡuc (ṡuc żero)) żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc (value-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc żero · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc caseℕ̇ (ṡuc żero) żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-ṡuc value-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero)))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc ((λ̇ caseℕ̇ żero (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (β-λ̇ value-żero))) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc caseℕ̇ żero żero (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc β-żero)) ⟩
--             (λ̇ caseℕ̇ (ṡuc (ṡuc żero)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero)
--         ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
--             caseℕ̇ (ṡuc (ṡuc żero)) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
--             ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             ṡuc ((λ̇ caseℕ̇ (ṡuc żero) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             ṡuc caseℕ̇ (ṡuc żero) (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (β-ṡuc value-żero) ⟩
--             ṡuc (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             ṡuc (ṡuc ((λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here))))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
--             ṡuc (ṡuc ((λ̇ caseℕ̇ żero (⊢lookup here) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ⊢lookup (there here)))) · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             ṡuc (ṡuc caseℕ̇ żero (ṡuc (ṡuc żero)) (ṡuc ((μ̇ (λ̇ (λ̇ caseℕ̇ (⊢lookup (there here)) (⊢lookup here) (ṡuc (⊢lookup (there (there (there here))) · ⊢lookup here · ⊢lookup (there here)))))) · ⊢lookup here · ṡuc (ṡuc żero))))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc β-żero) ⟩
--             ṡuc (ṡuc (ṡuc (ṡuc żero)))
--         ∎)
--     (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
-- _ = refl

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
determinism (ξ-·₁ {term₂ = term₂} reduction₁) (ξ-·₁ reduction₂) = cong (_· term₂) (determinism reduction₁ reduction₂)
determinism (ξ-·₁ reduction₁) (ξ-·₂ value₂ reduction₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-·₂ value₁ reduction₁) (β-λ̇ value₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-·₂ value₁ reduction₁) (ξ-·₁ reduction₂) = ⊥-elim (¬[value×reducible] value₁ reduction₂)
determinism (ξ-·₂ {term₁ = term₁} value₁ reduction₁) (ξ-·₂ value₂ reduction₂) = cong (term₁ ·_) (determinism reduction₁ reduction₂)
determinism (ξ-ṡuc reduction₁) (ξ-ṡuc reduction₂) = cong ṡuc_ (determinism reduction₁ reduction₂)
determinism (ξ-caseℕ̇ reduction₁) (β-ṡuc value₂) = ⊥-elim (¬[value×reducible] (value-ṡuc value₂) reduction₁)
determinism (ξ-caseℕ̇ {term₂ = term₂} {term₃ = term₃} reduction₁) (ξ-caseℕ̇ reduction₂) = cong (λ term₁ → caseℕ̇ term₁ term₂ term₃) (determinism reduction₁ reduction₂)
