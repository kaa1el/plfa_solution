{-# OPTIONS --without-K #-}

module plfa.part2.Lambda where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)

open import plfa.part1.Isomorphism using (_≅_; _≲_)
open import plfa.part1.Quantifiers using (Is-hProp; Σ-Is-Prop-iso)

-- Gordon Plotkin's Programmable Computable Functions (PCF) (1977)

-- Identifiers (Variables)

Id : Set
Id = String

infix 5 λ̇_⇒_
infix 5 μ_⇒_
infixl 7 _·_
infix 8 ṡuc_
infix 9 _̇

-- Terms

data Term : Set where
    _̇ : Id → Term
    λ̇_⇒_ : Id → Term → Term
    _·_ : Term → Term → Term
    μ_⇒_ : Id → Term → Term
    żero : Term
    ṡuc_ : Term → Term
    case_[żero⇒_|ṡuc_⇒_] : Term → Term → Id → Term → Term

ȯne : Term
ȯne = ṡuc żero

ṫwo : Term
ṫwo = ṡuc ȯne

ṫhree : Term
ṫhree = ṡuc ṫwo

ȧdd : Term
ȧdd = μ "+" ⇒ λ̇ "n" ⇒ λ̇ "m" ⇒ case "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]

ṁul : Term
ṁul = μ "*" ⇒ λ̇ "n" ⇒ λ̇ "m" ⇒ case "n"̇ [żero⇒ żero |ṡuc "n" ⇒ ȧdd · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]

ėxp : Term
ėxp = μ "^" ⇒ λ̇ "n" ⇒ λ̇ "m" ⇒ case "m"̇ [żero⇒ ȯne |ṡuc "m" ⇒ ṁul · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]

λ̇ṡuc : Term
λ̇ṡuc = λ̇ "n" ⇒ ṡuc "n"̇

-- Church numerals

żeroᶜ : Term
żeroᶜ = λ̇ "f" ⇒ λ̇ "x" ⇒ "x"̇

ṡucᶜ : Term
ṡucᶜ = λ̇ "n" ⇒ λ̇ "f" ⇒ λ̇ "x" ⇒ "f"̇ · ("n"̇ · "f"̇ · "x"̇)

ȯneᶜ : Term
ȯneᶜ = λ̇ "f" ⇒ λ̇ "x" ⇒ "f"̇ · "x"̇

ṫwoᶜ : Term
ṫwoᶜ = λ̇ "f" ⇒ λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇)

ṫhreeᶜ : Term
ṫhreeᶜ = λ̇ "f" ⇒ λ̇ "x" ⇒ "f"̇ · ("f"̇ · ("f"̇ · "x"̇))

ȧddᶜ : Term
ȧddᶜ = λ̇ "n" ⇒ λ̇ "m" ⇒ λ̇ "f" ⇒ λ̇ "x" ⇒ "n"̇ · "f"̇ · ("m"̇ · "f"̇ · "x"̇)

ṁulᶜ : Term
ṁulᶜ = λ̇ "n" ⇒ λ̇ "m" ⇒ λ̇ "f" ⇒ "n"̇ · ("m"̇ · "f"̇)

ėxpᶜ : Term
ėxpᶜ = λ̇ "n" ⇒ λ̇ "m" ⇒ "m"̇ · "n"̇

-- Values

data Value : Term → Set where
    value-λ̇ : {x : Id} → {t : Term} → Value (λ̇ x ⇒ t)
    value-żero : Value żero
    value-ṡuc : {t : Term} → Value t → Value (ṡuc t)

value-ȯne : Value ȯne
value-ȯne = value-ṡuc value-żero

value-ṫwo : Value ṫwo
value-ṫwo = value-ṡuc value-ȯne

value-ṫhree : Value ṫhree
value-ṫhree = value-ṡuc value-ṫwo

-- Here we consider closed terms and functions as values,
-- thereʳ are alternative choices where variables can be considered as values as well

-- Substitution

infix 9 _[_:=_]

-- Here the term s is assumed to be closed, otherwise the definition would require
-- renaming of bounded variables

_[_:=_] : Term → Id → Term → Term
(x ̇) [ y := s ] with x ≟ y
... | no _ = x ̇
... | yes _ = s
(λ̇ x ⇒ t) [ y := s ] with x ≟ y
... | no _ = λ̇ x ⇒ (t [ y := s ])
... | yes _ = λ̇ x ⇒ t
(t₁ · t₂) [ y := s ] = t₁ [ y := s ] · t₂ [ y := s ]
(μ x ⇒ t) [ y := s ] with x ≟ y
... | no _ = μ x ⇒ (t [ y := s ])
... | yes _ = μ x ⇒ t
żero [ y := s ] = żero
(ṡuc t) [ y := s ] = ṡuc (t [ y := s ])
case t [żero⇒ t₁ |ṡuc x ⇒ t₂ ] [ y := s ] with x ≟ y
... | no _ = case (t [ y := s ]) [żero⇒ (t₁ [ y := s ]) |ṡuc x ⇒ (t₂ [ y := s ]) ]
... | yes _ = case (t [ y := s ]) [żero⇒ (t₁ [ y := s ]) |ṡuc x ⇒ t₂ ]

_ : (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇)) [ "f" := ṡucᶜ ] ≡ λ̇ "x" ⇒ ṡucᶜ · (ṡucᶜ · "x"̇)
_ = refl

_ : (ṡucᶜ · (ṡucᶜ · "x"̇)) [ "x" := żeroᶜ ] ≡ ṡucᶜ · (ṡucᶜ · żeroᶜ)
_ = refl

_ : (λ̇ "x" ⇒ "y"̇) [ "y" := żero ] ≡ λ̇ "x" ⇒ żero
_ = refl

_ : (λ̇ "x" ⇒ "x"̇) [ "x" := żero ] ≡ λ̇ "x" ⇒ "x"̇
_ = refl

_ : (λ̇ "y" ⇒ "y"̇) [ "x" := żero ] ≡ λ̇ "y" ⇒ "y"̇
_ = refl

infix 9 _[_:=_]′

_[_≟_:=_]″ : Term → Id → Id → Term → Term
_[_:=_]′ : Term → Id → Term → Term

t [ x ≟ y := s ]″ with x ≟ y
... | no _ = t [ y := s ]′
... | yes _ = t

(x ̇) [ y := s ]′ with x ≟ y
... | no _ = x ̇
... | yes _ = s
(λ̇ x ⇒ t) [ y := s ]′ = λ̇ x ⇒ t [ x ≟ y := s ]″
(t₁ · t₂) [ y := s ]′ = t₁ [ y := s ]′ · t₂ [ y := s ]′
(μ x ⇒ t) [ y := s ]′ = μ x ⇒  t [ x ≟ y := s ]″
żero [ y := s ]′ = żero
(ṡuc t) [ y := s ]′ = ṡuc (t [ y := s ]′)
case t [żero⇒ t₁ |ṡuc x ⇒ t₂ ] [ y := s ]′ = case (t [ y := s ]′) [żero⇒ (t₁ [ y := s ]′) |ṡuc x ⇒ (t₂ [ x ≟ y := s ]″) ]

-- Reduction (call by value) (small-step operational semantics)

infix 2 _⟶_

data _⟶_ : Term → Term → Set where
    ξ-·₁ : {t t′ s : Term} -- ξ's are compatibility rules
        → t ⟶ t′
        → t · s ⟶ t′ · s
    ξ-·₂ : {t s s′ : Term} -- this reduction strategy is done left to right
        → Value t
        → s ⟶ s′
        → t · s ⟶ t · s′
    ξ-ṡuc : {t t′ : Term}
        → t ⟶ t′
        → ṡuc t ⟶ ṡuc t′
    ξ-case : {x : Id} → {t t′ s r : Term}
        → t ⟶ t′
        → case t [żero⇒ s |ṡuc x ⇒ r ] ⟶ case t′ [żero⇒ s |ṡuc x ⇒ r ]
    β-λ̇ : {x : Id} → {t s : Term} -- call by value reduction (another choice is call by name)
        → Value s
        → (λ̇ x ⇒ t) · s ⟶ t [ x := s ]
    β-żero : {x : Id} → {s r : Term}
        → case żero [żero⇒ s |ṡuc x ⇒ r ] ⟶ s
    β-ṡuc :  {x : Id} → {t s r : Term}
        → Value t
        → case (ṡuc t) [żero⇒ s |ṡuc x ⇒ r ] ⟶ r [ x := t ]
    β-μ : {x : Id} → {t : Term}
        → μ x ⇒ t ⟶ t [ x := μ x ⇒ t ]

_ : (λ̇ "x" ⇒ "x"̇) · (λ̇ "x" ⇒ "x"̇) ⟶ (λ̇ "x" ⇒ "x"̇)
_ = β-λ̇ value-λ̇

_ : (λ̇ "x" ⇒ "x"̇) · (λ̇ "x" ⇒ "x"̇) · (λ̇ "x" ⇒ "x"̇) ⟶ (λ̇ "x" ⇒ "x"̇) · (λ̇ "x" ⇒ "x"̇)
_ = ξ-·₁ (β-λ̇ value-λ̇)

_ : ṫwoᶜ · ṡucᶜ · żeroᶜ ⟶ (λ̇ "x" ⇒ ṡucᶜ · (ṡucᶜ · "x"̇)) · żeroᶜ
_ = ξ-·₁ (β-λ̇ value-λ̇)

-- _⟶⋆_ is the reflexive and transitive closure of _⟶_

infix  2 _⟶⋆_
infix  1 begin_
infixr 2 _⟶⟨_⟩_
infix  3 _∎

data _⟶⋆_ : Term → Term → Set where
    _∎ : (t : Term)
        → t ⟶⋆ t
    _⟶⟨_⟩_ : (t : Term) → {s r : Term}
        → t ⟶ s
        → s ⟶⋆ r
        → t ⟶⋆ r

begin_ : {t s : Term}
    → t ⟶⋆ s
    → t ⟶⋆ s
begin ps = ps

trans-⟶⋆ : {t s r : Term}
    → t ⟶⋆ s
    → s ⟶⋆ r
    → t ⟶⋆ r
trans-⟶⋆ (_ ∎) qs = qs
trans-⟶⋆ (t ⟶⟨ p ⟩ ps) qs = t ⟶⟨ p ⟩ trans-⟶⋆ ps qs

-- alternative definition (not initial (least)):

data _⟶⋆′_ : Term → Term → Set where
    step′ : {t s : Term}
        → t ⟶ s
        → t ⟶⋆′ s
    refl′ : {t : Term}
        → t ⟶⋆′ t
    trans′ : {t s r : Term}
        → t ⟶⋆′ s
        → s ⟶⋆′ r
        → t ⟶⋆′ r

⟶⋆≲⟶⋆′ : {t s : Term}
    → t ⟶⋆ s ≲ t ⟶⋆′ s
⟶⋆≲⟶⋆′ = record {
        to = to;
        from = from;
        from∘to = from∘to
        -- to∘from = to∘from
    } where
        to : {t s : Term}
            → t ⟶⋆ s → t ⟶⋆′ s
        to {t} {.t} (.t ∎) = refl′
        to {t} {s} (.t ⟶⟨ p ⟩ ps) = trans′ (step′ p) (to ps)

        from : {t s : Term}
            → t ⟶⋆′ s → t ⟶⋆ s
        from {t} {s} (step′ p) = t ⟶⟨ p ⟩ (s ∎)
        from {t} {.t} refl′ = t ∎
        from (trans′ ps qs) = trans-⟶⋆ (from ps) (from qs)

        from∘to : {t s : Term}
            → (ps : t ⟶⋆ s) → from (to ps) ≡ ps
        from∘to (_ ∎) = refl
        from∘to {t} (_ ⟶⟨ p ⟩ ps) = cong (t ⟶⟨ p ⟩_) (from∘to ps)

        -- to∘from : {t s : Term}
        --     → (ps : t ⟶⋆′ s) → to (from ps) ≡ ps
        -- to∘from (step′ p) = ?
        -- to∘from refl′ = refl
        -- to∘from (trans′ ps qs) = ?

-- ⟶⋆′ is not isomorphic to ⟶⋆ because it has non-canonical terms
-- canonical terms are those in the form of trans′ (step′ p1) (trans′ (step′ p2) ... refl′)

data Is-Canonical : {t s : Term} → t ⟶⋆′ s → Set where
    refl′-Is-Canonical : {t : Term}
        → Is-Canonical (refl′ {t})
    trans′-Is-Canonical : {t s r : Term}
        → (p : t ⟶ s) → (ps : s ⟶⋆′ r)
        → Is-Canonical ps
        → Is-Canonical (trans′ (step′ p) ps)

⟶⋆≅Σ⟶⋆′Is-Canonical : {t s : Term}
    → t ⟶⋆ s ≅ Σ (t ⟶⋆′ s) Is-Canonical
⟶⋆≅Σ⟶⋆′Is-Canonical = Σ-Is-Prop-iso to from from∘to Is-Canonical-Is-hProp to-Is-Canonical Is-Canonical→to∘from
    where
        to : {t s : Term}
            → t ⟶⋆ s → t ⟶⋆′ s
        to {t} {.t} (.t ∎) = refl′
        to {t} {s} (.t ⟶⟨ p ⟩ ps) = trans′ (step′ p) (to ps)

        from : {t s : Term}
            → t ⟶⋆′ s → t ⟶⋆ s
        from {t} {s} (step′ p) = t ⟶⟨ p ⟩ (s ∎)
        from {t} {.t} refl′ = t ∎
        from (trans′ ps qs) = trans-⟶⋆ (from ps) (from qs)

        from∘to : {t s : Term}
            → (p : t ⟶⋆ s) → from (to p) ≡ p
        from∘to (_ ∎) = refl
        from∘to {t} (_ ⟶⟨ p ⟩ ps) = cong (t ⟶⟨ p ⟩_) (from∘to ps)

        Is-Canonical-Is-hProp : {t s : Term} → {ps : t ⟶⋆′ s}
            → Is-hProp (Is-Canonical ps)
        Is-Canonical-Is-hProp refl′-Is-Canonical refl′-Is-Canonical = refl
        Is-Canonical-Is-hProp (trans′-Is-Canonical p ps u) (trans′-Is-Canonical .p .ps v) = cong (trans′-Is-Canonical p ps) (Is-Canonical-Is-hProp u v)

        to-Is-Canonical : {t s : Term}
            → (ps : t ⟶⋆ s)
            → Is-Canonical (to ps)
        to-Is-Canonical (_ ∎) = refl′-Is-Canonical
        to-Is-Canonical (_ ⟶⟨ p ⟩ ps) = trans′-Is-Canonical p (to ps) (to-Is-Canonical ps)

        Is-Canonical→to∘from : {t s : Term}
            → (ps : t ⟶⋆′ s)
            → Is-Canonical ps
            → to (from ps) ≡ ps
        Is-Canonical→to∘from .refl′ refl′-Is-Canonical = refl
        Is-Canonical→to∘from .(trans′ (step′ p) ps) (trans′-Is-Canonical p ps u) = cong (trans′ (step′ p)) (Is-Canonical→to∘from ps u)

_ : ṫwoᶜ · λ̇ṡuc · żero ⟶⋆ ṡuc ṡuc żero
_ =
    begin
        ṫwoᶜ · λ̇ṡuc · żero
    ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
        (λ̇ "x" ⇒ λ̇ṡuc · (λ̇ṡuc · "x"̇)) · żero
    ⟶⟨ β-λ̇ value-żero ⟩
        λ̇ṡuc · (λ̇ṡuc · żero)
    ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
        λ̇ṡuc · (ṡuc żero)
    ⟶⟨ β-λ̇ (value-ṡuc value-żero) ⟩
        ṡuc ṡuc żero
    ∎

_ : ȧdd · ṫwo · ṫwo ⟶⋆ ṡuc ṡuc ṡuc ṡuc żero
_ =
    begin
        ȧdd · ṫwo · ṫwo
    ⟶⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
        (λ̇ "n" ⇒ λ̇ "m" ⇒ case "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc (ȧdd · "n"̇ · "m"̇) ]) · ṫwo · ṫwo
    ⟶⟨ ξ-·₁ (β-λ̇ value-ṫwo) ⟩
        (λ̇ "m" ⇒ case ṫwo [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc (ȧdd · "n"̇ · "m"̇) ]) · ṫwo
    ⟶⟨ β-λ̇ value-ṫwo ⟩
        case ṫwo [żero⇒ ṫwo |ṡuc "n" ⇒ ṡuc (ȧdd · "n"̇ · ṫwo) ]
    ⟶⟨ β-ṡuc value-ȯne ⟩
        ṡuc (ȧdd · ȯne · ṫwo)
    ⟶⟨ ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
        ṡuc ((λ̇ "n" ⇒ λ̇ "m" ⇒ case "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc (ȧdd · "n"̇ · "m"̇) ]) · ȯne · ṫwo)
    ⟶⟨ ξ-ṡuc (ξ-·₁ (β-λ̇ value-ȯne)) ⟩
        ṡuc ((λ̇ "m" ⇒ case ȯne [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc (ȧdd · "n"̇ · "m"̇) ]) · ṫwo)
    ⟶⟨ ξ-ṡuc (β-λ̇ value-ṫwo) ⟩
        ṡuc (case ȯne [żero⇒ ṫwo |ṡuc "n" ⇒ ṡuc (ȧdd · "n"̇ · ṫwo) ])
    ⟶⟨ ξ-ṡuc (β-ṡuc value-żero) ⟩
        ṡuc (ṡuc (ȧdd · żero · ṫwo))
    ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
        ṡuc (ṡuc ((λ̇ "n" ⇒ λ̇ "m" ⇒ case "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc (ȧdd · "n"̇ · "m"̇) ]) · żero · ṫwo))
    ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
        ṡuc (ṡuc ((λ̇ "m" ⇒ case żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc (ȧdd · "n"̇ · "m"̇) ]) · ṫwo))
    ⟶⟨ ξ-ṡuc (ξ-ṡuc (β-λ̇ value-ṫwo)) ⟩
        ṡuc (ṡuc (case żero [żero⇒ ṫwo |ṡuc "n" ⇒ ṡuc (ȧdd · "n"̇ · ṫwo) ]))
    ⟶⟨ ξ-ṡuc (ξ-ṡuc β-żero) ⟩
        ṡuc ṡuc ṡuc ṡuc żero
    ∎

_ : ȧddᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero ⟶⋆ ṡuc ṡuc ṡuc ṡuc żero
_ =
    begin
        ȧddᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero
    ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇))) ⟩
        (λ̇ "m" ⇒ λ̇ "f" ⇒ λ̇ "x" ⇒ ṫwoᶜ · "f"̇ · ("m"̇ · "f"̇ · "x"̇)) · ṫwoᶜ · λ̇ṡuc · żero
    ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
        (λ̇ "f" ⇒ λ̇ "x" ⇒ ṫwoᶜ · "f"̇ · (ṫwoᶜ · "f"̇ · "x"̇)) · λ̇ṡuc · żero
    ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
        (λ̇ "x" ⇒ ṫwoᶜ · λ̇ṡuc · (ṫwoᶜ · λ̇ṡuc · "x"̇)) · żero
    ⟶⟨ β-λ̇ value-żero ⟩
        ṫwoᶜ · λ̇ṡuc · (ṫwoᶜ · λ̇ṡuc · żero)
    ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
        (λ̇ "x" ⇒ λ̇ṡuc · (λ̇ṡuc · "x"̇)) · (ṫwoᶜ · λ̇ṡuc · żero)
    ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
        (λ̇ "x" ⇒ λ̇ṡuc · (λ̇ṡuc · "x"̇)) · ((λ̇ "x" ⇒ λ̇ṡuc · (λ̇ṡuc · "x"̇)) · żero)
    ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
        (λ̇ "x" ⇒ λ̇ṡuc · (λ̇ṡuc · "x"̇)) · (λ̇ṡuc · (λ̇ṡuc · żero))
    ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
        (λ̇ "x" ⇒ λ̇ṡuc · (λ̇ṡuc · "x"̇)) · (λ̇ṡuc · (ṡuc żero))
    ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-ȯne) ⟩
        (λ̇ "x" ⇒ λ̇ṡuc · (λ̇ṡuc · "x"̇)) · (ṡuc ṡuc żero)
    ⟶⟨ β-λ̇ value-ṫwo ⟩
        λ̇ṡuc · (λ̇ṡuc · (ṡuc ṡuc żero))
    ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-ṫwo) ⟩
        λ̇ṡuc · (ṡuc ṡuc ṡuc żero)
    ⟶⟨ β-λ̇ value-ṫhree ⟩
        ṡuc ṡuc ṡuc ṡuc żero
    ∎

-- Types and Contexts

infixr 7 _⇒_

data Type : Set where
    ℕ̇ : Type
    _⇒_ : Type → Type → Type

infixl 5 _,_⦂_

data Context : Set where
    ∅ : Context
    _,_⦂_ : Context → Id → Type → Context

Context≅List[Id×Type] : Context ≅ List (Id × Type)
Context≅List[Id×Type] = record {
        to = to;
        from = from;
        from∘to = from∘to;
        to∘from = to∘from
    } where
        to : Context → List (Id × Type)
        to ∅ = []
        to (Γ , x ⦂ A) = (x , A) ∷ (to Γ)

        from : List (Id × Type) → Context
        from [] = ∅
        from ((x , A) ∷ pairs) = (from pairs) , x ⦂ A

        from∘to : (Γ : Context) → from (to Γ) ≡ Γ
        from∘to ∅ = refl
        from∘to (Γ , x ⦂ A) = cong (_, x ⦂ A) (from∘to Γ)

        to∘from : (pairs : List (Id × Type)) → to (from pairs) ≡ pairs
        to∘from [] = refl
        to∘from ((x , A) ∷ pairs) = cong ((x , A) ∷_) (to∘from pairs)

-- Context lookup

-- if more than one type are associated to a variable in the context,
-- then the lookup will pick the right-most one, the other ones are shadowed

infix 4 _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where
    here : {Γ : Context} → {x : Id} → {A : Type}
        → Γ , x ⦂ A ∋ x ⦂ A
    there : {Γ : Context} → {x y : Id} → {A B : Type}
        → x ≢ y
        → Γ ∋ x ⦂ A
        → Γ , y ⦂ B ∋ x ⦂ A

-- thereʳ using reflection

thereʳ : {Γ : Context} → {x y : Id} → {A B : Type}
        → {proof : False (x ≟ y)}
        → Γ ∋ x ⦂ A
        → Γ , y ⦂ B ∋ x ⦂ A
thereʳ {proof = proof} lookup = there (toWitnessFalse proof) lookup

-- Typing judgement

infix 4 _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where
    ⊢lookup : {Γ : Context} → {x : Id} → {A : Type}
        → Γ ∋ x ⦂ A
        → Γ ⊢ x ̇ ⦂ A -- from context lookup, or picking a variable
    ⊢λ̇ : {Γ : Context} → {x : Id} → {t : Term} → {A B : Type}
        → Γ , x ⦂ A ⊢ t ⦂ B
        → Γ ⊢ (λ̇ x ⇒ t) ⦂ A ⇒ B -- →-intro
    ⊢· : {Γ : Context} → {t s : Term} → {A B : Type}
        → Γ ⊢ t ⦂ A ⇒ B
        → Γ ⊢ s ⦂ A
        → Γ ⊢ (t · s) ⦂ B -- →-elim
    ⊢żero : {Γ : Context}
        → Γ ⊢ żero ⦂ ℕ̇ -- ℕ-intro-zero
    ⊢ṡuc : {Γ : Context} → {t : Term}
        → Γ ⊢ t ⦂ ℕ̇
        → Γ ⊢ ṡuc t ⦂ ℕ̇ -- ℕ-intro-suc
    ⊢case : {Γ : Context} → {x : Id} → {t s r : Term} → {A : Type}
        → Γ ⊢ t ⦂ ℕ̇
        → Γ ⊢ s ⦂ A
        → Γ , x ⦂ ℕ̇ ⊢ r ⦂ A
        → Γ ⊢ case t [żero⇒ s |ṡuc x ⇒ r ] ⦂ A -- ℕ-elim
    ⊢μ : {Γ : Context} → {x : Id} → {t : Term} → {A : Type}
        → Γ , x ⦂ A ⊢ t ⦂ A
        → Γ ⊢ (μ x ⇒ t) ⦂ A -- μ-intro, the fixpoint operator, can view μ : (A → A) → A

_ : ∅ , "f" ⦂ ℕ̇ ⇒ ℕ̇ , "x" ⦂ ℕ̇ ⊢ "x"̇ ⦂ ℕ̇
_ = ⊢lookup here

_ : ∅ , "f" ⦂ ℕ̇ ⇒ ℕ̇ , "x" ⦂ ℕ̇ ⊢ "f"̇ ⦂ ℕ̇ ⇒ ℕ̇
_ = ⊢lookup (thereʳ here)

_ : ∅ , "f" ⦂ ℕ̇ ⇒ ℕ̇ , "x" ⦂ ℕ̇ ⊢ "f"̇ · "x"̇ ⦂ ℕ̇
_ = ⊢· (⊢lookup (thereʳ here)) (⊢lookup here)

_ : ∅ , "f" ⦂ ℕ̇ ⇒ ℕ̇ , "x" ⦂ ℕ̇ ⊢ "f"̇ · ("f"̇ · "x"̇) ⦂ ℕ̇
_ = ⊢· (⊢lookup (thereʳ here)) (⊢· (⊢lookup (thereʳ here)) (⊢lookup here))

_ : ∅ , "f" ⦂ ℕ̇ ⇒ ℕ̇ ⊢ λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇) ⦂ ℕ̇ ⇒ ℕ̇
_ = ⊢λ̇ (⊢· (⊢lookup (thereʳ here)) (⊢· (⊢lookup (thereʳ here)) (⊢lookup here)))

_ : ∅ ⊢ λ̇ "f" ⇒ λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇) ⦂ (ℕ̇ ⇒ ℕ̇) ⇒ ℕ̇ ⇒ ℕ̇
_ = ⊢λ̇ (⊢λ̇ (⊢· (⊢lookup (thereʳ here)) (⊢· (⊢lookup (thereʳ here)) (⊢lookup here))))

⊢ȯne : {Γ : Context}
    → Γ ⊢ ȯne ⦂ ℕ̇
⊢ȯne = ⊢ṡuc ⊢żero

⊢ṫwo : {Γ : Context}
    → Γ ⊢ ṫwo ⦂ ℕ̇
⊢ṫwo = ⊢ṡuc (⊢ṡuc ⊢żero)

⊢ṫhree : {Γ : Context}
    → Γ ⊢ ṫhree ⦂ ℕ̇
⊢ṫhree = ⊢ṡuc (⊢ṡuc (⊢ṡuc ⊢żero))

⊢ȧdd : {Γ : Context}
    → Γ ⊢ ȧdd ⦂ ℕ̇ ⇒ ℕ̇ ⇒ ℕ̇
⊢ȧdd = ⊢μ (⊢λ̇ (⊢λ̇ (⊢case
    (⊢lookup (thereʳ here))
    (⊢lookup here)
    (⊢ṡuc
        (⊢·
            (⊢·
                (⊢lookup (thereʳ (thereʳ (thereʳ here))))
                (⊢lookup here))
            (⊢lookup (thereʳ here)))))))

⊢2+2 : ∅ ⊢ ȧdd · ṫwo · ṫwo ⦂ ℕ̇
⊢2+2 = ⊢· (⊢· ⊢ȧdd ⊢ṫwo) ⊢ṫwo

Church : Type → Type
Church A = (A ⇒ A) ⇒ (A ⇒ A)

⊢ȯneᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ ȯneᶜ ⦂ Church A
⊢ȯneᶜ = ⊢λ̇ (⊢λ̇ (⊢· (⊢lookup (thereʳ here)) (⊢lookup here)))

⊢ṫwoᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ ṫwoᶜ ⦂ Church A
⊢ṫwoᶜ = ⊢λ̇ (⊢λ̇ (⊢· (⊢lookup (thereʳ here)) (⊢· (⊢lookup (thereʳ here)) (⊢lookup here))))

⊢ṫhreeᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ ṫhreeᶜ ⦂ Church A
⊢ṫhreeᶜ = ⊢λ̇ (⊢λ̇ (⊢· (⊢lookup (thereʳ here)) (⊢· (⊢lookup (thereʳ here)) (⊢· (⊢lookup (thereʳ here)) (⊢lookup here)))))

⊢ȧddᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ ȧddᶜ ⦂ Church A ⇒ Church A ⇒ Church A
⊢ȧddᶜ = ⊢λ̇ (⊢λ̇ (⊢λ̇ (⊢λ̇
    (⊢·
        (⊢·
            (⊢lookup (thereʳ (thereʳ (thereʳ here))))
            (⊢lookup (thereʳ here)))
        (⊢·
            (⊢·
                (⊢lookup (thereʳ (thereʳ here)))
                (⊢lookup (thereʳ here)))
            (⊢lookup here))))))

⊢λ̇ṡuc : {Γ : Context}
    → Γ ⊢ λ̇ṡuc ⦂ ℕ̇ ⇒ ℕ̇
⊢λ̇ṡuc = ⊢λ̇ (⊢ṡuc (⊢lookup here))

⊢2+2ᶜ : ∅ ⊢ ȧddᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero ⦂ ℕ̇
⊢2+2ᶜ = ⊢· (⊢· (⊢· (⊢· ⊢ȧddᶜ ⊢ṫwoᶜ) ⊢ṫwoᶜ) ⊢λ̇ṡuc) ⊢żero

lookup-injective : {Γ : Context} → {x y : Id} → {A B : Type}
    → Γ ∋ x ⦂ A → Γ ∋ y ⦂ B → x ≡ y → A ≡ B
lookup-injective here here p = refl
lookup-injective here (there g lookup2) refl = ⊥-elim (g refl)
lookup-injective (there f lookup1) here refl = ⊥-elim (f refl)
lookup-injective (there f lookup1) (there g lookup2) p = lookup-injective lookup1 lookup2 p

-- notable discovery: if we write
-- → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
-- instead, then the unification would fail if axiom-K is disabled, i.e., we cannot pattern match refl on x ≡ x

nope₁ : {A : Type} → ¬ (∅ ⊢ żero · ṡuc żero ⦂ A)
nope₁ (⊢· () _)

nope₂ : {A : Type} → ¬ (∅ ⊢ λ̇ "x" ⇒ "x"̇ · "x"̇ ⦂ A)
nope₂ (⊢λ̇ (⊢· (⊢lookup lookup1) (⊢lookup lookup2))) with lookup-injective lookup1 lookup2 refl
... | () -- (A ⇒ B) ≢ A

⊢ṁul : {Γ : Context}
    → Γ ⊢ ṁul ⦂ ℕ̇ ⇒ ℕ̇ ⇒ ℕ̇
⊢ṁul = ⊢μ (⊢λ̇ (⊢λ̇ (⊢case
    (⊢lookup (thereʳ here))
    ⊢żero
    (⊢·
        (⊢·
            ⊢ȧdd
            (⊢lookup (thereʳ here)))
        (⊢·
            (⊢·
                (⊢lookup (thereʳ (thereʳ (thereʳ here))))
                (⊢lookup here))
            (⊢lookup (thereʳ here)))))))

⊢ṁulᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ ṁulᶜ ⦂ Church A ⇒ Church A ⇒ Church A
⊢ṁulᶜ = ⊢λ̇ (⊢λ̇ (⊢λ̇ (⊢·
    (⊢lookup (thereʳ (thereʳ here)))
    (⊢·
        (⊢lookup (thereʳ here))
        (⊢lookup here)))))

⊢2*2 : ∅ ⊢ ṁul · ṫwo · ṫwo ⦂ ℕ̇
⊢2*2 = ⊢· (⊢· ⊢ṁul ⊢ṫwo) ⊢ṫwo

⊢2*2ᶜ : ∅ ⊢ ṁulᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero ⦂ ℕ̇
⊢2*2ᶜ = ⊢· (⊢· (⊢· (⊢· ⊢ṁulᶜ ⊢ṫwoᶜ) ⊢ṫwoᶜ) ⊢λ̇ṡuc) ⊢żero

⊢ėxp : {Γ : Context}
    → Γ ⊢ ėxp ⦂ ℕ̇ ⇒ ℕ̇ ⇒ ℕ̇
⊢ėxp = ⊢μ (⊢λ̇ (⊢λ̇ (⊢case
    (⊢lookup here)
    ⊢ȯne
    (⊢·
        (⊢·
            ⊢ṁul
            (⊢lookup (thereʳ (thereʳ here))))
        (⊢·
            (⊢·
                (⊢lookup (thereʳ (thereʳ (thereʳ here))))
                (⊢lookup (thereʳ (thereʳ here))))
            (⊢lookup here))))))

_ : {A : Type}
    → Church (A ⇒ A) ≡ Church A ⇒ Church A
_ = refl

⊢ėxpᶜ : {Γ : Context} → {A : Type}
    → Γ ⊢ ėxpᶜ ⦂ Church A ⇒ Church (A ⇒ A) ⇒ Church A
⊢ėxpᶜ = ⊢λ̇ (⊢λ̇ (⊢·
    (⊢lookup here)
    (⊢lookup (thereʳ here))))

⊢2^2 : ∅ ⊢ ėxp · ṫwo · ṫwo ⦂ ℕ̇
⊢2^2 = ⊢· (⊢· ⊢ėxp ⊢ṫwo) ⊢ṫwo

⊢2^2ᶜ : ∅ ⊢ ėxpᶜ · ṫwoᶜ · ṫwoᶜ · λ̇ṡuc · żero ⦂ ℕ̇
⊢2^2ᶜ = ⊢· (⊢· (⊢· (⊢· ⊢ėxpᶜ ⊢ṫwoᶜ) ⊢ṫwoᶜ) ⊢λ̇ṡuc) ⊢żero
