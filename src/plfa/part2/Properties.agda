{-# OPTIONS --without-K #-}

module plfa.part2.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (T; not)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)

open import plfa.part1.Isomorphism using (_≅_; _≲_)
open import plfa.part1.Connectives using (currying; _map-×_)
open import plfa.part2.Lambda

-- Values do not reduce

¬[value×reducible] : {t s : Term} → Value t → ¬ (t ⟶ s)
¬[value×reducible] (value-ṡuc value) (ξ-ṡuc reduction) = ¬[value×reducible] value reduction

¬[reducible×value] : {t s : Term} → t ⟶ s → ¬ Value t
¬[reducible×value] reduction value = ¬[value×reducible] value reduction

-- Canonical forms

infix 4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where
    C-λ̇ : {x : Id} → {t : Term} → {A B : Type}
        → ∅ , x ⦂ A ⊢ t ⦂ B
        → Canonical (λ̇ x ⇒ t) ⦂ (A →̇ B)
    C-żero : Canonical żero ⦂ ℕ̇
    C-ṡuc : {t : Term}
        → Canonical t ⦂ ℕ̇
        → Canonical (ṡuc t) ⦂ ℕ̇

typed×value→canonical : {t : Term} → {A : Type}
    → ∅ ⊢ t ⦂ A
    → Value t
    → Canonical t ⦂ A
typed×value→canonical (⊢λ̇ typing) value-λ̇ = C-λ̇ typing
typed×value→canonical ⊢żero value-żero = C-żero
typed×value→canonical (⊢ṡuc typing) (value-ṡuc value) = C-ṡuc (typed×value→canonical typing value)

canonical→typed : {t : Term} → {A : Type}
    → Canonical t ⦂ A
    → ∅ ⊢ t ⦂ A
canonical→typed (C-λ̇ typing) = ⊢λ̇ typing
canonical→typed C-żero = ⊢żero
canonical→typed (C-ṡuc canonical) = ⊢ṡuc (canonical→typed canonical)

canonical→value : {t : Term} → {A : Type}
    → Canonical t ⦂ A
    → Value t
canonical→value (C-λ̇ typing) = value-λ̇
canonical→value C-żero = value-żero
canonical→value (C-ṡuc canonical) = value-ṡuc (canonical→value canonical)

open _≅_

canonical≅typed×value : {t : Term} → {A : Type}
    → Canonical t ⦂ A ≅ ∅ ⊢ t ⦂ A × Value t
canonical≅typed×value .to canonical = (canonical→typed canonical) , canonical→value canonical
canonical≅typed×value .from = currying .to typed×value→canonical
canonical≅typed×value .from∘to (C-λ̇ typing) = refl
canonical≅typed×value .from∘to C-żero = refl
canonical≅typed×value .from∘to (C-ṡuc canonical) = cong C-ṡuc (canonical≅typed×value .from∘to canonical)
canonical≅typed×value .to∘from (⊢λ̇ typing , value-λ̇) = refl
canonical≅typed×value .to∘from (⊢żero , value-żero) = refl
canonical≅typed×value .to∘from (⊢ṡuc typing , value-ṡuc value) = cong (⊢ṡuc map-× value-ṡuc) (canonical≅typed×value .to∘from (typing , value))

-- Progress

data Progress (t : Term) : Set where
    step : {s : Term}
        → t ⟶ s
        → Progress t
    done : Value t
        → Progress t

progress : {t : Term} → {A : Type}
    → ∅ ⊢ t ⦂ A
    → Progress t
progress (⊢λ̇ typing) = done value-λ̇
progress (⊢· typing₁ typing₂) with progress typing₁
... | step reduction₁ = step (ξ-·₁ reduction₁)
... | done value₁ with progress typing₂
...     | step reduction₂ = step (ξ-·₂ value₁ reduction₂)
...     | done value₂ with typed×value→canonical typing₁ value₁
...         | C-λ̇ _ = step (β-λ̇ value₂)
progress ⊢żero = done value-żero
progress (⊢ṡuc typing) with progress typing
... | step reduction = step (ξ-ṡuc reduction)
... | done value = done (value-ṡuc value)
progress (⊢caseℕ̇ typing₁ typing₂ typing₃) with progress typing₁
... | step reduction = step (ξ-caseℕ̇ reduction)
... | done value₁ with typed×value→canonical typing₁ value₁
...     | C-żero = step β-żero
...     | C-ṡuc canonical = step (β-ṡuc (canonical→value canonical))
progress (⊢μ̇ typing) = step β-μ̇

progress-iso : (t : Term) → Progress t ≅ Value t ⊎ Σ Term (λ s → t ⟶ s)
progress-iso t .to (step {s} reduction) = inj₂ (s , reduction)
progress-iso t .to (done value) = inj₁ value
progress-iso t .from (inj₁ value) = done value
progress-iso t .from (inj₂ (s , reduction)) = step reduction
progress-iso t .from∘to (step reduction) = refl
progress-iso t .from∘to (done value) = refl
progress-iso t .to∘from (inj₁ value) = refl
progress-iso t .to∘from (inj₂ (s , reduction)) = refl

progress′ : {t : Term} → {A : Type}
    → ∅ ⊢ t ⦂ A
    → Value t ⊎ Σ Term (λ s → t ⟶ s)
progress′ (⊢λ̇ typing) = inj₁ value-λ̇
progress′ (⊢· {Γ} {t} {s} typing₁ typing₂) with progress′ typing₁
... | inj₁ value₁ with progress′ typing₂
...     | inj₁ value₂ with typing₁ | value₁
...         | ⊢λ̇ {x = x} {t = t′} typing₁′ | value-λ̇ = inj₂ (t′ [ x := s ] , β-λ̇ value₂)
progress′ (⊢· {Γ} {t} {s} typing₁ typing₂) | inj₁ value₁ | inj₂ (s′ , reduction₂) = inj₂ (t · s′ , ξ-·₂ value₁ reduction₂)
progress′ (⊢· {Γ} {t} {s} typing₁ typing₂) | inj₂ (t′ , reduction₁) = inj₂ (t′ · s , ξ-·₁ reduction₁)
progress′ ⊢żero = inj₁ value-żero
progress′ (⊢ṡuc typing) with progress′ typing
... | inj₁ value = inj₁ (value-ṡuc value)
... | inj₂ (s , reduction) = inj₂ (ṡuc s , ξ-ṡuc reduction)
progress′ (⊢caseℕ̇ {Γ} {x} {t} {s} {r} typing₁ typing₂ typing₃) with progress′ typing₁
... | inj₁ value₁ with typing₁ | value₁
...     | ⊢żero | value-żero = inj₂ (s , β-żero)
...     | ⊢ṡuc {t = t′} typing₁′ | value-ṡuc value₁′ = inj₂ (r [ x := t′ ] , β-ṡuc value₁′)
progress′ (⊢caseℕ̇ {Γ} {x} {t} {s} {r} typing₁ typing₂ typing₃) | inj₂ (t′ , reduction) = inj₂ (caseℕ̇ t′ [żero⇒ s |ṡuc x ⇒ r ] , ξ-caseℕ̇ reduction)
progress′ (⊢μ̇ {x = x} {t = t} typing) = inj₂ (t [ x := μ̇ x ⇒ t ] , β-μ̇)

value? : {t : Term} → {A : Type}
    → ∅ ⊢ t ⦂ A
    → Dec (Value t)
value? typing with progress typing
... | step reduction = no (¬[reducible×value] reduction)
... | done value = yes value

-- Perservation

-- Step 1: Renaming

extend : {Γ Δ : Context}
    → ({x : Id} → {A : Type} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A) -- ρ maps each variable (index) of type A in context Γ to a variable of type A in context Δ
    → ({x y : Id} → {A B : Type} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A) -- ρ lifts to a map (by shifting 1) from variables of type A in context Γ extended by B to variables of type A in context Δ extended by B
extend ρ here = here
extend ρ (there f lookup) = there f (ρ lookup)

reindex : {Γ Δ : Context}
    → ({x : Id} → {A : Type} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A) -- ρ maps each variable (index) of type A in context Γ to a variable of type A in context Δ
    → ({t : Term} → {A : Type} → Γ ⊢ t ⦂ A → Δ ⊢ t ⦂ A) -- ρ lifts to a map from terms of type A in context Γ to terms of type A in context Γ
reindex ρ (⊢lookup lookup) = ⊢lookup (ρ lookup)
reindex ρ (⊢λ̇ typing) = ⊢λ̇ (reindex (extend ρ) typing)
reindex ρ (⊢· typing₁ typing₂) = ⊢· (reindex ρ typing₁) (reindex ρ typing₂)
reindex ρ ⊢żero = ⊢żero
reindex ρ (⊢ṡuc typing) = ⊢ṡuc (reindex ρ typing)
reindex ρ (⊢caseℕ̇ typing₁ typing₂ typing₃) = ⊢caseℕ̇ (reindex ρ typing₁) (reindex ρ typing₂) (reindex (extend ρ) typing₃)
reindex ρ (⊢μ̇ typing) = ⊢μ̇ (reindex (extend ρ) typing)

typing₁ : ∅ , "f" ⦂ ℕ̇ →̇ ℕ̇ ⊢ λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇) ⦂ ℕ̇ →̇ ℕ̇
typing₁ = ⊢λ̇ (⊢· (⊢lookup (thereʳ here)) (⊢· (⊢lookup (thereʳ here)) (⊢lookup here)))

typing₂ : ∅ , "f" ⦂ ℕ̇ →̇ ℕ̇ , "y" ⦂ ℕ̇ ⊢ λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇) ⦂ ℕ̇ →̇ ℕ̇
typing₂ = ⊢λ̇ (⊢· (⊢lookup (thereʳ (thereʳ here))) (⊢· (⊢lookup (thereʳ (thereʳ here))) (⊢lookup here)))

_ : reindex (λ { here → thereʳ here }) typing₁ ≡ typing₂
_ = refl

weaken : {Γ : Context} → {t : Term} → {A : Type}
    → ∅ ⊢ t ⦂ A
    → Γ ⊢ t ⦂ A
weaken typing = reindex (λ ()) typing

drop : {Γ : Context} → {x : Id} → {t : Term} → {A B C : Type}
    → Γ , x ⦂ A , x ⦂ B ⊢ t ⦂ C
    → Γ , x ⦂ B ⊢ t ⦂ C
drop {Γ} {x} {t} {A} {B} {C} typing = reindex ρ typing where
    ρ : {z : Id} → {D : Type}
        → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ D
        → Γ , x ⦂ B ∋ z ⦂ D
    ρ here = here
    ρ (there f here) = ⊥-elim (f refl)
    ρ (there f (there g typing)) = there f typing

swap : {Γ : Context} → {x y : Id} → {t : Term} → {A B C : Type}
    → y ≢ x
    → Γ , x ⦂ A , y ⦂ B ⊢ t ⦂ C
    → Γ , y ⦂ B , x ⦂ A ⊢ t ⦂ C
swap {Γ} {x} {y} {t} {A} {B} {C} f typing = reindex ρ typing where
    ρ : {z : Id} → {D : Type}
        → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ D
        → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ D
    ρ here = there f here
    ρ (there g here) = here
    ρ (there g (there h lookup)) = there h (there g lookup)

-- Step 2: Substitution

substitute : {Γ : Context} → {x : Id} → {t s : Term} → {A B : Type}
    → Γ , x ⦂ A ⊢ t ⦂ B
    → ∅ ⊢ s ⦂ A
    → Γ ⊢ t [ x := s ] ⦂ B
substitute {x = x} (⊢lookup {x = .x} here) typing₂ with x ≟ x
... | no f = ⊥-elim (f refl)
... | yes p = weaken typing₂
substitute {x = x} (⊢lookup {x = y} (there f lookup)) typing₂ with y ≟ x
... | no _ = ⊢lookup lookup
... | yes refl = ⊥-elim (f refl)
substitute {x = x} (⊢λ̇ {x = y} typing₁) typing₂ with y ≟ x
... | no f = ⊢λ̇ (substitute (swap f typing₁) typing₂)
... | yes refl = ⊢λ̇ (drop typing₁)
substitute (⊢· typing₁ typing₂) typing₃ = ⊢· (substitute typing₁ typing₃) (substitute typing₂ typing₃)
substitute ⊢żero typing₂ = ⊢żero
substitute (⊢ṡuc typing₁) typing₂ = ⊢ṡuc (substitute typing₁ typing₂)
substitute {x = x} (⊢caseℕ̇ {x = y} typing₁ typing₂ typing₃) typing₄ with y ≟ x
... | no f = ⊢caseℕ̇ (substitute typing₁ typing₄) (substitute typing₂ typing₄) (substitute (swap f typing₃) typing₄)
... | yes refl = ⊢caseℕ̇ (substitute typing₁ typing₄) (substitute typing₂ typing₄) (drop typing₃)
substitute {x = x} (⊢μ̇ {x = y} typing₁) typing₂ with y ≟ x
... | no f = ⊢μ̇ (substitute (swap f typing₁) typing₂)
... | yes refl = ⊢μ̇ (drop typing₁)

substitute′-lemma : {Γ : Context} → {x y : Id} → {t s : Term} → {A B C : Type}
    → Γ , x ⦂ A , y ⦂ B ⊢ t ⦂ C
    → ∅ ⊢ s ⦂ A
    → Γ , y ⦂ B ⊢ t [ y ≟ x := s ]″ ⦂ C
substitute′ : {Γ : Context} → {x : Id} → {t s : Term} → {A B : Type}
    → Γ , x ⦂ A ⊢ t ⦂ B
    → ∅ ⊢ s ⦂ A
    → Γ ⊢ t [ x := s ]′ ⦂ B

substitute′-lemma {x = x} {y = y} typing₁ typing₂ with y ≟ x
... | no f = substitute′ (swap f typing₁) typing₂
... | yes refl = drop typing₁

substitute′ {x = x} (⊢lookup {x = .x} here) typing₂ with x ≟ x
... | no f = ⊥-elim (f refl)
... | yes p = weaken typing₂
substitute′ {x = x} (⊢lookup {x = y} (there f lookup)) typing₂ with y ≟ x
... | no _ = ⊢lookup lookup
... | yes refl = ⊥-elim (f refl)
substitute′ (⊢λ̇ typing₁) typing₂ = ⊢λ̇ (substitute′-lemma typing₁ typing₂)
substitute′ (⊢· typing₁ typing₂) typing₃ = ⊢· (substitute′ typing₁ typing₃) (substitute′ typing₂ typing₃)
substitute′ ⊢żero typing₂ = ⊢żero
substitute′ (⊢ṡuc typing₁) typing₂ = ⊢ṡuc (substitute′ typing₁ typing₂)
substitute′ (⊢caseℕ̇ typing₁ typing₂ typing₃) typing₄ = ⊢caseℕ̇ (substitute′ typing₁ typing₄) (substitute′ typing₂ typing₄) (substitute′-lemma typing₃ typing₄)
substitute′ (⊢μ̇ typing₁) typing₂ = ⊢μ̇ (substitute′-lemma typing₁ typing₂)

-- Step 3: Perservation

perserve : {t s : Term} → {A : Type}
    → ∅ ⊢ t ⦂ A
    → t ⟶ s
    → ∅ ⊢ s ⦂ A
perserve (⊢· typing₁ typing₂) (ξ-·₁ reduction₁) = ⊢· (perserve typing₁ reduction₁) typing₂
perserve (⊢· typing₁ typing₂) (ξ-·₂ value reduction₂) = ⊢· typing₁ (perserve typing₂ reduction₂)
perserve (⊢· (⊢λ̇ typing₁) typing₂) (β-λ̇ value) = substitute typing₁ typing₂
perserve (⊢ṡuc typing) (ξ-ṡuc reduction) = ⊢ṡuc (perserve typing reduction)
perserve (⊢caseℕ̇ typing₁ typing₂ typing₃) (ξ-caseℕ̇ reduction₁) = ⊢caseℕ̇ (perserve typing₁ reduction₁) typing₂ typing₃
perserve (⊢caseℕ̇ ⊢żero typing₂ typing₃) β-żero = typing₂
perserve (⊢caseℕ̇ (⊢ṡuc typing₁) typing₂ typing₃) (β-ṡuc value) = substitute typing₃ typing₁
perserve (⊢μ̇ typing) β-μ̇ = substitute typing (⊢μ̇ typing)

-- Evaluation

-- infinite loop

μ̇ṡuc : Term
μ̇ṡuc = μ̇ "x" ⇒ ṡuc "x"̇

_ : μ̇ṡuc ⟶⋆ ṡuc (ṡuc (ṡuc μ̇ṡuc))
_ =
    begin
        μ̇ṡuc ⟶⟨ β-μ̇ ⟩
        ṡuc μ̇ṡuc ⟶⟨ ξ-ṡuc β-μ̇ ⟩
        ṡuc ṡuc μ̇ṡuc ⟶⟨ ξ-ṡuc (ξ-ṡuc β-μ̇) ⟩
        ṡuc ṡuc ṡuc μ̇ṡuc --  ...
    ∎

-- in order to limit the unboundedness of evaluation steps
-- we introduce a natural number to put a bound on evaluation

record Gas : Set where
    constructor gas
    field
        amount : ℕ

data Finished (t : Term) : Set where
    done : Value t → Finished t
    out-of-gas : Finished t

Finished≅MaybeValue : {t : Term} → Finished t ≅ Maybe (Value t)
Finished≅MaybeValue .to (done value) = just value
Finished≅MaybeValue .to out-of-gas = nothing
Finished≅MaybeValue .from nothing = out-of-gas
Finished≅MaybeValue .from (just value) = done value
Finished≅MaybeValue .from∘to (done value) = refl
Finished≅MaybeValue .from∘to out-of-gas = refl
Finished≅MaybeValue .to∘from nothing = refl
Finished≅MaybeValue .to∘from (just value) = refl

data Steps (t : Term) : Set where
    steps : {s : Term} → t ⟶⋆ s → Finished s → Steps t

Steps-iso : {t : Term} → Steps t ≅ Σ Term (λ s → (t ⟶⋆ s) × Finished s)
Steps-iso .to (steps {s} reductions finished) = s , reductions , finished
Steps-iso .from (s , reductions , finished) = steps reductions finished
Steps-iso .from∘to (steps _ _) = refl
Steps-iso .to∘from (_ , _ , _) = refl

eval : {t : Term} → {A : Type}
    → Gas
    → ∅ ⊢ t ⦂ A
    → Steps t
eval {t} (gas zero) typing = steps (t ∎) out-of-gas
eval {t} (gas (suc n)) typing with progress typing
... | done value = steps (t ∎) (done value)
... | step {s} reduction with eval (gas n) (perserve typing reduction)
...     | steps reductions finished = steps (t ⟶⟨ reduction ⟩ reductions) finished

⊢μ̇ṡuc : ∅ ⊢ μ̇ṡuc ⦂ ℕ̇
⊢μ̇ṡuc = ⊢μ̇ (⊢ṡuc (⊢lookup here))

_ : eval (gas 3) ⊢μ̇ṡuc ≡ steps
    (-- begin
            μ̇ "x" ⇒ ṡuc "x"̇
        ⟶⟨ β-μ̇ ⟩
            ṡuc (μ̇ "x" ⇒ ṡuc "x"̇)
        ⟶⟨ ξ-ṡuc β-μ̇ ⟩
            ṡuc (ṡuc (μ̇ "x" ⇒ ṡuc "x"̇))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc β-μ̇) ⟩
            ṡuc (ṡuc (ṡuc (μ̇ "x" ⇒ ṡuc "x"̇)))
        ∎)
    out-of-gas
_ = refl

_ : eval (gas 100) (⊢· (⊢· ⊢ṫwoᶜ ⊢λ̇ṡuc) ⊢żero) ≡ steps
    (-- begin
            (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · żero
        ⟶⟨ β-λ̇ value-żero ⟩
            (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
            (λ̇ "n" ⇒ ṡuc "n"̇) · ṡuc żero
        ⟶⟨ β-λ̇ (value-ṡuc value-żero) ⟩
            ṡuc (ṡuc żero)
        ∎)
    (done (value-ṡuc (value-ṡuc value-żero)))
_ = refl

_ : eval (gas 13) ⊢2+2 ≡ steps
    (-- begin
            (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
        ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
            (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
        ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            caseℕ̇ ṡuc (ṡuc żero) [żero⇒ ṡuc (ṡuc żero) |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ]
        ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
            ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
            ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
            ṡuc ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            ṡuc caseℕ̇ ṡuc żero [żero⇒ ṡuc (ṡuc żero) |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ]
        ⟶⟨ ξ-ṡuc (β-ṡuc value-żero) ⟩
            ṡuc (ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
            ṡuc (ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
            ṡuc (ṡuc ((λ̇ "m" ⇒ caseℕ̇ żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
            ṡuc (ṡuc caseℕ̇ żero [żero⇒ ṡuc (ṡuc żero) |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ])
        ⟶⟨ ξ-ṡuc (ξ-ṡuc β-żero) ⟩
            ṡuc (ṡuc (ṡuc (ṡuc żero)))
        ∎)
    (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
_ = refl

_ : eval (gas 13) ⊢2+2ᶜ ≡ steps
    (-- begin
            (λ̇ "n" ⇒ (λ̇ "m" ⇒ (λ̇ "f" ⇒ (λ̇ "x" ⇒ "n"̇ · "f"̇ · ("m"̇ · "f"̇ · "x"̇))))) · (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇))) ⟩
            (λ̇ "m" ⇒ (λ̇ "f" ⇒ (λ̇ "x" ⇒ (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · "f"̇ · ("m"̇ · "f"̇ · "x"̇)))) · (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
            (λ̇ "f" ⇒ (λ̇ "x" ⇒ (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · "f"̇ · ((λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · "f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ "x" ⇒ (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · żero
        ⟶⟨ β-λ̇ value-żero ⟩
            (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · żero)
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · ((λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · ((λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · ((λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · ((λ̇ "n" ⇒ ṡuc "n"̇) · ṡuc żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ "n" ⇒ ṡuc "n"̇) · ṡuc (ṡuc (ṡuc żero))
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc (value-ṡuc value-żero))) ⟩
            ṡuc (ṡuc (ṡuc (ṡuc żero)))
        ∎)
    (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
_ = refl

_ : eval (gas 37) ⊢2*2 ≡ steps
    (-- begin
            (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
        ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
            (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
        ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ]
        ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
            (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
            (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ ṡuc żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ]
        ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-żero))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ])
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · żero) ]
        ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc (value-ṡuc value-żero)) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc żero · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ value-żero)) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc caseℕ̇ ṡuc żero [żero⇒ żero |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · żero) ]
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-ṡuc value-żero)) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · żero · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · żero · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero)))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc ((λ̇ "m" ⇒ caseℕ̇ żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (β-λ̇ value-żero))) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc caseℕ̇ żero [żero⇒ żero |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · żero) ])
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc β-żero)) ⟩
            (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            caseℕ̇ ṡuc (ṡuc żero) [żero⇒ ṡuc (ṡuc żero) |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ]
        ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
            ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
            ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc żero · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
            ṡuc ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            ṡuc caseℕ̇ ṡuc żero [żero⇒ ṡuc (ṡuc żero) |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ]
        ⟶⟨ ξ-ṡuc (β-ṡuc value-żero) ⟩
            ṡuc (ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
            ṡuc (ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · żero · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
            ṡuc (ṡuc ((λ̇ "m" ⇒ caseℕ̇ żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero)))
        ⟶⟨ ξ-ṡuc (ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
            ṡuc (ṡuc caseℕ̇ żero [żero⇒ ṡuc (ṡuc żero) |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ])
        ⟶⟨ ξ-ṡuc (ξ-ṡuc β-żero) ⟩
            ṡuc (ṡuc (ṡuc (ṡuc żero)))
        ∎)
    (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
_ = refl

_ : eval (gas 13) ⊢2*2ᶜ ≡ steps
    (-- begin
            (λ̇ "n" ⇒ (λ̇ "m" ⇒ (λ̇ "f" ⇒ "n"̇ · ("m"̇ · "f"̇)))) · (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇)))· (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇)))· (λ̇ "n" ⇒ ṡuc "n"̇)· żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇))) ⟩
            (λ̇ "m" ⇒ (λ̇ "f" ⇒ (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · ("m"̇ · "f"̇)))· (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇)))· (λ̇ "n" ⇒ ṡuc "n"̇)· żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
            (λ̇ "f" ⇒ (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · ((λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · "f"̇))· (λ̇ "n" ⇒ ṡuc "n"̇)· żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · ((λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇))· żero
        ⟶⟨ ξ-·₁ (ξ-·₂ value-λ̇ (β-λ̇ value-λ̇)) ⟩
            (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇))· żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ "x" ⇒ (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇))· ((λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇))· "x"̇))· żero
        ⟶⟨ β-λ̇ value-żero ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇))· ((λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇))· żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇))· ((λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇))· ((λ̇ "n" ⇒ ṡuc "n"̇) · ṡuc żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇))· ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ "n" ⇒ ṡuc "n"̇) · ṡuc (ṡuc (ṡuc żero))
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc (value-ṡuc value-żero))) ⟩
            ṡuc (ṡuc (ṡuc (ṡuc żero)))
        ∎)
    (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
_ = refl

-- _ : eval (gas 77) ⊢2^2 ≡ steps
--     (-- begin
--             (μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
--         ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
--             (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc (ṡuc żero) · ṡuc (ṡuc żero)
--         ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · "m"̇) ]) · ṡuc (ṡuc żero)
--         ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
--             caseℕ̇ ṡuc (ṡuc żero) [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · "m"̇) ]
--         ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
--             (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
--             (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc (ṡuc żero) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc (ṡuc żero) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · "m"̇) ]) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ ṡuc żero [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · "m"̇) ]
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc (ṡuc żero) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc (ṡuc żero) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · "m"̇) ]) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ żero [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "^" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "m"̇ [żero⇒ ṡuc żero |ṡuc "m" ⇒ (μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ("^"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · "m"̇) ])
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc żero) ]
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc (value-ṡuc value-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc żero · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc żero · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ ṡuc żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc żero) ])
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-ṡuc value-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc żero · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · żero · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-żero)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc żero) ]))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ ṡuc żero [żero⇒ żero |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · żero) ])
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-ṡuc value-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((λ̇ "m" ⇒ caseℕ̇ żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc caseℕ̇ żero [żero⇒ żero |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · żero) ])
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-ṡuc β-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ ṡuc żero [żero⇒ ṡuc żero |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc żero) ]
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · żero · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((λ̇ "m" ⇒ caseℕ̇ żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc caseℕ̇ żero [żero⇒ ṡuc żero |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc żero) ]
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc β-żero) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero)
--         ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
--             caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ]
--         ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
--             (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₁ (ξ-·₁ β-μ̇) ⟩
--             (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ ṡuc żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ]
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc value-żero) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (ξ-·₁ (β-λ̇ value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ żero [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc (ṡuc żero) · ((μ̇ "*" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ żero |ṡuc "n" ⇒ (μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "m"̇ · ("*"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ])
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ β-żero) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ((λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · caseℕ̇ ṡuc (ṡuc żero) [żero⇒ żero |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · żero) ]
--         ⟶⟨ ξ-·₂ value-λ̇ (β-ṡuc (value-ṡuc value-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc żero · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · żero)
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-λ̇ value-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc caseℕ̇ ṡuc żero [żero⇒ żero |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · żero) ]
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (β-ṡuc value-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · żero · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero)))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc ((λ̇ "m" ⇒ caseℕ̇ żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · żero))
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc (β-λ̇ value-żero))) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc caseℕ̇ żero [żero⇒ żero |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · żero) ])
--         ⟶⟨ ξ-·₂ value-λ̇ (ξ-ṡuc (ξ-ṡuc β-żero)) ⟩
--             (λ̇ "m" ⇒ caseℕ̇ ṡuc (ṡuc żero) [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero)
--         ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
--             caseℕ̇ ṡuc (ṡuc żero) [żero⇒ ṡuc (ṡuc żero) |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ]
--         ⟶⟨ β-ṡuc (value-ṡuc value-żero) ⟩
--             ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇)) ⟩
--             ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · ṡuc żero · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (ξ-·₁ (β-λ̇ (value-ṡuc value-żero))) ⟩
--             ṡuc ((λ̇ "m" ⇒ caseℕ̇ ṡuc żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero))
--         ⟶⟨ ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
--             ṡuc caseℕ̇ ṡuc żero [żero⇒ ṡuc (ṡuc żero) |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ]
--         ⟶⟨ ξ-ṡuc (β-ṡuc value-żero) ⟩
--             ṡuc (ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (ξ-·₁ β-μ̇))) ⟩
--             ṡuc (ṡuc ((λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ])) · żero · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (ξ-·₁ (β-λ̇ value-żero))) ⟩
--             ṡuc (ṡuc ((λ̇ "m" ⇒ caseℕ̇ żero [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · "m"̇) ]) · ṡuc (ṡuc żero)))
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc (β-λ̇ (value-ṡuc (value-ṡuc value-żero)))) ⟩
--             ṡuc (ṡuc caseℕ̇ żero [żero⇒ ṡuc (ṡuc żero) |ṡuc "n" ⇒ ṡuc ((μ̇ "+" ⇒ (λ̇ "n" ⇒ (λ̇ "m" ⇒ caseℕ̇ "n"̇ [żero⇒ "m"̇ |ṡuc "n" ⇒ ṡuc ("+"̇ · "n"̇ · "m"̇) ]))) · "n"̇ · ṡuc (ṡuc żero)) ])
--         ⟶⟨ ξ-ṡuc (ξ-ṡuc β-żero) ⟩
--             ṡuc (ṡuc (ṡuc (ṡuc żero)))
--         ∎)
--     (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
-- _ = refl

_ : eval (gas 14) ⊢2^2ᶜ ≡ steps
    (-- begin
            (λ̇ "n" ⇒ (λ̇ "m" ⇒ "m"̇ · "n"̇)) · (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇))) ⟩
            (λ̇ "m" ⇒ "m"̇ · (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇)))) · (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
            (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇) · żero
        ⟶⟨ ξ-·₁ (ξ-·₁ (β-λ̇ value-λ̇)) ⟩
            (λ̇ "x" ⇒ (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · ((λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · "x"̇)) · (λ̇ "n" ⇒ ṡuc "n"̇) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · ((λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "n" ⇒ ṡuc "n"̇)) · żero
        ⟶⟨ ξ-·₁ (ξ-·₂ value-λ̇ (β-λ̇ value-λ̇)) ⟩
            (λ̇ "f" ⇒ (λ̇ "x" ⇒ "f"̇ · ("f"̇ · "x"̇))) · (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · żero
        ⟶⟨ ξ-·₁ (β-λ̇ value-λ̇) ⟩
            (λ̇ "x" ⇒ (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · ((λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · "x"̇)) · żero
        ⟶⟨ β-λ̇ value-żero ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · ((λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ value-żero) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · ((λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · żero))
        ⟶⟨ ξ-·₂ value-λ̇ (ξ-·₂ value-λ̇ (β-λ̇ value-żero)) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · ((λ̇ "n" ⇒ ṡuc "n"̇) · ṡuc żero)
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc value-żero)) ⟩
            (λ̇ "x" ⇒ (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · "x"̇)) · ṡuc (ṡuc żero)
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc value-żero)) ⟩
            (λ̇ "n" ⇒ ṡuc "n"̇) · ((λ̇ "n" ⇒ ṡuc "n"̇) · ṡuc (ṡuc żero))
        ⟶⟨ ξ-·₂ value-λ̇ (β-λ̇ (value-ṡuc (value-ṡuc value-żero))) ⟩
            (λ̇ "n" ⇒ ṡuc "n"̇) · ṡuc (ṡuc (ṡuc żero))
        ⟶⟨ β-λ̇ (value-ṡuc (value-ṡuc (value-ṡuc value-żero))) ⟩
            ṡuc (ṡuc (ṡuc (ṡuc żero)))
        ∎)
    (done (value-ṡuc (value-ṡuc (value-ṡuc (value-ṡuc value-żero)))))
_ = refl

-- The converse of perservation does not hold:

_ : Σ Term λ t → Σ Term λ s → Σ Type λ A → ((t ⟶ s) × ∅ ⊢ s ⦂ A × ¬ ∅ ⊢ t ⦂ A)
_ = caseℕ̇ żero [żero⇒ żero |ṡuc "n" ⇒ λ̇ "x" ⇒ "x"̇ ] , żero , ℕ̇ , β-żero , ⊢żero , f where
    f : ∅ ⊢ caseℕ̇ żero [żero⇒ żero |ṡuc "n" ⇒ λ̇ "x" ⇒ "x"̇ ] ⦂ ℕ̇ → ⊥
    f (⊢caseℕ̇ typing₁ typing₂ ())

_ : Σ Term λ t → Σ Term λ s → Σ Type λ A → ((t ⟶ s) × ∅ ⊢ s ⦂ A × ¬ ∅ ⊢ t ⦂ A)
_ = (λ̇ "f" ⇒ żero) · (λ̇ "x" ⇒ "x"̇ · "x"̇) , żero , ℕ̇ , β-λ̇ value-λ̇ , ⊢żero , f where
    f : ∅ ⊢ (λ̇ "f" ⇒ żero) · (λ̇ "x" ⇒ "x"̇ · "x"̇) ⦂ ℕ̇ → ⊥
    f (⊢· typing₁ typing₂) = nope₂ typing₂

Normal : Term → Set
Normal t = {s : Term} → ¬ (t ⟶ s)

Stuck : Term → Set
Stuck t = Normal t × ¬ Value t

-- example of term getting stuck:

_ : Σ Term Stuck
_ = żero · żero , normal , f where
    normal : {s : Term} → ¬ (żero · żero ⟶ s)
    normal (ξ-·₁ ())
    normal (ξ-·₂ value-żero ())
    f : ¬ Value (żero · żero)
    f ()

Progress→¬Stuck : {t : Term}
    → Progress t → ¬ (Stuck t)
Progress→¬Stuck (step reduction) (normal , f) = normal reduction
Progress→¬Stuck (done value) (normal , f) = f value

unstuck : {t : Term} → {A : Type}
    → ∅ ⊢ t ⦂ A
    → ¬ (Stuck t) -- this is just a weaker version of progress′
unstuck typing = Progress→¬Stuck (progress typing)

preserves : {t s : Term} → {A : Type}
    → ∅ ⊢ t ⦂ A
    → t ⟶⋆ s
    → ∅ ⊢ s ⦂ A
preserves typing (_ ∎) = typing
preserves typing (_ ⟶⟨ reduction ⟩ reductions) = preserves (perserve typing reduction) reductions

wttdgs : {t s : Term} → {A : Type}
    → ∅ ⊢ t ⦂ A
    → t ⟶⋆ s
    → ¬ (Stuck s)
wttdgs typing reductions = unstuck (preserves typing reductions)

determinism : {t s r : Term}
    → t ⟶ s → t ⟶ r
    → s ≡ r
determinism (β-λ̇ value₁) (β-λ̇ value₂) = refl
determinism (β-λ̇ value₁) (ξ-·₂ value₂ reduction₂) = ⊥-elim (¬[value×reducible] value₁ reduction₂)
determinism β-żero β-żero = refl
determinism (β-ṡuc value₁) (β-ṡuc value₂) = refl
determinism (β-ṡuc value₁) (ξ-caseℕ̇ reduction₂) = ⊥-elim (¬[value×reducible] (value-ṡuc value₁) reduction₂)
determinism β-μ̇ β-μ̇ = refl
determinism (ξ-·₁ {s = s} reduction₁) (ξ-·₁ reduction₂) = cong (_· s) (determinism reduction₁ reduction₂)
determinism (ξ-·₁ reduction₁) (ξ-·₂ value₂ reduction₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-·₂ value₁ reduction₁) (β-λ̇ value₂) = ⊥-elim (¬[value×reducible] value₂ reduction₁)
determinism (ξ-·₂ value₁ reduction₁) (ξ-·₁ reduction₂) = ⊥-elim (¬[value×reducible] value₁ reduction₂)
determinism (ξ-·₂ {t = t} value₁ reduction₁) (ξ-·₂ value₂ reduction₂) = cong (t ·_) (determinism reduction₁ reduction₂)
determinism (ξ-caseℕ̇ reduction₁) (β-ṡuc value₂) = ⊥-elim (¬[value×reducible] (value-ṡuc value₂) reduction₁)
determinism (ξ-ṡuc reduction₁) (ξ-ṡuc reduction₂) = cong ṡuc_ (determinism reduction₁ reduction₂)
determinism (ξ-caseℕ̇ {x = x} {s = s} {r = r} reduction₁) (ξ-caseℕ̇ reduction₂) = cong caseℕ̇_[żero⇒ s |ṡuc x ⇒ r ] (determinism reduction₁ reduction₂)

-- Quiz 1
-- add the following:
-- zap : Term
-- β-zap : {t : Term} → t ⟶ zap
-- ⊢zap : {Γ : Context} → {A : Type} → Γ ⊢ zap ⦂ A
-- then:
-- determinism does not hold, counter-example: λ̇ṡuc · żero ⟶ ṡuc żero / zap
-- progress holds (if zap is a value)
-- perservation holds

-- Quiz 2
-- add the following:
-- foo : Term
-- β-foo₁ : {x : Id} → (λ̇ x ⇒ x ̇) ⟶ foo
-- β-foo₂ : foo ⟶ żero
-- then:
-- determinism does not hold, counter-example: (λ̇ x ⇒ x ̇) · żero ⟶ żero / foo · żero
-- progress does not hold, counter-example: (λ̇ x ⇒ x ̇) · żero ⟶ foo · żero ⟶ żero · żero (stuck)
-- perservation does not hold, counter-example: (λ̇ x ⇒ x ̇) ⟶ foo ⟶ żero

-- Quiz 3
-- remove ξ-·₁
-- then:
-- determinism holds
-- progress does not hold, counter-example: (ṫwoᶜ · λ̇ṡuc) · żero is stuck
-- perservation holds

-- Quiz 4
-- let f_i denote the enumeration of all computable function ℕ̇ →̇ ℕ̇ (partial recursive function)
-- could be implemented by lexicographic order (picking one from alpha-equivalent class of terms, or just all terms, or using de Bruijn indices)
-- note i : ℕ is in the meta theory, i.e., f : ℕ → Term, (i : ℕ) → ∅ ⊢ f i ⦂ ℕ̇ →̇ ℕ̇, (t : Term) → ∅ ⊢ t ⦂ ℕ̇ →̇ ℕ̇ → Σ ℕ (λ i → t ≡ f i)
-- or equivalently Σ Term (λ t → ∅ ⊢ t ⦂ ℕ̇ →̇ ℕ̇) ≲ ℕ
-- or actually ℕ ≅ Σ Term (λ t → ∅ ⊢ t ⦂ ℕ̇ →̇ ℕ̇), to = f, from = g, g (f i) ≡ i, f (g t) ≡ t, since ℕ̇ →̇ ℕ̇ must be infinite
-- add the following, where natural 0 = żero, natural :
-- ⊢·ℕ̇ : {Γ : Context} → {t s : Term}
--     → Γ ⊢ t ⦂ ℕ̇
--     → Γ ⊢ s ⦂ ℕ̇
--     → Γ ⊢ (t · s) ⦂ ℕ̇
-- δ : {i : ℕ} → {t s : Term}
--     → (f i) · t ⟶ s -- note here ∅ ⊢ f i ⦂ ℕ̇ →̇ ℕ̇
--     → (natural i) · t ⟶ s
-- then:
-- determinism holds
-- progress does not hold, since a computable function might not halt on some inputs, leaving (f i) · t stuck
-- perservation holds
-- Are there any other alterations we would wish to make to the system?
-- support general computable functions: ℕ̇ →̇ ℕ̇ →̇ ... →̇ ℕ̇ (ℕ̇ⁿ →̇ ℕ̇)
 