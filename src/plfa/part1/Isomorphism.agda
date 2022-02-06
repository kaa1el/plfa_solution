{-# OPTIONS --without-K #-}

module plfa.part1.Isomorphism where

open import Agda.Primitive

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Relation.Nullary using (¬_; Dec; yes; no)
-- open import Tactic.Cong using (cong!)

open import plfa.part1.Equality using (cong-app; cong-app-d; subst-trans; subst-cong; subst₂-d; subst₂-d-const; cong-d; cong₂-d; trans-identity-l; trans-identity-r; trans-sym-l; trans-sym-r; trans-assoc; cong-cong; cong-id; subst-eq-r; subst-refl-l; homotopy-natural-variation)

private
    variable
        i j k l : Level

-- Lambda Expressions

test : ℕ → ℕ
test zero = 0
test (suc x) = 1

test2 : ℕ → ℕ
test2 = λ { zero → 1; (suc x) → 2 }

test3 : ℕ → ℕ
test3 = λ where
    zero → 1
    (suc x) → 2

_ : (λ (x : ℕ) → x) ≡ (λ (x : ℕ) → x)
_ = refl

-- _ : (λ {x → x}) ≡ (λ {x → x})
-- _ = refl

-- _ : (λ {zero → 1; (suc x) → 2}) ≡ (λ {zero → 1; (suc x) → 2})
-- _ = refl

-- Function Composition

_∘_ : {A : Set i} → {B : Set j} → {C : Set k} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

_∘′_ : {A : Set i} → {B : Set j} → {C : Set k} → (B → C) → (A → B) → (A → C)
g ∘′ f = λ x → g (f x)

-- Extensionality

postulate
    extensionality : {A : Set i} → {B : Set j} → {f g : A → B}
        → ((x : A) → f x ≡ g x) → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ suc n = suc (m +′ n)

same-app : (m n : ℕ) → m +′ n ≡ m + n
same-app m zero rewrite +-comm m zero = refl
same-app m (suc n)
    rewrite +-comm m (suc n)
    | same-app m n
    | +-comm m n = refl

extensionality₂ : {A : Set i} → {B : Set j} → {C : Set k} → {f g : A → B → C}
    → ((x : A) → (y : B) → f x y ≡ g x y) → f ≡ g
extensionality₂ p = extensionality (λ x → extensionality (λ y → p x y))

same : _+′_ ≡ _+_
same = extensionality₂ same-app

postulate
    Π-extensionality : {A : Set i} → {B : A → Set j} → {f g : (x : A) → B x}
        → ((x : A) → f x ≡ g x) → f ≡ g -- HoTT Book Exercise 4.9, i.e., the dependent function extensionality can be proved from the non-dependent one
-- Π-extensionality p = ? -- TODO

Π-extensionality₂ : {A : Set i} → {B : A → Set j} → {C : (x : A) → B x → Set k} → {f g : (x : A) → (y : B x) → C x y}
    → ((x : A) → (y : B x) → f x y ≡ g x y) → f ≡ g
Π-extensionality₂ p = Π-extensionality (λ x → Π-extensionality (λ y → p x y))

infix 0 _≅_

record _≅_ (A : Set i) (B : Set j) : Set (i ⊔ j) where
    field
        to : A → B -- the functor f
        from : B → A -- the inverse g
        from∘to : (x : A) → from (to x) ≡ x -- the inverse of unit (sym η)
        to∘from : (y : B) → to (from y) ≡ y -- the counit ε

open _≅_ -- this opens the fields declared in the record

data _≅′_ (A : Set i) (B : Set j) : Set (i ⊔ j) where
    mk-≅′ : (to : A → B) → (from : B → A)
        → (from∘to : (x : A) → from (to x) ≡ x)
        → (to∘from : (y : B) → to (from y) ≡ y)
        → A ≅′ B

to′ : {A : Set i} → {B : Set j} → (A ≅′ B) → (A → B)
to′ (mk-≅′ f g g∘f f∘g) = f

from′ : {A : Set i} → {B : Set j} → (A ≅′ B) → (B → A)
from′ (mk-≅′ f g g∘f f∘g) = g

from∘to′ : {A : Set i} → {B : Set j} → (A≅B : A ≅′ B) → ((x : A) → from′ A≅B (to′ A≅B x) ≡ x)
from∘to′ (mk-≅′ f g g∘f f∘g) = g∘f

to∘from′ : {A : Set i} → {B : Set j} → (A≅B : A ≅′ B) → ((y : B) → to′ A≅B (from′ A≅B y) ≡ y)
to∘from′ (mk-≅′ f g g∘f f∘g) = f∘g

≅-refl : {A : Set i} → A ≅ A
≅-refl =
    record {
        to = λ {x → x};
        from = λ {y → y};
        from∘to = λ {x → refl};
        to∘from = λ {y → refl}
    }

≅-sym : {A : Set i} → {B : Set j} → A ≅ B → B ≅ A
≅-sym A≅B =
    record {
        to = from A≅B;
        from = to A≅B;
        from∘to = to∘from A≅B;
        to∘from = from∘to A≅B
    }

≅-trans : {A : Set i} → {B : Set j} → {C : Set k} → A ≅ B → B ≅ C → A ≅ C
≅-trans A≅B B≅C =
    record {
        to = to B≅C ∘ to A≅B;
        from = from A≅B ∘ from B≅C;
        from∘to = λ x → trans (cong (from A≅B) (from∘to B≅C (to A≅B x))) (from∘to A≅B x);
        to∘from = λ y → trans (cong (to B≅C) (to∘from A≅B (from B≅C y))) (to∘from B≅C y)
    }

module ≅-Reasoning where

    infix 1 begin≅_
    infixr 2 _≅⟨⟩_ _≅⟨_⟩_
    infix 3 _≅∎

    begin≅_ : {A : Set i} → {B : Set j} → A ≅ B → A ≅ B
    begin≅ A≅B = A≅B

    _≅⟨⟩_ : (A : Set i) → {B : Set j} → A ≅ B → A ≅ B
    A ≅⟨⟩ A≅B = A≅B

    _≅⟨_⟩_ : (A : Set i) → {B : Set j} → {C : Set k} → A ≅ B → B ≅ C → A ≅ C
    A ≅⟨ A≅B ⟩ B≅C = ≅-trans A≅B B≅C

    _≅∎ : (A : Set i) → A ≅ A
    A ≅∎ = ≅-refl

open ≅-Reasoning

-- Embedding

record _≲_ (A : Set i) (B : Set j) : Set (i ⊔ j) where -- A is a retract of B
    field
        to : A → B -- section of from
        from : B → A -- retraction of to
        from∘to : (x : A) → from (to x) ≡ x
infix 0 _≲_
open _≲_

id : {A : Set i} → A → A
id x = x

≲-refl : {A : Set i} → A ≲ A
to ≲-refl = id -- copattern matching, put cursor in the hole, hit C-c C-c then hit enter, i.e., case split on the right side
from ≲-refl = id
from∘to ≲-refl x = refl -- can also combine copattern matching with pattern matching

≲-trans : {A : Set i} → {B : Set j} → {C : Set k} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C .to = B≲C .to ∘ A≲B .to -- copattern matching, here we changed to suffix notation (prefix), default is prefix
≲-trans A≲B B≲C .from = A≲B .from ∘ B≲C .from
≲-trans A≲B B≲C .from∘to x -- can also combine with rewrite and with
    rewrite B≲C .from∘to (A≲B .to x)
    | A≲B .from∘to x = refl

≲-refl′ : {A : Set i} → A ≲ A
≲-refl′ = λ { .to → id; .from → id; .from∘to → λ x → refl } -- copattern matching can also use lambda abstraction, but must be in suffix notation

≲-refl″ : {A : Set i} → A ≲ A
≲-refl″ = λ where -- or use where clause
    .to → id; .from → id
    .from∘to → λ _ → refl

≲-antisym : {A : Set i} → {B : Set j} → (A≲B : A ≲ B) → (B≲A : B ≲ A)
    → (A≲B .to ≡ B≲A .from) → (A≲B .from ≡ B≲A .to)
    → A ≅ B
≲-antisym A≲B B≲A to≡from from≡to .to = A≲B .to
≲-antisym A≲B B≲A to≡from from≡to .from = A≲B .from
≲-antisym A≲B B≲A to≡from from≡to .from∘to = A≲B .from∘to
≲-antisym A≲B B≲A to≡from from≡to .to∘from y
    rewrite to≡from
    | from≡to
    | B≲A .from∘to y = refl

module ≲-Reasoning where

    infix 1 begin≲_
    infixr 2 _≲⟨⟩_ _≲⟨_⟩_
    infix 3 _≲∎

    begin≲_ : {A : Set i} → {B : Set j} → A ≲ B → A ≲ B
    begin≲ A≲B = A≲B

    _≲⟨⟩_ : (A : Set i) → {B : Set j} → A ≲ B → A ≲ B
    A ≲⟨⟩ A≲B = A≲B

    _≲⟨_⟩_ : (A : Set i) → {B : Set j} → {C : Set k} → A ≲ B → B ≲ C → A ≲ C
    A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

    _≲∎ : (A : Set i) → A ≲ A
    A ≲∎ = ≲-refl

open ≲-Reasoning

≅-implies-≲ : {A : Set i} → {B : Set j} → A ≅ B → A ≲ B
≅-implies-≲ A≅B .to = A≅B .to
≅-implies-≲ A≅B .from = A≅B .from
≅-implies-≲ A≅B .from∘to = A≅B .from∘to

record _⇔_ (A : Set i) (B : Set j) : Set (i ⊔ j) where
    field
        to : A → B
        from : B → A

open _⇔_

⇔-refl : {A : Set i} → A ⇔ A
⇔-refl .to = id
⇔-refl .from = id

⇔-sym : {A : Set i} → {B : Set j} → A ⇔ B → B ⇔ A
⇔-sym A⇔B .to = A⇔B .from
⇔-sym A⇔B .from = A⇔B .to

⇔-trans : {A : Set i} → {B : Set j} → {C : Set k} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans A⇔B B⇔C .to = B⇔C .to ∘ A⇔B .to
⇔-trans A⇔B B⇔C .from = A⇔B .from ∘ B⇔C .from

open import plfa.part1.Induction using (Bin; toBin; fromBin; fromBin-toBin)

ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin =
    record {
        to = toBin;
        from = fromBin;
        from∘to = fromBin-toBin
    }

subst-iso : {A : Set i} → (P : A → Set j) → {x y : A} → x ≡ y → (P x ≅ P y)
subst-iso P refl .to = id
subst-iso P refl .from = id
subst-iso P refl .from∘to _ = refl
subst-iso P refl .to∘from _ = refl

-- subst-iso : {A : Set i} → (P : A → Set j) → {x y : A} → x ≡ y → (P x ≅ P y)
-- subst-iso P p .to = subst P p
-- subst-iso P p .from = subst P (sym p)
-- subst-iso P p .from∘to u = trans (trans (sym (subst-trans P p (sym p))) (cong (λ e → subst P e u) (trans-sym-r p))) refl
-- subst-iso P p .to∘from v = trans (trans (sym (subst-trans P (sym p) p)) (cong (λ e → subst P e v) (trans-sym-l p))) refl

-- import Function using (_∘_; id)
-- import Function.Inverse using (_↔_)
-- import Function.LeftInverse using (_↞_)

-- a detour into homotopy type theory

record _≃_ (A : Set i) (B : Set j) : Set (i ⊔ j) where
    field
        to : A → B -- the functor f
        retraction : B → A -- the retraction g of f
        section : B → A -- the section h of f
        retraction∘to : (x : A) → retraction (to x) ≡ x -- the inverse of unit (sym η)
        to∘section : (y : B) → to (section y) ≡ y -- the counit ε

-- Has-Retraction : {A : Set i} → {B : Set j} → (f : A → B) → Set (i ⊔ j)
-- Has-Retraction {A = A} {B = B} f = Σ (B → A) (λ g → (x : A) → g (f x) ≡ x)
record Has-Retraction {A : Set i} {B : Set j} (to : A → B) : Set (i ⊔ j) where
    field
        retraction : B → A
        retraction∘to : (x : A) → retraction (to x) ≡ x

-- Has-Section : {A : Set i} → {B : Set j} → (f : A → B) → Set (i ⊔ j)
-- Has-Section {A = A} {B = B} f = Σ (B → A) (λ h → (y : B) → f (h y) ≡ y)
record Has-Section {A : Set i} {B : Set j} (to : A → B) : Set (i ⊔ j) where
    field
        section : B → A
        to∘section : (y : B) → to (section y) ≡ y

-- Is-Biinvertible : {A : Set i} → {B : Set j} → (f : A → B) → Set (i ⊔ j)
-- Is-Biinvertible f = Has-Retraction f × Has-Section f
record Is-Biinvertible {A : Set i} {B : Set j} (to : A → B) : Set (i ⊔ j) where
    field
        retraction : B → A
        section : B → A
        retraction∘to : (x : A) → retraction (to x) ≡ x
        to∘section : (y : B) → to (section y) ≡ y

-- Is-Invertible : {A : Set i} → {B : Set j} → (f : A → B) → Set (i ⊔ j)
-- Is-Invertible {A = A} {B = B} f = Σ (B → A) (λ g → ((x : A) → g (f x) ≡ x) × ((y : B) → f (g y) ≡ y))
record Is-Invertible {A : Set i} {B : Set j} (to : A → B) : Set (i ⊔ j) where
    field
        from : B → A
        from∘to : (x : A) → from (to x) ≡ x
        to∘from : (y : B) → to (from y) ≡ y

record Is-Half-Adjoint-Equivalence {A : Set i} {B : Set j} (to : A → B) : Set (i ⊔ j) where
    field
        from : B → A
        from∘to : (x : A) → from (to x) ≡ x
        to∘from : (y : B) → to (from y) ≡ y
        cong-from∘to : (x : A) → cong to (from∘to x) ≡ to∘from (to x)
        -- cong-to∘from : (y : B) → cong from (to∘from y) ≡ from∘to (from y)

Is-Invertible→Is-Biinvertible : {A : Set i} → {B : Set j} → {f : A → B}
    → Is-Invertible f → Is-Biinvertible f
Is-Invertible→Is-Biinvertible
    record {
        from = from;
        from∘to = from∘to;
        to∘from = to∘from
    } =
    record {
        retraction = from;
        section = from;
        retraction∘to = from∘to;
        to∘section = to∘from
    }

Is-Biinvertible→Is-Invertible : {A : Set i} → {B : Set j} → {f : A → B}
    → Is-Biinvertible f → Is-Invertible f
Is-Biinvertible→Is-Invertible {A = A} {B} {to}
    record {
        retraction = retraction;
        section = section;
        retraction∘to = retraction∘to;
        to∘section = to∘section
    } =
    record {
        from = retraction;
        from∘to = retraction∘to;
        to∘from = to∘retraction
    } where
        to∘retraction : (y : B) → to (retraction y) ≡ y
        to∘retraction y =
            begin
                to (retraction y)
            ≡⟨ cong (to ∘ retraction) (sym (to∘section y)) ⟩
                to (retraction (to (section y)))
            ≡⟨ cong to (retraction∘to (section y)) ⟩
                to (section y)
            ≡⟨ to∘section y ⟩
                y
            ∎

Is-Biinvertible→Is-Invertible′ : {A : Set i} → {B : Set j} → {f : A → B}
    → Is-Biinvertible f → Is-Invertible f
Is-Biinvertible→Is-Invertible′ {A = A} {B} {to}
    record {
        retraction = retraction;
        section = section;
        retraction∘to = retraction∘to;
        to∘section = to∘section
    } =
    record {
        from = section;
        from∘to = section∘to;
        to∘from = to∘section
    } where
        section∘to : (x : A) → section (to x) ≡ x
        section∘to x =
            begin
                section (to x)
            ≡⟨ sym (retraction∘to (section (to x))) ⟩
                retraction (to (section (to x)))
            ≡⟨ cong retraction (to∘section (to x)) ⟩
                retraction (to x)
            ≡⟨ retraction∘to x ⟩
                x
            ∎

Is-Invertible⇔Is-Biinvertible : {A : Set i} → {B : Set j} → {f : A → B}
    → Is-Invertible f ⇔ Is-Biinvertible f
Is-Invertible⇔Is-Biinvertible =
    record {
        to = Is-Invertible→Is-Biinvertible;
        from = Is-Biinvertible→Is-Invertible
    }

Fiber : {A : Set i} → {B : Set j} → (f : A → B) → (y : B) → Set (i ⊔ j)
Fiber {A = A} {B = B} f y = Σ A (λ x → f x ≡ y)

Is-Contractible : Set i → Set i
Is-Contractible A = Σ A (λ x → (y : A) → x ≡ y)

Has-Contractible-Fibers : {A : Set i} → {B : Set j} → (f : A → B) → Set (i ⊔ j)
Has-Contractible-Fibers {B = B} f = (y : B) → Is-Contractible (Fiber f y)

Is-hProp : Set i → Set i
Is-hProp A = (x y : A) → x ≡ y

Is-hProp′ : Set i → Set i
Is-hProp′ A = (x y : A) → Is-Contractible (x ≡ y)

Is-hProp″ : Set i → Set i
Is-hProp″ A = A → Is-Contractible A

Is-hSet : Set i → Set i
Is-hSet A = (x y : A) → Is-hProp (x ≡ y)

Is-hGroupoid : Set i → Set i
Is-hGroupoid A = (x y : A) → Is-hSet (x ≡ y)

Is-hType : ℕ → Set i → Set i
Is-hType zero A = Is-Contractible A
Is-hType (suc n) A = (x y : A) → Is-hType n (x ≡ y)

⊤-Is-hProp : Is-hProp ⊤
⊤-Is-hProp tt tt = refl

⊥-Is-hProp : Is-hProp ⊥
⊥-Is-hProp () ()

×-Is-hProp : {A : Set i} → {B : Set j} → Is-hProp A → Is-hProp B → Is-hProp (A × B) -- HoTT Book Example 3.6.1
×-Is-hProp is-hProp₁ is-hProp₂ (x₁ , y₁) (x₂ , y₂) = cong₂ _,_ (is-hProp₁ x₁ x₂) (is-hProp₂ y₁ y₂)

Σ-Is-hProp : {A : Set i} → {B : A → Set j} → Is-hProp A → ((x : A) → Is-hProp (B x)) → Is-hProp (Σ A B)
Σ-Is-hProp {A = A} {B = B} is-hProp₁ are-hProps₂ (x₁ , y₁) (x₂ , y₂) = trans
    (sym (subst₂-d-const (Σ A B) (is-hProp₁ x₁ x₂) (are-hProps₂ x₂ (subst B (is-hProp₁ x₁ x₂) y₁) y₂)))
    (cong₂-d _,_ (is-hProp₁ x₁ x₂) (are-hProps₂ x₂ (subst B (is-hProp₁ x₁ x₂) y₁) y₂))

→-Is-hProp : {A : Set i} → {B : Set j} → Is-hProp B → Is-hProp (A → B)
→-Is-hProp is-hProp f g = extensionality λ x → is-hProp (f x) (g x)

Π-Is-hProp : {A : Set i} → {B : A → Set j} → ((x : A) → Is-hProp (B x)) → Is-hProp ((x : A) → B x) -- HoTT Book Example 3.6.2
Π-Is-hProp is-hProp f g = Π-extensionality λ x → is-hProp x (f x) (g x)

¬-Is-hProp : {A : Set i} → Is-hProp (¬ A)
¬-Is-hProp = →-Is-hProp ⊥-Is-hProp

EM-Is-hProp : {A : Set i} → Is-hProp A → Is-hProp (A ⊎ ¬ A) -- HoTT Book Exercise 3.6
EM-Is-hProp is-hProp (inj₁ x) (inj₁ y) = cong inj₁ (is-hProp x y)
EM-Is-hProp is-hProp (inj₁ x) (inj₂ g) = ⊥-elim (g x)
EM-Is-hProp is-hProp (inj₂ f) (inj₁ y) = ⊥-elim (f y)
EM-Is-hProp is-hProp (inj₂ f) (inj₂ g) = cong inj₂ (¬-Is-hProp f g)

+-Is-hProp : {A : Set i} → {B : Set j} → Is-hProp A → Is-hProp B → ¬ (A × B) → Is-hProp (A ⊎ B) -- HoTT Book Exercise 3.7
+-Is-hProp is-hProp₁ is-hProp₂ f (inj₁ x₁) (inj₁ x₂) = cong inj₁ (is-hProp₁ x₁ x₂)
+-Is-hProp is-hProp₁ is-hProp₂ f (inj₁ x₁) (inj₂ y₂) = ⊥-elim (f (x₁ , y₂))
+-Is-hProp is-hProp₁ is-hProp₂ f (inj₂ y₁) (inj₁ x₂) = ⊥-elim (f (x₂ , y₁))
+-Is-hProp is-hProp₁ is-hProp₂ f (inj₂ y₁) (inj₂ y₂) = cong inj₂ (is-hProp₂ y₁ y₂)

×-eq-iso : {A : Set i} → {B : Set j}
    → {x₁ x₂ : A} → {y₁ y₂ : B}
    → (x₁ , y₁) ≡ (x₂ , y₂) ≅ x₁ ≡ x₂ × y₁ ≡ y₂ -- HoTT Book Theorem 2.6.2
×-eq-iso = record {
        to = f;
        from = g;
        from∘to = sym-η;
        to∘from = ε
    } where
        f : {A : Set i} → {B : Set j}
            → {x₁ x₂ : A} → {y₁ y₂ : B}
            → (x₁ , y₁) ≡ (x₂ , y₂) → x₁ ≡ x₂ × y₁ ≡ y₂
        f refl = refl , refl
        -- f z = cong proj₁ z , cong proj₂ z

        g : {A : Set i} → {B : Set j}
            → {x₁ x₂ : A} → {y₁ y₂ : B}
            → x₁ ≡ x₂ × y₁ ≡ y₂ → (x₁ , y₁) ≡ (x₂ , y₂)
        g (refl , refl) = refl

        sym-η : {A : Set i} → {B : Set j}
            → {x₁ x₂ : A} → {y₁ y₂ : B}
            → (z : (x₁ , y₁) ≡ (x₂ , y₂)) → g (f z) ≡ z
        sym-η refl = refl

        ε : {A : Set i} → {B : Set j}
            → {x₁ x₂ : A} → {y₁ y₂ : B}
            → (w : x₁ ≡ x₂ × y₁ ≡ y₂) → f (g w) ≡ w
        ε (refl , refl) = refl

Σ-eq-iso : {A : Set i} → {B : A → Set j}
    → {x₁ x₂ : A} → {y₁ : B x₁} → {y₂ : B x₂}
    → (x₁ , y₁) ≡ (x₂ , y₂) ≅ Σ (x₁ ≡ x₂) (λ p → subst B p y₁ ≡ y₂) -- HoTT Book Theorem 2.6.2
Σ-eq-iso = record {
        to = f;
        from = g;
        from∘to = η⁻¹;
        to∘from = ε
    } where
        f : {A : Set i} → {B : A → Set j}
            → {x₁ x₂ : A} → {y₁ : B x₁} → {y₂ : B x₂}
            → (x₁ , y₁) ≡ (x₂ , y₂) → Σ (x₁ ≡ x₂) (λ p → subst B p y₁ ≡ y₂)
        f refl = refl , refl
        -- f {B = B} z = cong proj₁ z , trans (subst-cong B z) (cong-d proj₂ z)

        g : {A : Set i} → {B : A → Set j}
            → {x₁ x₂ : A} → {y₁ : B x₁} → {y₂ : B x₂}
            → Σ (x₁ ≡ x₂) (λ p → subst B p y₁ ≡ y₂) → (x₁ , y₁) ≡ (x₂ , y₂)
        g (refl , refl) = refl

        η⁻¹ : {A : Set i} → {B : A → Set j}
            → {x₁ x₂ : A} → {y₁ : B x₁} → {y₂ : B x₂}
            → (z : (x₁ , y₁) ≡ (x₂ , y₂)) → g (f z) ≡ z
        η⁻¹ refl = refl

        ε : {A : Set i} → {B : A → Set j}
            → {x₁ x₂ : A} → {y₁ : B x₁} → {y₂ : B x₂}
            → (w : Σ (x₁ ≡ x₂) (λ p → subst B p y₁ ≡ y₂)) → f (g w) ≡ w
        ε (refl , refl) = refl

Unit-eq-iso : {x y : ⊤} → x ≡ y ≅ ⊤ -- HoTT Book Theorem 2.8.1
Unit-eq-iso = record {
        to = f;
        from = g;
        from∘to = η⁻¹;
        to∘from = ε
    } where
        f : {x y : ⊤} → x ≡ y → ⊤
        f refl = tt

        g : {x y : ⊤} → ⊤ → x ≡ y
        g {tt} {tt} tt = refl

        η⁻¹ : {x y : ⊤} → (p : x ≡ y) → g (f p) ≡ p
        η⁻¹ refl = refl
        
        ε : {x y : ⊤} → (t : ⊤) → f (g t) ≡ t
        ε tt = refl

id-Has-Contractible-Fibers : {A : Set i} → Has-Contractible-Fibers (id {A = A}) -- HoTT Book Lemma 3.11.8
id-Has-Contractible-Fibers x = (x , refl) , λ { (.x , refl) → Σ-eq-iso .from (refl , refl) }

Is-Invertible-cong : {A : Set i} → {B : Set j}
    → {f : A → B} → {x y : A}
    → Is-Invertible f → Is-Invertible (cong f {x} {y}) -- HoTT Book Theorem 2.11.1
Is-Invertible-cong {f = f} {x} {y} record { from = g; from∘to = η⁻¹; to∘from = ε } = record {
        from = cong-g;
        from∘to = cong-g-cong-f;
        to∘from = cong-f-cong-g
    } where
        cong-g : f x ≡ f y → x ≡ y
        cong-g q = trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y))

        cong-g-cong-f : (p : x ≡ y) → cong-g (cong f p) ≡ p
        cong-g-cong-f p =
            begin
                cong-g (cong f p)
            ≡⟨⟩
                trans (sym (η⁻¹ x)) (trans (cong g (cong f p)) (η⁻¹ y))
            ≡⟨ cong (λ r → trans (sym (η⁻¹ x)) (trans r (η⁻¹ y))) (cong-cong p) ⟩
                trans (sym (η⁻¹ x)) (trans (cong (g ∘ f) p) (η⁻¹ y))
            ≡⟨ homotopy-natural-variation η⁻¹ p ⟩
                cong id p
            ≡⟨ cong-id p ⟩
                p
            ∎

        cong-f-cong-g : (q : f x ≡ f y) → cong f (cong-g q) ≡ q
        cong-f-cong-g q =
            begin
                cong f (cong-g q)
            ≡⟨⟩
                cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))
            ≡⟨ sym (trans-identity-l (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y))))) ⟩
                trans refl (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y))))
            ≡⟨ cong (λ r → trans r (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y))))) (sym (trans-sym-r (sym (ε (f x))))) ⟩
                trans (trans (sym (ε (f x))) (sym (sym (ε (f x))))) (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y))))
            ≡⟨ trans-assoc (sym (ε (f x))) (sym (sym (ε (f x)))) (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))) ⟩
                trans (sym (ε (f x))) (trans (sym (sym (ε (f x)))) (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (sym (sym (ε (f x)))) r)) (sym (trans-identity-r (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))))) ⟩
                trans (sym (ε (f x))) (trans (sym (sym (ε (f x)))) (trans (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))) refl))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (sym (sym (ε (f x)))) (trans (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))) r))) (sym (trans-sym-l (ε (f y)))) ⟩
                trans (sym (ε (f x))) (trans (sym (sym (ε (f x)))) (trans (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))) (trans (sym (ε (f y))) (ε (f y)))))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (sym (sym (ε (f x)))) r)) (sym (trans-assoc (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))) (sym (ε (f y))) (ε (f y)))) ⟩
                trans (sym (ε (f x))) (trans (sym (sym (ε (f x)))) (trans (trans (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))) (sym (ε (f y)))) (ε (f y))))
            ≡⟨ cong (trans (sym (ε (f x)))) (sym (trans-assoc (sym (sym (ε (f x)))) (trans (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))) (sym (ε (f y)))) (ε (f y)))) ⟩
                trans (sym (ε (f x))) (trans (trans (sym (sym (ε (f x)))) (trans (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))) (sym (ε (f y))))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (trans (sym (sym (ε (f x)))) (trans r (sym (ε (f y))))) (ε (f y)))) (sym (cong-id (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))))) ⟩
                trans (sym (ε (f x))) (trans (trans (sym (sym (ε (f x)))) (trans (cong id (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y))))) (sym (ε (f y))))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans r (ε (f y)))) (homotopy-natural-variation (λ z → sym (ε z)) (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y))))) ⟩
                trans (sym (ε (f x))) (trans (cong (f ∘ g) (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y))))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans r (ε (f y)))) (sym (cong-cong (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))))) ⟩
                trans (sym (ε (f x))) (trans (cong f (cong g (cong f (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (cong f r) (ε (f y)))) (cong-cong (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))) ⟩
                trans (sym (ε (f x))) (trans (cong f (cong (g ∘ f) (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y))))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (cong f r) (ε (f y)))) (sym (homotopy-natural-variation (λ z → sym (η⁻¹ z)) (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y))))) ⟩
                trans (sym (ε (f x))) (trans (cong f (trans (sym (sym (η⁻¹ x))) (trans (cong id (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))) (sym (η⁻¹ y))))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (cong f (trans (sym (sym (η⁻¹ x))) (trans r (sym (η⁻¹ y))))) (ε (f y)))) (cong-id (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)))) ⟩
                trans (sym (ε (f x))) (trans (cong f (trans (sym (sym (η⁻¹ x))) (trans (trans (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y))) (sym (η⁻¹ y))))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (cong f (trans (sym (sym (η⁻¹ x))) r)) (ε (f y)))) (trans-assoc (sym (η⁻¹ x)) (trans (cong g q) (η⁻¹ y)) (sym (η⁻¹ y))) ⟩
                trans (sym (ε (f x))) (trans (cong f (trans (sym (sym (η⁻¹ x))) (trans (sym (η⁻¹ x)) (trans (trans (cong g q) (η⁻¹ y)) (sym (η⁻¹ y)))))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (cong f (trans (sym (sym (η⁻¹ x))) (trans (sym (η⁻¹ x)) r))) (ε (f y)))) (trans-assoc (cong g q) (η⁻¹ y) (sym (η⁻¹ y))) ⟩
                trans (sym (ε (f x))) (trans (cong f (trans (sym (sym (η⁻¹ x))) (trans (sym (η⁻¹ x)) (trans (cong g q) (trans (η⁻¹ y) (sym (η⁻¹ y))))))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (cong f (trans (sym (sym (η⁻¹ x))) (trans (sym (η⁻¹ x)) (trans (cong g q) r)))) (ε (f y)))) (trans-sym-r (η⁻¹ y)) ⟩
                trans (sym (ε (f x))) (trans (cong f (trans (sym (sym (η⁻¹ x))) (trans (sym (η⁻¹ x)) (trans (cong g q) refl)))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (cong f (trans (sym (sym (η⁻¹ x))) (trans (sym (η⁻¹ x)) r))) (ε (f y)))) (trans-identity-r (cong g q)) ⟩
                trans (sym (ε (f x))) (trans (cong f (trans (sym (sym (η⁻¹ x))) (trans (sym (η⁻¹ x)) (cong g q)))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (cong f r) (ε (f y)))) (sym (trans-assoc (sym (sym (η⁻¹ x))) (sym (η⁻¹ x)) (cong g q))) ⟩
                trans (sym (ε (f x))) (trans (cong f (trans (trans (sym (sym (η⁻¹ x))) (sym (η⁻¹ x))) (cong g q))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (cong f (trans r (cong g q))) (ε (f y)))) (trans-sym-l (sym (η⁻¹ x))) ⟩
                trans (sym (ε (f x))) (trans (cong f (trans refl (cong g q))) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans (cong f r) (ε (f y)))) (trans-identity-l (cong g q)) ⟩
                trans (sym (ε (f x))) (trans (cong f (cong g q)) (ε (f y)))
            ≡⟨ cong (λ r → trans (sym (ε (f x))) (trans r (ε (f y)))) (cong-cong q) ⟩
                trans (sym (ε (f x))) (trans (cong (f ∘ g) q) (ε (f y)))
            ≡⟨ homotopy-natural-variation ε q ⟩
                cong id q
            ≡⟨ cong-id q ⟩
                q
            ∎

Eq-iso : {A : Set i} → {B : Set j}
    → (iso : A ≅ B) → {x y : A}
    → x ≡ y ≅ iso .to x ≡ iso .to y
Eq-iso iso {x} {y} = record {
        to = cong (iso .to);
        from = has-Inverse-cong .Is-Invertible.from;
        from∘to = has-Inverse-cong .Is-Invertible.from∘to;
        to∘from = has-Inverse-cong .Is-Invertible.to∘from
    } where
        has-Inverse-cong : Is-Invertible (cong (iso .to) {x} {y})
        has-Inverse-cong = Is-Invertible-cong record {from = iso .from; from∘to = iso .from∘to; to∘from = iso .to∘from }

-- Unit and Empty type with universe polymorphism

record Unit : Set i where
    constructor unit

data Empty {i} : Set i where

Unit≅⊤ : Unit {i} ≅ ⊤
Unit≅⊤ .to unit = tt
Unit≅⊤ .from tt = unit
Unit≅⊤ .from∘to unit = refl
Unit≅⊤ .to∘from tt = refl

Empty≅⊥ : Empty {i} ≅ ⊥
Empty≅⊥ .to ()
Empty≅⊥ .from ()
Empty≅⊥ .from∘to ()
Empty≅⊥ .to∘from ()

Unit-Is-hProp : Is-hProp (Unit {i})
Unit-Is-hProp unit unit = refl

Empty-Is-hProp : Is-hProp (Empty {i})
Empty-Is-hProp () ()

-- encode-decode method

CodeSum-inj₁ : {A : Set i} → {B : Set j} → A → A ⊎ B → Set i
CodeSum-inj₁ x₁ (inj₁ x₂) = x₁ ≡ x₂
CodeSum-inj₁ x₁ (inj₂ y₂) = Empty

CodeSum-inj₂ : {A : Set i} → {B : Set j} → B → A ⊎ B → Set j
CodeSum-inj₂ y₁ (inj₁ x₂) = Empty
CodeSum-inj₂ y₁ (inj₂ y₂) = y₁ ≡ y₂

Sum-eq≅CodeSum-inj₁ : {A : Set i} → {B : Set j}
    → {x₁ : A} → {w : A ⊎ B}
    → inj₁ x₁ ≡ w ≅ CodeSum-inj₁ x₁ w -- HoTT Book Theorem 2.12.5
Sum-eq≅CodeSum-inj₁ = record {
        to = encodeSum-inj₁;
        from = decodeSum-inj₁;
        from∘to = decodeSum-inj₁-encodeSum-inj₁;
        to∘from = encodeSum-inj₁-decodeSum-inj₁
    } where
        encodeSum-inj₁ : {A : Set i} → {B : Set j}
            → {x₁ : A} → {w : A ⊎ B}
            → inj₁ x₁ ≡ w → CodeSum-inj₁ x₁ w
        encodeSum-inj₁ refl = refl
        -- encodeSum-inj₁ {x₁ = x₁} p = subst (CodeSum-inj₁ x₁) p refl

        decodeSum-inj₁ : {A : Set i} → {B : Set j}
            → {x₁ : A} → {w : A ⊎ B}
            → CodeSum-inj₁ x₁ w → inj₁ x₁ ≡ w
        decodeSum-inj₁ {x₁ = x₁} {w = inj₁ .x₁} refl = cong inj₁ refl

        decodeSum-inj₁-encodeSum-inj₁ : {A : Set i} → {B : Set j}
            → {x₁ : A} → {w : A ⊎ B}
            → (p : inj₁ x₁ ≡ w) → decodeSum-inj₁ (encodeSum-inj₁ p) ≡ p
        decodeSum-inj₁-encodeSum-inj₁ refl = refl

        encodeSum-inj₁-decodeSum-inj₁ : {A : Set i} → {B : Set j}
            → {x₁ : A} → {w : A ⊎ B}
            → (code : CodeSum-inj₁ x₁ w) → encodeSum-inj₁ (decodeSum-inj₁ code) ≡ code
        encodeSum-inj₁-decodeSum-inj₁ {x₁ = x₁} {w = inj₁ .x₁} refl = refl

Sum-eq≅CodeSum-inj₂ : {A : Set i} → {B : Set j}
    → {y₁ : B} → {w : A ⊎ B}
    → inj₂ y₁ ≡ w ≅ CodeSum-inj₂ y₁ w
Sum-eq≅CodeSum-inj₂ = record {
        to = encodeSum-inj₂;
        from = decodeSum-inj₂;
        from∘to = decodeSum-inj₂-encodeSum-inj₂;
        to∘from = encodeSum-inj₂-decodeSum-inj₂
    } where
        encodeSum-inj₂ : {A : Set i} → {B : Set j}
            → {y₁ : B} → {w : A ⊎ B}
            → inj₂ y₁ ≡ w → CodeSum-inj₂ y₁ w
        encodeSum-inj₂ refl = refl
        -- encodeSum-inj₂ {y₁ = y₁} p = subst (CodeSum-inj₂ y₁) p refl

        decodeSum-inj₂ : {A : Set i} → {B : Set j}
            → {y₁ : B} → {w : A ⊎ B}
            → CodeSum-inj₂ y₁ w → inj₂ y₁ ≡ w
        decodeSum-inj₂ {y₁ = y₁} {w = inj₂ .y₁} refl = cong inj₂ refl

        decodeSum-inj₂-encodeSum-inj₂ : {A : Set i} → {B : Set j}
            → {y₁ : B} → {w : A ⊎ B}
            → (p : inj₂ y₁ ≡ w) → decodeSum-inj₂ (encodeSum-inj₂ p) ≡ p
        decodeSum-inj₂-encodeSum-inj₂ refl = refl

        encodeSum-inj₂-decodeSum-inj₂ : {A : Set i} → {B : Set j}
            → {y₁ : B} → {w : A ⊎ B}
            → (code : CodeSum-inj₂ y₁ w) → encodeSum-inj₂ (decodeSum-inj₂ code) ≡ code
        encodeSum-inj₂-decodeSum-inj₂ {y₁ = y₁} {w = inj₂ .y₁} refl = refl
        
Sum-eq-iso-inj₁ : {A : Set i} → {B : Set j}
    → {x₁ x₂ : A}
    → inj₁ {A = A} {B = B} x₁ ≡ inj₁ x₂ ≅ x₁ ≡ x₂
Sum-eq-iso-inj₁ = Sum-eq≅CodeSum-inj₁

Sum-eq-iso-inj₂ : {A : Set i} → {B : Set j}
    → {y₁ y₂ : B}
    → inj₂ {A = A} {B = B} y₁ ≡ inj₂ y₂ ≅ y₁ ≡ y₂
Sum-eq-iso-inj₂ = Sum-eq≅CodeSum-inj₂

Sum-eq-iso-inj₁-inj₂ : {A : Set i} → {B : Set j}
    → {x : A} → {y : B}
    → inj₁ {A = A} {B = B} x ≡ inj₂ y ≅ ⊥
Sum-eq-iso-inj₁-inj₂ = ≅-trans Sum-eq≅CodeSum-inj₁ Empty≅⊥

Sum-eq-iso-inj₂-inj₁ : {A : Set i} → {B : Set j}
    → {x : A} → {y : B}
    → inj₂ {A = A} {B = B} y ≡ inj₁ x ≅ ⊥
Sum-eq-iso-inj₂-inj₁ = ≅-trans Sum-eq≅CodeSum-inj₂ Empty≅⊥

Sum-Is-hSet : {A : Set i} → {B : Set j} → Is-hSet A → Is-hSet B → Is-hSet (A ⊎ B) -- HoTT Book Exercise 3.2
Sum-Is-hSet is-hSet₁ is-hSet₂ (inj₁ x₁) (inj₁ x₂) p q = Eq-iso Sum-eq-iso-inj₁ .from (is-hSet₁ x₁ x₂ (Sum-eq-iso-inj₁ .to p) (Sum-eq-iso-inj₁ .to q)) -- This does not work: is-hSet₁ x₁ x₂ (inj₁-injective p) (inj₁-injective q)
Sum-Is-hSet is-hSet₁ is-hSet₂ (inj₂ y₁) (inj₂ y₂) p q = Eq-iso Sum-eq-iso-inj₂ .from (is-hSet₂ y₁ y₂ (Sum-eq-iso-inj₂ .to p) (Sum-eq-iso-inj₂ .to q))

×-Is-hSet : {A : Set i} → {B : Set j} → Is-hSet A → Is-hSet B → Is-hSet (A × B) -- HoTT Book Example 3.1.5 (a)
×-Is-hSet is-hSet₁ is-hSet₂ (x₁ , y₁) (x₂ , y₂) p q = Eq-iso ×-eq-iso .from
    (×-eq-iso .from
        (is-hSet₁ x₁ x₂ (×-eq-iso .to p .proj₁) (×-eq-iso .to q .proj₁) ,
            is-hSet₂ y₁ y₂ (×-eq-iso .to p .proj₂) (×-eq-iso .to q .proj₂)))

Σ-Is-hSet : {A : Set i} → {B : A → Set j} → Is-hSet A → ((x : A) → Is-hSet (B x)) → Is-hSet (Σ A B) -- HoTT Book Example 3.1.5 (b), Exercise 3.3
Σ-Is-hSet {B = B} is-hSet₁ are-hSets₂ (x₁ , y₁) (x₂ , y₂) p q = Eq-iso Σ-eq-iso .from
    (Σ-eq-iso .from
        (is-hSet₁ x₁ x₂ (Σ-eq-iso .to p .proj₁) (Σ-eq-iso .to q .proj₁) ,
            are-hSets₂ x₂
                (subst B (Σ-eq-iso .to q .proj₁) y₁)
                y₂
                (subst (λ r → subst B r y₁ ≡ y₂) (is-hSet₁ x₁ x₂ (Σ-eq-iso .to p .proj₁) (Σ-eq-iso .to q .proj₁)) (Σ-eq-iso .to p .proj₂))
                (Σ-eq-iso .to q .proj₂)))

-- →-Is-hSet : {A : Set i} → {B : Set j} → Is-hSet B → Is-hSet (A → B) -- TODO
-- →-Is-hSet is-hSet f g p q = ?

-- Π-Is-hSet : {A : Set i} → {B : A → Set j} → ((x : A) → Is-hSet (B x)) → Is-hSet ((x : A) → B x) -- HoTT Book Example 3.1.6
-- Π-Is-hSet is-hSet f g = ?

Is-Contractible-implies-Is-hProp : {A : Set i} → Is-Contractible A → Is-hProp A
Is-Contractible-implies-Is-hProp is-Contractible x y = trans (sym (is-Contractible .proj₂ x)) (is-Contractible .proj₂ y)

Is-Contractible⇔Is-Inhabited×Is-hProp : {A : Set i} → Is-Contractible A ⇔ (A × Is-hProp A) --  HoTT Book Lemma 3.11.3 (a)
Is-Contractible⇔Is-Inhabited×Is-hProp = record {
        to = f;
        from = g
    } where
        f : {A : Set i} → Is-Contractible A → A × Is-hProp A
        f is-Contractible = (is-Contractible .proj₁) , (λ x y → trans (sym (is-Contractible .proj₂ x)) (is-Contractible .proj₂ y))

        g : {A : Set i} → A × Is-hProp A → Is-Contractible A
        g (x , is-hProp) = x , λ y → is-hProp x y

⊤-Is-Contractible : Is-Contractible ⊤
-- ⊤-Is-Contractible = Is-Contractible⇔Is-Inhabited×Is-hProp .from (tt , ⊤-Is-hProp)
⊤-Is-Contractible = tt , λ { tt → refl }

→-Is-Contractible : {A : Set i} → {B : Set j} → Is-Contractible B → Is-Contractible (A → B)
→-Is-Contractible is-Contractible = Is-Contractible⇔Is-Inhabited×Is-hProp .from ((λ x → is-Contractible .proj₁) , →-Is-hProp (Is-Contractible-implies-Is-hProp is-Contractible))

Π-Is-Contractible : {A : Set i} → {B : A → Set j} → ((x : A) → Is-Contractible (B x)) → Is-Contractible ((x : A) → B x) -- HoTT Book Lemma 3.11.6
Π-Is-Contractible are-Contractibles = Is-Contractible⇔Is-Inhabited×Is-hProp .from ((λ x → are-Contractibles x .proj₁) , Π-Is-hProp (λ x → Is-Contractible-implies-Is-hProp (are-Contractibles x)))

Retract-Is-Contractible : {A : Set i} → {B : Set j} → A ≲ B → Is-Contractible B → Is-Contractible A -- HoTT Book Lemma 3.11.7
Retract-Is-Contractible record { to = f; from = g; from∘to = g∘f } (b , q) = g b , λ x → trans (cong g (q (f x))) (g∘f x)

trans-is-hProp : {A : Set i} → (is-hProp : Is-hProp A) → {x y z : A} → (p : y ≡ z)
    → trans (is-hProp x y) p ≡ is-hProp x z
trans-is-hProp is-hProp {x} {y} {z} p = trans (sym (subst-eq-r (is-hProp x y) p)) (cong-d (is-hProp x) p)

Is-hProp-implies-Is-hSet : {A : Set i} → Is-hProp A → Is-hSet A -- HoTT Book Lemma 3.3.4
Is-hProp-implies-Is-hSet is-hProp x y p q =
    begin
        p
    ≡⟨ trans-identity-l p ⟩
        trans refl p
    ≡⟨ cong (λ r → trans r p) (sym (trans-sym-l (is-hProp x x))) ⟩
        trans (trans (sym (is-hProp x x)) (is-hProp x x)) p
    ≡⟨ trans-assoc (sym (is-hProp x x)) (is-hProp x x) p ⟩
        trans (sym (is-hProp x x)) (trans (is-hProp x x) p)
    ≡⟨ cong (trans (sym (is-hProp x x))) (trans-is-hProp is-hProp p) ⟩
        trans (sym (is-hProp x x)) (is-hProp x y)
    ≡⟨ cong (trans (sym (is-hProp x x))) (sym (trans-is-hProp is-hProp q)) ⟩
        trans (sym (is-hProp x x)) (trans (is-hProp x x) q)
    ≡⟨ sym (trans-assoc (sym (is-hProp x x)) (is-hProp x x) q) ⟩
        trans (trans (sym (is-hProp x x)) (is-hProp x x)) q
    ≡⟨ cong (λ r → trans r q) (trans-sym-l (is-hProp x x)) ⟩
        trans refl q
    ≡⟨ sym (trans-identity-l q) ⟩
        q
    ∎

Is-Contractible-implies-Is-hSet : {A : Set i} → Is-Contractible A → Is-hSet A
Is-Contractible-implies-Is-hSet = Is-hProp-implies-Is-hSet ∘ Is-Contractible-implies-Is-hProp

Is-hProp⇔Is-hProp′ : {A : Set i} → Is-hProp A ⇔ Is-hProp′ A -- HoTT Book Lemma 3.11.10
Is-hProp⇔Is-hProp′ = record {
        to = f;
        from = g
    } where
        f : {A : Set i} → Is-hProp A → Is-hProp′ A
        f is-hProp x y = is-hProp x y , λ p → Is-hProp-implies-Is-hSet is-hProp x y (is-hProp x y) p

        g : {A : Set i} → Is-hProp′ A → Is-hProp A
        g is-hProp′ x y = is-hProp′ x y .proj₁

Is-hProp⇔Is-hProp″ : {A : Set i} → Is-hProp A ⇔ Is-hProp″ A -- HoTT Book Exercise 3.5
Is-hProp⇔Is-hProp″ = record {
        to = f;
        from = g
    } where
        f : {A : Set i} → Is-hProp A → Is-hProp″ A
        f is-hProp x = x , λ y → is-hProp x y

        g : {A : Set i} → Is-hProp″ A → Is-hProp A
        g is-hProp″ x y = trans (sym (is-hProp″ x .proj₂ x)) (is-hProp″ x .proj₂ y)

Is-hSet-implies-Is-hGroupoid : {A : Set i} → Is-hSet A → Is-hGroupoid A -- HoTT Book Lemma 3.1.8
Is-hSet-implies-Is-hGroupoid is-hSet x y p q r s = Is-hProp-implies-Is-hSet (is-hSet x y) p q r s

Is-Contractible-Is-hProp : {A : Set i} → Is-hProp (Is-Contractible A) -- HoTT Book Lemma 3.11.4, note this uses Π-extensionality
Is-Contractible-Is-hProp {A = A} (x₁ , f₁) (x₂ , f₂) = Σ-eq-iso .from
    (f₁ x₂ , Π-Is-hProp
        (λ x → Is-Contractible-implies-Is-hSet (x₁ , f₁) x₂ x)
        (subst (λ z → (x : A) → z ≡ x) (f₁ x₂) f₁)
        f₂)

Is-Contractible-Is-Contractible : {A : Set i} → Is-Contractible A → Is-Contractible (Is-Contractible A) -- HoTT Book Corollary 3.11.5
Is-Contractible-Is-Contractible is-Contractible = Is-Contractible⇔Is-Inhabited×Is-hProp .from (is-Contractible , Is-Contractible-Is-hProp)

Is-hProp-Is-hProp : {A : Set i} → Is-hProp (Is-hProp A) -- HoTT Book Lemma 3.3.5 (a)
Is-hProp-Is-hProp f g = Π-extensionality₂ (λ x y → Is-hProp-implies-Is-hSet f x y (f x y) (g x y))

Is-hSet-Is-hProp : {A : Set i} → Is-hProp (Is-hSet A) -- HoTT Book Lemma 3.3.5 (b)
Is-hSet-Is-hProp f g = Π-extensionality₂ (λ x y → Is-hProp-Is-hProp (f x y) (g x y))
-- Is-hSet-Is-hProp f g = Π-extensionality₂ (λ x y → Π-extensionality₂ (λ p q → Is-hSet-implies-Is-hGroupoid f x y p q (f x y p q) (g x y p q)))

Is-hGroupoid-Is-hProp : {A : Set i} → Is-hProp (Is-hGroupoid A)
Is-hGroupoid-Is-hProp f g = Π-extensionality₂ (λ x y → Is-hSet-Is-hProp (f x y) (g x y))

hProp-iso : {A : Set i} → {B : Set j}
    → Is-hProp A → Is-hProp B
    → (A → B) → (B → A) → A ≅ B -- HoTT Book Lemma 3.3.3
hProp-iso p q f g .to = f
hProp-iso p q f g .from = g
hProp-iso p q f g .from∘to x = p (g (f x)) x
hProp-iso p q f g .to∘from y = q (f (g y)) y

≅-Is-hProp : {A : Set i} → {B : Set j} → A ≅ B → Is-hProp B → Is-hProp A
≅-Is-hProp iso is-hProp x y =
    begin
        x
    ≡⟨ sym (iso .from∘to x) ⟩
        iso .from (iso .to x)
    ≡⟨ cong (iso .from) (is-hProp (iso .to x) (iso .to y)) ⟩
        iso .from (iso .to y)
    ≡⟨ iso .from∘to y ⟩
        y
    ∎

≅-Is-hSet : {A : Set i} → {B : Set j} → A ≅ B → Is-hSet B → Is-hSet A -- HoTT Book Exercise 3.1
≅-Is-hSet iso is-hSet x y p q =
    begin
        p
    ≡⟨ sym (cong-id p) ⟩
        cong id p
    ≡⟨ sym (homotopy-natural-variation (iso .from∘to) p) ⟩
        trans
            (sym (iso .from∘to x))
            (trans
                (cong (iso .from ∘ iso .to) p)
                (iso .from∘to y))
    ≡⟨ sym (cong (λ r → trans (sym (iso .from∘to x)) (trans r (iso .from∘to y))) (cong-cong p)) ⟩
        trans
            (sym (iso .from∘to x))
            (trans
                (cong (iso .from) (cong (iso .to) p))
                (iso .from∘to y))
    ≡⟨ cong (λ r → trans (sym (iso .from∘to x)) (trans (cong (iso .from) r) (iso .from∘to y))) (is-hSet (iso .to x) (iso .to y) (cong (iso .to) p) (cong (iso .to) q)) ⟩
        trans
            (sym (iso .from∘to x))
            (trans
                (cong (iso .from) (cong (iso .to) q))
                (iso .from∘to y))
    ≡⟨ cong (λ r → trans (sym (iso .from∘to x)) (trans r (iso .from∘to y))) (cong-cong q) ⟩
        trans
            (sym (iso .from∘to x))
            (trans
                (cong (iso .from ∘ iso .to) q)
                (iso .from∘to y))
    ≡⟨ homotopy-natural-variation (iso .from∘to) q ⟩
        cong id q
    ≡⟨ cong-id q ⟩
        q
    ∎

Σ-Is-Prop-iso : {A : Set i} → {B : A → Set j} → {Z : Set k}
    → ({x : A} → Is-hProp (B x))
    → (to : Z → A) → (from : A → Z) → (from∘to : (z : Z) → from (to z) ≡ z) -- Z ≲ A
    → (to-P : (z : Z) → B (to z)) → (B-to∘from : (x : A) → B x → to (from x) ≡ x)
    → Σ A B ≅ Z
Σ-Is-Prop-iso {B = B} are-hProps f g g∘f f-P B-f∘g = record {
        to = g ∘ proj₁;
        from = λ z → f z , f-P z;
        from∘to = λ { (x , y) → Σ-eq-iso .from (B-f∘g x y , are-hProps (subst B (B-f∘g x y) (f-P (g x))) y) };
        to∘from = g∘f
    }

Σ-Is-Contractible-proj₁-iso : {A : Set i} → {B : A → Set j}
    → ({x : A} → Is-Contractible (B x))
    → Σ A B ≅ A -- HoTT Book Lemma 3.11.9 (a)
Σ-Is-Contractible-proj₁-iso {B = B} are-Contractible = record {
        to = proj₁;
        from = λ x → x , are-Contractible .proj₁;
        from∘to = λ { (x , y) → Σ-eq-iso .from (refl , are-Contractible .proj₂ y) };
        to∘from = λ x → refl
    }

Σ-Is-Contractible-proj₂-iso : {A : Set i} → {B : A → Set j}
    → (is-Contractible : Is-Contractible A)
    → Σ A B ≅ B (is-Contractible .proj₁) -- HoTT Book Lemma 3.11.9 (b), Exercise 3.20
Σ-Is-Contractible-proj₂-iso is-Contractible = record {
        to = f is-Contractible;
        from = g is-Contractible;
        from∘to = g∘f is-Contractible;
        to∘from = f∘g is-Contractible
    } where
        f : {A : Set i} → {B : A → Set j}
            → (is-Contractible : Is-Contractible A)
            → Σ A B → B (is-Contractible .proj₁)
        f {B = B} (a , p) (x , y) = subst B (sym (p x)) y

        g : {A : Set i} → {B : A → Set j}
            → (is-Contractible : Is-Contractible A)
            → B (is-Contractible .proj₁) → Σ A B
        g (a , p) b = a , b

        g∘f : {A : Set i} → {B : A → Set j}
            → (is-Contractible : Is-Contractible A)
            → (w : Σ A B) → g is-Contractible (f is-Contractible w) ≡ w
        -- g∘f {B = B} (a , p) (x , y) = Σ-eq-iso .from (p x , trans (sym (subst-trans B (sym (p x)) (p x))) (cong (λ q → subst B q y) (trans-sym-l (p x))))
        g∘f {B = B} (a , p) (x , y) with p x
        ... | refl = refl
        
        f∘g : {A : Set i} → {B : A → Set j}
            → (is-Contractible : Is-Contractible A)
            → (b : B (is-Contractible .proj₁)) → f {B = B} is-Contractible (g is-Contractible b) ≡ b
        f∘g {B = B} (a , p) b = cong (λ q → subst B q b) (Is-Contractible-implies-Is-hSet (a , p) a a (sym (p a)) refl)

Σ-Is-Contractible-iso : {A : Set i} → {B : A → Set j} → {Z : Set k}
    → ({x : A} → Is-Contractible (B x))
    → (to : Z → A) → (from : A → Z) → (from∘to : (z : Z) → from (to z) ≡ z) -- Z ≲ A
    → (B-to∘from : (x : A) → B x → to (from x) ≡ x)
    → Σ A B ≅ Z
Σ-Is-Contractible-iso {B = B} are-Contractible f g g∘f B-f∘g = record {
        to = g ∘ proj₁;
        from = λ z → f z , are-Contractible {f z} .proj₁;
        -- from∘to = λ { (x , y) → Σ-eq-iso .from (B-f∘g x y , (Is-Contractible-implies-Is-hProp are-Contractible (subst B (B-f∘g x y) (are-Contractible .proj₁)) y)) };
        from∘to = λ { (x , y) → Σ-eq-iso .from (B-f∘g x y , trans (sym (are-Contractible .proj₂ (subst B (B-f∘g x y) (are-Contractible .proj₁)))) (are-Contractible .proj₂ y)) };
        to∘from = g∘f
    }

Σ-Is-Contractible-iso′ : {A : Set i} → {B : A → Set j} → {Z : Set k}
    → ({x : A} → Is-Contractible (B x))
    → (to : Z → A) → (from : A → Z) → (from∘to : (z : Z) → from (to z) ≡ z) -- Z ≲ A
    → (B-to∘from : (x : A) → B x → to (from x) ≡ x)
    → Σ A B ≅ Z
Σ-Is-Contractible-iso′ are-Contractible f g g∘f B-f∘g = Σ-Is-Prop-iso
    (Is-Contractible-implies-Is-hProp are-Contractible)
    f g g∘f (λ x → are-Contractible .proj₁) B-f∘g

Σ-Is-Contractible-proj₁-iso′ : {A : Set i} → {B : A → Set j}
    → ({x : A} → Is-Contractible (B x))
    → Σ A B ≅ A -- HoTT Book Lemma 3.11.9 (a)
Σ-Is-Contractible-proj₁-iso′ are-Contractible = Σ-Is-Prop-iso
    (Is-Contractible-implies-Is-hProp are-Contractible)
    id id (λ x → refl) (λ x → are-Contractible .proj₁) (λ x _ → refl)

Σ-Is-Contractible-proj₁-iso″ : {A : Set i} → {B : A → Set j}
    → ({x : A} → Is-Contractible (B x))
    → Σ A B ≅ A -- HoTT Book Lemma 3.11.9 (a)
Σ-Is-Contractible-proj₁-iso″ are-Contractible = Σ-Is-Contractible-iso′ are-Contractible id id (λ x → refl) (λ x _ → refl)

weak-extensionality : {A : Set i} → {B : A → Set j}
    → ((x : A) → Is-Contractible (B x)) → Is-Contractible ((x : A) → B x) -- HoTT Book Definition 4.9.1, TODO: Prove this from non-dependent function extensionality
weak-extensionality are-Contractible = (λ x → are-Contractible x .proj₁) , λ f → Π-extensionality (λ x → are-Contractible x .proj₂ (f x))

-- extensionality-iso : {A : Set i} → {B : Set j} → {f g : A → B}
--     → (f ≡ g) ≅ ((x : A) → f x ≡ g x)
-- extensionality-iso = record {
--         to = cong-app;
--         from = extensionality;
--         from∘to = extensionality-cong-app;
--         to∘from = cong-app-extensionality
--     } where
--         extensionality-cong-app : {A : Set i} → {B : Set j} → {f g : A → B}
--             → (p : f ≡ g) → extensionality (cong-app p) ≡ p
--         extensionality-cong-app p = ?

--         cong-app-extensionality : {A : Set i} → {B : Set j} → {f g : A → B}
--             → (h : (x : A) → f x ≡ g x) → cong-app (extensionality h) ≡ h
--         cong-app-extensionality h = ?

-- Π-extensionality-iso : {A : Set i} → {B : A → Set j} → {f g : (x : A) → B x}
--     → (f ≡ g) ≅ ((x : A) → f x ≡ g x) -- HoTT Book Exercise 2.16
-- Π-extensionality-iso = record {
--         to = cong-app-d;
--         from = Π-extensionality;
--         from∘to = Π-extensionality-cong-app-d;
--         to∘from = cong-app-d-Π-extensionality
--     } where
--         Π-extensionality-cong-app-d : {A : Set i} → {B : A → Set j} → {f g : (x : A) → B x}
--             → (p : f ≡ g) → Π-extensionality (cong-app-d p) ≡ p
--         Π-extensionality-cong-app-d p = ?

--         cong-app-d-Π-extensionality : {A : Set i} → {B : A → Set j} → {f g : (x : A) → B x}
--             → (h : (x : A) → f x ≡ g x) → cong-app-d (Π-extensionality h) ≡ h
--         cong-app-d-Π-extensionality h = ?

-- Has-Retraction-Is-hProp : {A : Set i} → {B : Set j} → (f : A → B) → Is-hProp (Has-Retraction f)
-- Has-Retraction-Is-hProp f (g₁ , sym-η₁) (g₂ , sym-η₂) = Σ-eq-iso .from ((extensionality (λ y → ?) , ?)
