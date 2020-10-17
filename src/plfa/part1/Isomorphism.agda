module plfa.part1.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; trans)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

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

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

_∘′_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f = λ x → g (f x)

-- Extensionality

postulate
    extensionality : {A B : Set} → {f g : A → B}
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

same : _+′_ ≡ _+_
same = extensionality λ m → extensionality (λ n → same-app m n)

postulate
    ∀-extensionality : {A : Set} → {B : A → Set} → {f g : (x : A) → B x}
        → ((x : A) → f x ≡ g x) → f ≡ g

infix 0 _≃_

record _≃_ (A B : Set) : Set where
    field
        to : A → B
        from : B → A
        from∘to : (x : A) → from (to x) ≡ x
        to∘from : (y : B) → to (from y) ≡ y

open _≃_ -- this opens the fields declared in the record

data _≃′_ (A B : Set) : Set where
    mk-≃′ : (to : A → B) → (from : B → A)
        → (from∘to : (x : A) → from (to x) ≡ x)
        → (to∘from : (y : B) → to (from y) ≡ y)
        → A ≃′ B

to′ : {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : {A B : Set} → (A≃B : A ≃′ B) → ((x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : {A B : Set} → (A≃B : A ≃′ B) → ((y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

≃-refl : {A : Set} → A ≃ A
≃-refl =
    record {
        to = λ {x → x};
        from = λ {y → y};
        from∘to = λ {x → refl};
        to∘from = λ {y → refl}
    }

≃-sym : {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B =
    record {
        to = from A≃B;
        from = to A≃B;
        from∘to = to∘from A≃B;
        to∘from = from∘to A≃B
    }

≃-trans : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C =
    record {
        to = to B≃C ∘ to A≃B;
        from = from A≃B ∘ from B≃C;
        from∘to = λ x → trans (cong (from A≃B) (from∘to B≃C (to A≃B x))) (from∘to A≃B x);
        to∘from = λ y → trans (cong (to B≃C) (to∘from A≃B (from B≃C y))) (to∘from B≃C y)
    }

module ≃-Reasoning where

    infix 1 begin≃_
    infixr 2 _≃⟨⟩_ _≃⟨_⟩_
    infix 3 _≃∎

    begin≃_ : {A B : Set} → A ≃ B → A ≃ B
    begin≃ A≃B = A≃B

    _≃⟨⟩_ : (A : Set) → {B : Set} → A ≃ B → A ≃ B
    A ≃⟨⟩ A≃B = A≃B

    _≃⟨_⟩_ : (A : Set) → {B C : Set} → A ≃ B → B ≃ C → A ≃ C
    A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

    _≃∎ : (A : Set) → A ≃ A
    A ≃∎ = ≃-refl

open ≃-Reasoning

-- Embedding

record _≲_ (A B : Set) : Set where -- A is a retract of B
    field
        to : A → B -- section of from
        from : B → A -- retraction of to
        from∘to : (x : A) → from (to x) ≡ x
infix 0 _≲_
open _≲_

id : {A : Set} → A → A
id x = x

≲-refl : {A : Set} → A ≲ A
to ≲-refl = id -- copattern matching, put cursor in the hole, hit C-c C-c then hit enter, i.e., case split on the right side
from ≲-refl = id
from∘to ≲-refl x = refl -- can also combine copattern matching with pattern matching

≲-trans : {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C .to = B≲C .to ∘ A≲B .to -- copattern matching, here we changed to suffix notation (prefix), default is prefix
≲-trans A≲B B≲C .from = A≲B .from ∘ B≲C .from
≲-trans A≲B B≲C .from∘to x -- can also combine with rewrite and with
    rewrite B≲C .from∘to (A≲B .to x)
    | A≲B .from∘to x = refl

≲-refl′ : {A : Set} → A ≲ A
≲-refl′ = λ { .to → id; .from → id; .from∘to → λ x → refl } -- copattern matching can also use lambda abstraction, but must be in suffix notation

≲-refl″ : {A : Set} → A ≲ A
≲-refl″ = λ where -- or use where clause
    .to → id; .from → id
    .from∘to → λ _ → refl

≲-antisym : {A B : Set} → (A≲B : A ≲ B) → (B≲A : B ≲ A)
    → (A≲B .to ≡ B≲A .from) → (A≲B .from ≡ B≲A .to)
    → A ≃ B
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

    begin≲_ : {A B : Set} → A ≲ B → A ≲ B
    begin≲ A≲B = A≲B

    _≲⟨⟩_ : (A : Set) → {B : Set} → A ≲ B → A ≲ B
    A ≲⟨⟩ A≲B = A≲B

    _≲⟨_⟩_ : (A : Set) → {B C : Set} → A ≲ B → B ≲ C → A ≲ C
    A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

    _≲∎ : (A : Set) → A ≲ A
    A ≲∎ = ≲-refl

open ≲-Reasoning

≃-implies-≲ : {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ A≃B .to = A≃B .to
≃-implies-≲ A≃B .from = A≃B .from
≃-implies-≲ A≃B .from∘to = A≃B .from∘to

record _⇔_ (A B : Set) : Set where
    field
        to : A → B
        from : B → A

open _⇔_

⇔-refl : {A : Set} → A ⇔ A
⇔-refl .to = id
⇔-refl .from = id

⇔-sym : {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym A⇔B .to = A⇔B .from
⇔-sym A⇔B .from = A⇔B .to

⇔-trans : {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans A⇔B B⇔C .to = B⇔C .to ∘ A⇔B .to
⇔-trans A⇔B B⇔C .from = A⇔B .from ∘ B⇔C .from

open import plfa.part1.Binary using (Bin; to; from; from-to)

ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin =
    record {
        to = plfa.part1.Binary.to;
        from = plfa.part1.Binary.from;
        from∘to = plfa.part1.Binary.from-to
    }

-- import Function using (_∘_)
-- import Function.Inverse using (_↔_)
-- import Function.LeftInverse using (_↞_)
