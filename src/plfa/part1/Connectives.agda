module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where
    ⟨_,_⟩ : A → B → A × B

proj₁ : {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

η-× : {A B : Set} → (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

record _×′_ (A B : Set) : Set where -- inductive records enjoy η-expansion (note η-expansion is dual to β-reduction)
    constructor ⟨_,_⟩′
    field
        proj₁′ : A
        proj₂′ : B
open _×′_

η-×′ : {A B : Set} → (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl

data Empty : Set where

data Unit : Set where
    unit : Unit

η-unit : (w : Unit) → unit ≡ w
η-unit unit = refl -- no eta-expansion here, need pattern matching to prove eta-expansion

record Unit′ : Set where
    constructor unit′

η-unit′ : (w : Unit′) → unit′ ≡ w
η-unit′ x = refl -- enjoy eta-expansion here

data _¹ (A : Set) : Set where
    ⟨_⟩ : A → A ¹

proj : {A : Set} → A ¹ → A
proj ⟨ x ⟩ = x

η-¹ : {A : Set} → (w : A ¹) → ⟨ proj w ⟩ ≡ w
η-¹ ⟨ x ⟩ = refl -- no eta-expansion here, need pattern matching to prove eta-expansion

record _¹′ (A : Set) : Set where
    constructor ⟨_⟩′
    field
        proj′ : A
open _¹′

η-¹′ : {A : Set} → (w : A ¹′) → ⟨ proj′ w ⟩′ ≡ w
η-¹′ w = refl -- enjoy eta-expansion here

data Bool : Set where
    false : Bool
    true : Bool

data Color : Set where
    red : Color
    green : Color
    blue : Color

×-count : Bool × Color → ℕ
×-count ⟨ false , red ⟩ = 1
×-count ⟨ false , green ⟩ = 2
×-count ⟨ false , blue ⟩ = 3
×-count ⟨ true , red ⟩ = 4
×-count ⟨ true , green ⟩ = 5
×-count ⟨ true , blue ⟩ = 6

×-comm : {A B : Set} → A × B ≃ B × A
×-comm =
    record {
        to = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ };
        from = λ { ⟨ y , x ⟩ → ⟨ x , y ⟩ };
        from∘to = λ { ⟨ x , y ⟩ → refl };
        to∘from = λ { ⟨ y , x ⟩ → refl }
    }

×-assoc : {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
    record {
        to = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ };
        from = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ };
        from∘to = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → refl };
        to∘from = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

open _≃_

⇔≃× : {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× .to A⇔B = ⟨ A⇔B ._⇔_.to , A⇔B ._⇔_.from ⟩
⇔≃× .from w = record { to = proj₁ w ; from = proj₂ w }
⇔≃× .from∘to _ = refl
⇔≃× .to∘from w = η-× w

test : {A B : Set} → (f : A → B) → (λ x → f x) ≡ f
test f = refl

-- Truth is Unit

data ⊤ : Set where
    tt : ⊤

η-⊤ : (w : ⊤) → tt ≡ w
η-⊤ tt = refl

record ⊤′ : Set where
    constructor tt′

η-⊤′ : (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

truth′ : ⊤′
truth′ = _

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : {A : Set} → ⊤ × A ≃ A
⊤-identityˡ .to ⟨ tt , x ⟩ = x
⊤-identityˡ .from x = ⟨ tt , x ⟩
⊤-identityˡ .from∘to ⟨ tt , x ⟩ = refl
⊤-identityˡ .to∘from x = refl

⊤-identityʳ : {A : Set} → A × ⊤ ≃ A
⊤-identityʳ {A} = 
    begin≃
        (A × ⊤)
    ≃⟨ ×-comm ⟩
        (⊤ × A)
    ≃⟨ ⊤-identityˡ ⟩
        A
    ≃∎

data _+_ (A B : Set) : Set where
    inj₁ : A → A + B
    inj₂ : B → A + B

infixr 1 _+_

_ : ℕ + ℕ × ℕ
_ = inj₂ ⟨ 1 , 2 ⟩

case-+ : {A B C : Set} → (A → C) → (B → C) → (A + B → C)
case-+ f g (inj₁ x) = f x
case-+ f g (inj₂ y) = g y

η-+ : {A B : Set} → (w : A + B) → case-+ inj₁ inj₂ w ≡ w
η-+ (inj₁ _) = refl
η-+ (inj₂ _) = refl

uniq-+ : {A B C : Set} → (h : A + B → C) → (w : A + B)
    → case-+ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-+ h (inj₁ _) = refl
uniq-+ h (inj₂ _) = refl

+-count : Bool + Color → ℕ
+-count (inj₁ false) = 1
+-count (inj₁ true) = 2
+-count (inj₂ red) = 3
+-count (inj₂ green) = 4
+-count (inj₂ blue) = 5

+-comm : {A B : Set} → A + B ≃ B + A
+-comm =
    record {
        to = λ {
            (inj₁ x) → inj₂ x;
            (inj₂ y) → inj₁ y
        };
        from = λ {
            (inj₁ y) → inj₂ y;
            (inj₂ x) → inj₁ x
        };
        from∘to = λ {
            (inj₁ x) → refl;
            (inj₂ y) → refl
        };
        to∘from = λ {
            (inj₁ y) → refl;
            (inj₂ x) → refl
        }
    }

+-assoc : {A B C : Set} → (A + B) + C ≃ A + (B + C)
+-assoc .to (inj₁ (inj₁ x)) = inj₁ x
+-assoc .to (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
+-assoc .to (inj₂ z) = inj₂ (inj₂ z)
+-assoc .from (inj₁ x) = inj₁ (inj₁ x)
+-assoc .from (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
+-assoc .from (inj₂ (inj₂ z)) = inj₂ z
+-assoc .from∘to (inj₁ (inj₁ x)) = refl
+-assoc .from∘to (inj₁ (inj₂ y)) = refl
+-assoc .from∘to (inj₂ z) = refl
+-assoc .to∘from (inj₁ x) = refl
+-assoc .to∘from (inj₂ (inj₁ y)) = refl
+-assoc .to∘from (inj₂ (inj₂ z)) = refl

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : {C : Set} → (h : ⊥ → C) → (w : ⊥)
    → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : {A : Set} → ⊥ + A ≃ A
to ⊥-identityˡ (inj₂ x) = x
from ⊥-identityˡ x = inj₂ x
from∘to ⊥-identityˡ (inj₂ _) = refl
to∘from ⊥-identityˡ _ = refl

⊥-identityʳ : {A : Set} → A + ⊥ ≃ A
to ⊥-identityʳ (inj₁ x) = x
from ⊥-identityʳ x = inj₁ x
from∘to ⊥-identityʳ (inj₁ _) = refl
to∘from ⊥-identityʳ _ = refl

→-elim : {A B : Set} → (A → B) → A → B
→-elim f x = f x

η-→ : {A B : Set} → (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool → Color) → ℕ
→-count f with f false | f true
... | red | red = 1
... | red | green = 2
... | red | blue = 3
... | green | red = 4
... | green | green = 5
... | green | blue = 6
... | blue | red = 7
... | blue | green = 8
... | blue | blue = 9

currying : {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying .to f ⟨ x , y ⟩ = f x y
currying .from g x y = g ⟨ x , y ⟩
currying .from∘to f = refl
currying .to∘from g = extensionality (λ { ⟨ x , y ⟩ → refl })

currying′ : {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying′ =
    record {
        to = λ { f → λ { ⟨ x , y ⟩ → f x y } };
        from = λ { g → λ { x → λ { y → g ⟨ x , y ⟩ } }};
        from∘to = λ { f → refl };
        to∘from = λ { g → extensionality λ { ⟨ x , y ⟩ → refl } }
    }

→-distrib-+ : {A B C : Set} → (A + B → C) ≃ (A → C) × (B → C)
→-distrib-+ =
    record {
        to = λ { f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ };
        from = λ { ⟨ g , h ⟩ → λ { (inj₁ x) → g x; (inj₂ y) → h y } };
        from∘to = λ { f → extensionality λ { (inj₁ x) → refl; (inj₂ x) → refl } };
        to∘from = λ { ⟨ g , h ⟩ → refl }
    }

ind-+ : {A B : Set} → {C : A + B → Set}
    → ((x : A) → C (inj₁ x))
    → ((y : B) → C (inj₂ y))
    → ((w : A + B) → C w)
ind-+ f g (inj₁ x) = f x
ind-+ f g (inj₂ y) = g y

rec-+ : {A B C : Set} → (A → C) → (B → C) → (A + B → C)
rec-+ = ind-+

test1 : {A B : Set} → A + B → ℕ
test1 = λ w → rec-+ (λ x → 1) (λ y → 2) w

ind-ℕ : {C : ℕ → Set}
    → (C zero)
    → ((n : ℕ) → C n → C (suc n))
    → ((n : ℕ) → C n)
ind-ℕ z s zero = z
ind-ℕ z s (suc n) = s n (ind-ℕ z s n)

rec-ℕ : {C : Set} → C → (ℕ → C → C) → (ℕ → C)
rec-ℕ = ind-ℕ

ind-Unit : {C : Unit → Set}
    → C unit
    → (w : Unit) → C w
ind-Unit u unit = u

rec-Unit : {C : Set} → C → Unit → C
rec-Unit = ind-Unit

ind-Empty : {C : Empty → Set}
    → (w : Empty) → C w
ind-Empty ()

rec-Empty : {C : Set} → Empty → C
rec-Empty = ind-Empty

ind-Bool : {C : Bool → Set}
    → C false
    → C true
    → (w : Bool) → C w
ind-Bool f t false = f
ind-Bool f t true = t

rec-Bool : {C : Set} → C → C → Bool → C
rec-Bool = ind-Bool

→-distrib-× : {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
    record {
        to = λ { f → ⟨ (proj₁ ∘ f) , proj₂ ∘ f ⟩ };
        from = λ { ⟨ g , h ⟩ → λ { x → ⟨ g x , h x ⟩ } };
        from∘to = λ { f → extensionality λ { x → η-× (f x) } };
        to∘from = λ { ⟨ g , h ⟩ → refl }
    }

×-distrib-+ : {A B C : Set} → (A + B) × C ≃ (A × C) + (B × C)
×-distrib-+ .to ⟨ inj₁ x , z ⟩ = inj₁ ⟨ x , z ⟩
×-distrib-+ .to ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩
×-distrib-+ .from (inj₁ ⟨ x , z ⟩) = ⟨ inj₁ x , z ⟩
×-distrib-+ .from (inj₂ ⟨ y , z ⟩) = ⟨ inj₂ y , z ⟩
×-distrib-+ .from∘to ⟨ inj₁ x , z ⟩ = refl
×-distrib-+ .from∘to ⟨ inj₂ y , z ⟩ = refl
×-distrib-+ .to∘from (inj₁ ⟨ x , z ⟩) = refl
×-distrib-+ .to∘from (inj₂ ⟨ y , z ⟩) = refl

+-distrib-× : {A B C : Set} → (A × B) + C ≲ (A + C) × (B + C)
+-distrib-× =
    record {
        to = λ {
            (inj₁ ⟨ x , y ⟩) → ⟨ (inj₁ x) , (inj₁ y) ⟩;
            (inj₂ z) → ⟨ inj₂ z , inj₂ z ⟩
        };
        from = λ {
            ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩;
            ⟨ inj₁ x , inj₂ z ⟩ → inj₂ z;
            ⟨ inj₂ z , _ ⟩ → inj₂ z -- note the second component is discarded
        };
        from∘to = λ {
            (inj₁ ⟨ x , y ⟩) → refl;
            (inj₂ z) → refl
        }
    }

+-weak-× : {A B C : Set} → (A + B) × C → A + (B × C)
+-weak-× ⟨ inj₁ x , z ⟩ = inj₁ x
+-weak-× ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩

+×-implies-×+ : {A B C D : Set} → (A × B) + (C × D) → (A + C) × (B + D) -- converse does not hold, try (A,B,C,D) = (Empty,Unit,Unit,Empty)
+×-implies-×+ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
+×-implies-×+ (inj₂ ⟨ z , w ⟩) = ⟨ inj₂ z , inj₂ w ⟩

-- import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
-- import Data.Unit using (⊤; tt)
-- import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
-- import Data.Empty using (⊥; ⊥-elim)
-- import Function.Equivalence using (_⇔_)
