{-# OPTIONS --without-K #-}

module plfa.part1.Connectives where

open import Agda.Primitive

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _+_)
open import Function using (id; _∘_)

open import plfa.part1.Isomorphism using (_≅_; _≲_; extensionality; Π-extensionality; _⇔_)
open plfa.part1.Isomorphism.≅-Reasoning

private
    variable
        i j k l : Level

data _×′_ (A : Set i) (B : Set j) : Set (i ⊔ j) where
    _,′_ : A → B → A ×′ B
infixr 2 _×′_

proj₁′ : {A : Set i} → {B : Set j} → A ×′ B → A
proj₁′ (x ,′ y) = x

proj₂′ : {A : Set i} → {B : Set j} → A ×′ B → B
proj₂′ (x ,′ y) = y

η-×′ : {A : Set i} → {B : Set j} → (w : A ×′ B) → (proj₁′ w ,′ proj₂′ w) ≡ w
η-×′ (x ,′ y) = refl

record _×″_ (A : Set i) (B : Set j) : Set (i ⊔ j) where -- inductive records enjoy η-expansion (note η-expansion is dual to β-reduction)
    constructor _,″_
    field
        proj₁″ : A
        proj₂″ : B
open _×″_

η-×″ : {A : Set i} → {B : Set j} → (w : A ×″ B) → (proj₁″ w ,″ proj₂″ w) ≡ w
η-×″ w = refl

η-× : {A : Set i} → {B : Set j} → (w : A × B) → (proj₁ w , proj₂ w) ≡ w
η-× w = refl

data Empty {i} : Set i where

data Unit {i} : Set i where
    unit : Unit

η-unit : (w : Unit {i}) → unit ≡ w
η-unit unit = refl -- no eta-expansion here, need pattern matching to prove eta-expansion

record Unit′ : Set i where
    constructor unit′

η-unit′ : (w : Unit′ {i}) → unit′ ≡ w
η-unit′ x = refl -- enjoy eta-expansion here

data _¹ (A : Set i) : Set i where
    _, : A → A ¹

proj : {A : Set i} → A ¹ → A
proj (x ,) = x

η-¹ : {A : Set i} → (w : A ¹) → proj w , ≡ w
η-¹ (x ,) = refl -- no eta-expansion here, need pattern matching to prove eta-expansion

record _¹′ (A : Set i) : Set i where
    constructor _,′
    field
        proj′ : A
open _¹′

η-¹′ : {A : Set i} → (w : A ¹′) → proj′ w ,′ ≡ w
η-¹′ w = refl -- enjoy eta-expansion here

data Bool {i} : Set i where
    false : Bool
    true : Bool

data Color {i} : Set i where
    red : Color
    green : Color
    blue : Color

×-count : Bool {i} × Color {j} → ℕ
×-count (false , red) = 1
×-count (false , green) = 2
×-count (false , blue) = 3
×-count (true , red) = 4
×-count (true , green) = 5
×-count (true , blue) = 6

×-comm : {A : Set i} → {B : Set j} → A × B ≅ B × A
×-comm =
    record {
        to = λ { (x , y) → (y , x) };
        from = λ { (y , x) → (x , y) };
        from∘to = λ { (x , y) → refl };
        to∘from = λ { (y , x) → refl }
    }

×-assoc : {A : Set i} → {B : Set j} → {C : Set k}
    → (A × B) × C ≅ A × (B × C)
×-assoc =
    record {
        to = λ { ((x , y) , z) → (x , (y , z)) };
        from = λ { (x , (y , z)) → ((x , y) , z) };
        from∘to = λ { ((x , y) , z) → refl };
        to∘from = λ { (x , (y , z)) → refl }
    }

-- _×_ is a functor

_map-×_ : {A : Set i} → {B : Set j} → {C : Set k} → {D : Set l}
    → (A → B) → (C → D) → (A × C) → (B × D)
(f map-× g) (x , y) = f x , g y

open _≅_

⇔≅× : {A : Set i} → {B : Set j} → A ⇔ B ≅ (A → B) × (B → A)
⇔≅× .to A⇔B = (A⇔B ._⇔_.to , A⇔B ._⇔_.from)
⇔≅× .from w = record { to = proj₁ w ; from = proj₂ w }
⇔≅× .from∘to _ = refl
⇔≅× .to∘from w = η-× w

eta : {A : Set i} → {B : A → Set j} → (f : (x : A) → B x) → (λ x → f x) ≡ f
eta f = refl

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

⊤-identityˡ : {A : Set i} → ⊤ × A ≅ A
⊤-identityˡ .to (tt , x) = x
⊤-identityˡ .from x = (tt , x)
⊤-identityˡ .from∘to (tt , x) = refl
⊤-identityˡ .to∘from x = refl

⊤-identityʳ : {A : Set i} → A × ⊤ ≅ A
⊤-identityʳ {A = A} = 
    begin≅
        (A × ⊤)
    ≅⟨ ×-comm ⟩
        (⊤ × A)
    ≅⟨ ⊤-identityˡ ⟩
        A
    ≅∎

-- data _+_ (A : Set i) (B : Set j) : Set (i ⊔ j) where
--     inj₁ : A → A + B
--     inj₂ : B → A + B
-- infixr 1 _+_

_ : ℕ + ℕ × ℕ
_ = inj₂ (1 , 2)

case-+ : {A : Set i} → {B : Set j} → {C : Set k} → (A → C) → (B → C) → (A + B → C)
case-+ f g (inj₁ x) = f x
case-+ f g (inj₂ y) = g y

η-+ : {A : Set i} → {B : Set j} → (w : A + B) → case-+ inj₁ inj₂ w ≡ w
η-+ (inj₁ _) = refl
η-+ (inj₂ _) = refl

uniq-+ : {A : Set i} → {B : Set j} → {C : Set k} → (h : A + B → C) → (w : A + B)
    → case-+ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-+ h (inj₁ _) = refl
uniq-+ h (inj₂ _) = refl

+-count : Bool {i} + Color {j} → ℕ
+-count (inj₁ false) = 1
+-count (inj₁ true) = 2
+-count (inj₂ red) = 3
+-count (inj₂ green) = 4
+-count (inj₂ blue) = 5

+-comm : {A : Set i} → {B : Set j} → A + B ≅ B + A
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

+-assoc : {A : Set i} → {B : Set j} → {C : Set k}
    → (A + B) + C ≅ A + (B + C)
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

_map-+_ : {A : Set i} → {B : Set j} → {C : Set k} → {D : Set l}
    → (A → B) → (C → D) → (A + C) → (B + D)
(f map-+ g) (inj₁ x) = inj₁ (f x)
(f map-+ g) (inj₂ y) = inj₂ (g y)

inj₁-injective : {A : Set i} → {B : Set j}
    → {x y : A} → inj₁ {A = A} {B = B} x ≡ inj₁ {A = A} {B = B} y → x ≡ y
inj₁-injective refl = refl

inj₂-injective : {A : Set i} → {B : Set j}
    → {x y : B} → inj₂ {A = A} {B = B} x ≡ inj₂ {A = A} {B = B} y → x ≡ y
inj₂-injective refl = refl

data ⊥ : Set where

⊥-elim : {A : Set i} → ⊥ → A
⊥-elim ()

uniq-⊥ : {C : Set i} → (h : ⊥ → C) → (w : ⊥)
    → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : {A : Set i} → ⊥ + A ≅ A
to ⊥-identityˡ (inj₂ x) = x
from ⊥-identityˡ x = inj₂ x
from∘to ⊥-identityˡ (inj₂ _) = refl
to∘from ⊥-identityˡ _ = refl

⊥-identityʳ : {A : Set i} → A + ⊥ ≅ A
to ⊥-identityʳ (inj₁ x) = x
from ⊥-identityʳ x = inj₁ x
from∘to ⊥-identityʳ (inj₁ _) = refl
to∘from ⊥-identityʳ _ = refl

→-elim : {A : Set i} → {B : Set j} → (A → B) → A → B
→-elim f x = f x

η-→ : {A : Set i} → {B : Set j} → (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool {i} → Color {j}) → ℕ
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

currying : {A : Set i} → {B : Set j} → {C : Set k}
    → (A → B → C) ≅ (A × B → C)
currying .to f (x , y) = f x y
currying .from g x y = g (x , y)
currying .from∘to f = refl
currying .to∘from g = extensionality (λ { (x , y) → refl })

currying′ : {A : Set i} → {B : Set j} → {C : Set k}
    → (A → B → C) ≅ (A × B → C)
currying′ =
    record {
        to = λ { f → λ { (x , y) → f x y } };
        from = λ { g → λ { x → λ { y → g (x , y) } }};
        from∘to = λ { f → refl };
        to∘from = λ { g → extensionality λ { (x , y) → refl } }
    }

→-distrib-+ : {A : Set i} → {B : Set j} → {C : Set k}
    → (A + B → C) ≅ (A → C) × (B → C)
→-distrib-+ =
    record {
        to = λ { f → (f ∘ inj₁ , f ∘ inj₂) };
        from = λ { (g , h) → λ { (inj₁ x) → g x; (inj₂ y) → h y } };
        from∘to = λ { f → extensionality λ { (inj₁ x) → refl; (inj₂ x) → refl } };
        to∘from = λ { (g , h) → refl }
    }

ind-+ : {A : Set i} → {B : Set j} → {C : A + B → Set k}
    → ((x : A) → C (inj₁ x))
    → ((y : B) → C (inj₂ y))
    → ((w : A + B) → C w)
ind-+ f g (inj₁ x) = f x
ind-+ f g (inj₂ y) = g y

rec-+ : {A : Set i} → {B : Set j} → {C : Set k}
    → (A → C) → (B → C) → (A + B → C)
rec-+ = ind-+

rec-+-test : {A : Set i} → {B : Set j} → A + B → ℕ
rec-+-test = λ w → rec-+ (λ x → 1) (λ y → 2) w

ind-ℕ : {P : ℕ → Set i}
    → (P zero)
    → ((n : ℕ) → P n → P (suc n))
    → ((n : ℕ) → P n)
ind-ℕ pz ps zero = pz
ind-ℕ pz ps (suc n) = ps n (ind-ℕ pz ps n)

ind-Unit : {C : Unit {i} → Set j}
    → C unit
    → (w : Unit) → C w
ind-Unit u unit = u

rec-Unit : {C : Set i} → C → Unit {j} → C
rec-Unit = ind-Unit

ind-Empty : {C : Empty {i} → Set j}
    → (w : Empty) → C w
ind-Empty ()

rec-Empty : {C : Set i} → Empty {j} → C
rec-Empty = ind-Empty

ind-Bool : {C : Bool {i} → Set j}
    → C false
    → C true
    → (w : Bool) → C w
ind-Bool f t false = f
ind-Bool f t true = t

rec-Bool : {C : Set i} → C → C → Bool {j} → C
rec-Bool = ind-Bool

→-distrib-× : {A : Set i} → {B : Set j} → {C : Set k}
    → (A → B × C) ≅ (A → B) × (A → C)
→-distrib-× =
    record {
        to = λ { f → ((proj₁ ∘ f) , proj₂ ∘ f) };
        from = λ { (g , h) → λ { x → (g x , h x) } };
        from∘to = λ { f → extensionality λ { x → η-× (f x) } };
        to∘from = λ { (g , h) → refl }
    }

×-distrib-+ : {A : Set i} → {B : Set j} → {C : Set k}
    → (A + B) × C ≅ (A × C) + (B × C)
×-distrib-+ .to (inj₁ x , z) = inj₁ (x , z)
×-distrib-+ .to (inj₂ y , z) = inj₂ (y , z)
×-distrib-+ .from (inj₁ (x , z)) = (inj₁ x , z)
×-distrib-+ .from (inj₂ (y , z)) = (inj₂ y , z)
×-distrib-+ .from∘to (inj₁ x , z) = refl
×-distrib-+ .from∘to (inj₂ y , z) = refl
×-distrib-+ .to∘from (inj₁ (x , z)) = refl
×-distrib-+ .to∘from (inj₂ (y , z)) = refl

+-distrib-× : {A : Set i} → {B : Set j} → {C : Set k}
    → (A × B) + C ≲ (A + C) × (B + C)
+-distrib-× =
    record {
        to = λ {
            (inj₁ (x , y)) → ((inj₁ x) , (inj₁ y));
            (inj₂ z) → (inj₂ z , inj₂ z)
        };
        from = λ {
            (inj₁ x , inj₁ y) → inj₁ (x , y);
            (inj₁ x , inj₂ z) → inj₂ z;
            (inj₂ z , _) → inj₂ z -- note the second component is discarded
        };
        from∘to = λ {
            (inj₁ (x , y)) → refl;
            (inj₂ z) → refl
        }
    }

+-weak-× : {A : Set i} → {B : Set j} → {C : Set k}
    → (A + B) × C → A + (B × C)
+-weak-× (inj₁ x , z) = inj₁ x
+-weak-× (inj₂ y , z) = inj₂ (y , z)

+×-implies-×+ : {A : Set i} → {B : Set j} → {C : Set k} → {D : Set l}
    → (A × B) + (C × D) → (A + C) × (B + D) -- The converse does not hold, try (A,B,C,D) = (Empty,Unit,Unit,Empty)
+×-implies-×+ (inj₁ (x , y)) = (inj₁ x , inj₁ y)
+×-implies-×+ (inj₂ (z , w)) = (inj₂ z , inj₂ w)

_ : (⊥ + ⊤) × (⊤ + ⊥) ≅ ⊤
_ = record {
        to = λ { _ → tt };
        from = λ { _ → inj₂ tt , inj₁ tt };
        from∘to = λ { (inj₂ tt , inj₁ tt) → refl };
        to∘from = λ { tt → refl }
    }

_ : (⊥ × ⊤) + (⊤ × ⊥) ≅ ⊥
_ = record {
        to = λ { (inj₁ ()); (inj₂ ()) };
        from = λ ();
        from∘to = λ { (inj₁ ()); (inj₂ ()) };
        to∘from = λ ()
    }

-- import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
-- import Data.Unit using (⊤; tt)
-- import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
-- import Data.Empty using (⊥; ⊥-elim)
-- import Function.Equivalence using (_⇔_)
 