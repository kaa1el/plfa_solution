module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _+_)
open import Function using (_∘_)

open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_; id)
open plfa.part1.Isomorphism.≃-Reasoning

data _×′_ (A B : Set) : Set where
    _,′_ : A → B → A ×′ B
infixr 2 _×′_

proj₁′ : {A B : Set} → A ×′ B → A
proj₁′ (x ,′ y) = x

proj₂′ : {A B : Set} → A ×′ B → B
proj₂′ (x ,′ y) = y

η-×′ : {A B : Set} → (w : A ×′ B) → (proj₁′ w ,′ proj₂′ w) ≡ w
η-×′ (x ,′ y) = refl

record _×″_ (A B : Set) : Set where -- inductive records enjoy η-expansion (note η-expansion is dual to β-reduction)
    constructor _,″_
    field
        proj₁″ : A
        proj₂″ : B
open _×″_

η-×″ : {A B : Set} → (w : A ×″ B) → (proj₁″ w ,″ proj₂″ w) ≡ w
η-×″ w = refl

η-× : {A B : Set} → (w : A × B) → (proj₁ w , proj₂ w) ≡ w
η-× w = refl

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
    _, : A → A ¹

proj : {A : Set} → A ¹ → A
proj (x ,) = x

η-¹ : {A : Set} → (w : A ¹) → proj w , ≡ w
η-¹ (x ,) = refl -- no eta-expansion here, need pattern matching to prove eta-expansion

record _¹′ (A : Set) : Set where
    constructor _,′
    field
        proj′ : A
open _¹′

η-¹′ : {A : Set} → (w : A ¹′) → proj′ w ,′ ≡ w
η-¹′ w = refl -- enjoy eta-expansion here

data Bool : Set where
    false : Bool
    true : Bool

data Color : Set where
    red : Color
    green : Color
    blue : Color

×-count : Bool × Color → ℕ
×-count (false , red) = 1
×-count (false , green) = 2
×-count (false , blue) = 3
×-count (true , red) = 4
×-count (true , green) = 5
×-count (true , blue) = 6

×-comm : {A B : Set} → A × B ≃ B × A
×-comm =
    record {
        to = λ { (x , y) → (y , x) };
        from = λ { (y , x) → (x , y) };
        from∘to = λ { (x , y) → refl };
        to∘from = λ { (y , x) → refl }
    }

×-assoc : {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
    record {
        to = λ { ((x , y) , z) → (x , (y , z)) };
        from = λ { (x , (y , z)) → ((x , y) , z) };
        from∘to = λ { ((x , y) , z) → refl };
        to∘from = λ { (x , (y , z)) → refl }
    }

open _≃_

⇔≃× : {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× .to A⇔B = (A⇔B ._⇔_.to , A⇔B ._⇔_.from)
⇔≃× .from w = record { to = proj₁ w ; from = proj₂ w }
⇔≃× .from∘to _ = refl
⇔≃× .to∘from w = η-× w

eta : {A B : Set} → (f : A → B) → (λ x → f x) ≡ f
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

⊤-identityˡ : {A : Set} → ⊤ × A ≃ A
⊤-identityˡ .to (tt , x) = x
⊤-identityˡ .from x = (tt , x)
⊤-identityˡ .from∘to (tt , x) = refl
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

-- data _+_ (A B : Set) : Set where
--     inj₁ : A → A + B
--     inj₂ : B → A + B
-- infixr 1 _+_

_ : ℕ + ℕ × ℕ
_ = inj₂ (1 , 2)

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
currying .to f (x , y) = f x y
currying .from g x y = g (x , y)
currying .from∘to f = refl
currying .to∘from g = extensionality (λ { (x , y) → refl })

currying′ : {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying′ =
    record {
        to = λ { f → λ { (x , y) → f x y } };
        from = λ { g → λ { x → λ { y → g (x , y) } }};
        from∘to = λ { f → refl };
        to∘from = λ { g → extensionality λ { (x , y) → refl } }
    }

→-distrib-+ : {A B C : Set} → (A + B → C) ≃ (A → C) × (B → C)
→-distrib-+ =
    record {
        to = λ { f → (f ∘ inj₁ , f ∘ inj₂) };
        from = λ { (g , h) → λ { (inj₁ x) → g x; (inj₂ y) → h y } };
        from∘to = λ { f → extensionality λ { (inj₁ x) → refl; (inj₂ x) → refl } };
        to∘from = λ { (g , h) → refl }
    }

ind-+ : {A B : Set} → {C : A + B → Set}
    → ((x : A) → C (inj₁ x))
    → ((y : B) → C (inj₂ y))
    → ((w : A + B) → C w)
ind-+ f g (inj₁ x) = f x
ind-+ f g (inj₂ y) = g y

rec-+ : {A B C : Set} → (A → C) → (B → C) → (A + B → C)
rec-+ = ind-+

rec-+-test : {A B : Set} → A + B → ℕ
rec-+-test = λ w → rec-+ (λ x → 1) (λ y → 2) w

ind-ℕ : {P : ℕ → Set} -- standard induction
    → (P zero)
    → ((n : ℕ) → P n → P (suc n))
    → ((n : ℕ) → P n)
ind-ℕ pz ps zero = pz
ind-ℕ pz ps (suc n) = ps n (ind-ℕ pz ps n)

ind-ℕ-η : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (f : (n : ℕ) → P n)
    → f zero ≡ pz
    → ((n : ℕ) → f (suc n) ≡ ps n (f n))
    → ((n : ℕ) → f n ≡ ind-ℕ pz ps n)
ind-ℕ-η pz ps f ez es = ind-ℕ ez qs where
    qs : (n : ℕ) → f n ≡ ind-ℕ pz ps n → f (suc n) ≡ ind-ℕ pz ps (suc n)
    qs n e = trans (es n) (cong (ps n) e)
-- ind-ℕ-η pz ps f ez es zero = ez
-- ind-ℕ-η pz ps f ez es (suc n) rewrite es n | ind-ℕ-η pz ps f ez es n = refl

rec-ℕ : {C : Set} → C → (ℕ → C → C) → (ℕ → C) -- standard recursion
rec-ℕ cz cs = ind-ℕ cz cs -- non-dependent version of standard induction
-- rec-ℕ cz cs zero = cz
-- rec-ℕ cz cs (suc n) = cs n (rec-ℕ cz cs n)

rec-ℕ-η : {C : Set} → (cz : C) → (cs : ℕ → C → C) → (f : ℕ → C)
    → f zero ≡ cz
    → ((n : ℕ) → f (suc n) ≡ cs n (f n))
    → ((n : ℕ) → f n ≡ rec-ℕ cz cs n)
rec-ℕ-η = ind-ℕ-η
-- rec-ℕ-η cz cs f ez es = ind-ℕ ez qs where
--     qs : (n : ℕ) → f n ≡ rec-ℕ cz cs n → f (suc n) ≡ rec-ℕ cz cs (suc n)
--     qs n e = trans (es n) (cong (cs n) e)
-- rec-ℕ-η cz cs f ez es zero = ez
-- rec-ℕ-η cz cs f ez es (suc n) rewrite es n | rec-ℕ-η cz cs f ez es n = refl

r-ℕ : {X : Set} → X → (X → X) → (ℕ → X) -- categorical recursion (initial algebra)
r-ℕ xz xs = rec-ℕ xz (λ _ → xs)
-- r-ℕ xz xs zero = xz
-- r-ℕ xz xs (suc n) = xs (r-ℕ xz xs n)

r-ℕ-η : {X : Set} → (xz : X) → (xs : X → X) → (f : ℕ → X)
    → f zero ≡ xz
    → ((n : ℕ) → f (suc n) ≡ xs (f n))
    → ((n : ℕ) → f n ≡ r-ℕ xz xs n)
r-ℕ-η xz xs = rec-ℕ-η xz (λ _ → xs)
-- r-ℕ-η xz xs f ez es = ind-ℕ ez qs where
--     qs : (n : ℕ) → f n ≡ r-ℕ xz xs n → f (suc n) ≡ r-ℕ xz xs (suc n)
--     qs n e = trans (es n) (cong xs e)
-- r-ℕ-η xz xs f ez es zero = ez
-- r-ℕ-η xz xs f ez es (suc n) rewrite es n | r-ℕ-η xz xs f ez es n = refl

r-ℕ-η-βz : {X : Set} → (xz : X) → (xs : X → X) → (f : ℕ → X)
    → (ez : f zero ≡ xz)
    → (es : (n : ℕ) → f (suc n) ≡ xs (f n))
    → r-ℕ-η xz xs f ez es zero ≡ ez
r-ℕ-η-βz xz xs f ez es = refl

r-ℕ-η-βs : {X : Set} → (xz : X) → (xs : X → X) → (f : ℕ → X)
    → (ez : f zero ≡ xz)
    → (es : (n : ℕ) → f (suc n) ≡ xs (f n))
    → (n : ℕ) → r-ℕ-η xz xs f ez es (suc n) ≡ trans (es n) (cong xs (r-ℕ-η xz xs f ez es n))
r-ℕ-η-βs xz xs f ez es n = refl

r-ℕ-η-id : (n : ℕ) → r-ℕ 0 suc n ≡ n
r-ℕ-η-id n = sym (r-ℕ-η zero suc id refl (λ _ → refl) n)
-- r-ℕ-η-id zero = refl
-- r-ℕ-η-id (suc n) rewrite r-ℕ-η-id n = refl

rec-ℕ′-full : {C : Set} → C → (ℕ → C → C) → (ℕ → ℕ × C)
rec-ℕ′-full {C} cz cs n = r-ℕ {ℕ × C} xz xs n where
    xz : ℕ × C
    xz = (zero , cz)
    xs : ℕ × C → ℕ × C
    xs w = (suc (proj₁ w) , cs (proj₁ w) (proj₂ w))

rec-ℕ′-1 : {C : Set} → C → (ℕ → C → C) → (ℕ → ℕ)
rec-ℕ′-1 cz cs n = proj₁ (rec-ℕ′-full cz cs n)

rec-ℕ′-1-β : {C : Set} → (cz : C) → (cs : ℕ → C → C) → (n : ℕ) → rec-ℕ′-1 cz cs n ≡ n
rec-ℕ′-1-β cz cs n = trans (helper n) (r-ℕ-η-id n) where
    helper : (n : ℕ) → rec-ℕ′-1 cz cs n ≡ r-ℕ 0 suc n
    helper = r-ℕ-η zero suc (rec-ℕ′-1 cz cs) refl es where
        es : (n : ℕ) → rec-ℕ′-1 cz cs (suc n) ≡ suc (rec-ℕ′-1 cz cs n)
        es n = refl

rec-ℕ′ : {C : Set} → C → (ℕ → C → C) → (ℕ → C) -- standard recursion from categorical recursion
rec-ℕ′ cz cs n = proj₂ (rec-ℕ′-full cz cs n)

rec-ℕ′-βz : {C : Set} → (cz : C) → (cs : ℕ → C → C) → rec-ℕ′ cz cs zero ≡ cz
rec-ℕ′-βz cz cs = refl

rec-ℕ′-βs-test1 : {C : Set} → (cz : C) → (cs : ℕ → C → C) → rec-ℕ′ cz cs 1 ≡ cs 0 (rec-ℕ′ cz cs 0)
rec-ℕ′-βs-test1 cz cs = refl

rec-ℕ′-βs-test2 : {C : Set} → (cz : C) → (cs : ℕ → C → C) → rec-ℕ′ cz cs 2 ≡ cs 1 (rec-ℕ′ cz cs 1)
rec-ℕ′-βs-test2 cz cs = refl

rec-ℕ′-βs : {C : Set} → (cz : C) → (cs : ℕ → C → C) → (n : ℕ) → rec-ℕ′ cz cs (suc n) ≡ cs n (rec-ℕ′ cz cs n)
rec-ℕ′-βs {C} cz cs n = cong f (rec-ℕ′-1-β cz cs n) where
    f : ℕ → C
    f m = cs m (rec-ℕ′ cz cs n)
-- rewrite rec-ℕ′-1-β cz cs n = refl

rec-ℕ′≡rec-ℕ : {C : Set} → (cz : C) → (cs : ℕ → C → C) → (n : ℕ) → rec-ℕ′ cz cs n ≡ rec-ℕ cz cs n
rec-ℕ′≡rec-ℕ cz cs zero rewrite rec-ℕ′-βz cz cs = refl
rec-ℕ′≡rec-ℕ cz cs (suc n) rewrite rec-ℕ′-βs cz cs n | rec-ℕ′≡rec-ℕ cz cs n = refl

ind-ℕ′-full : {P : ℕ → Set}
    → P zero
    → ((n : ℕ) → P n → P (suc n))
    → ((n : ℕ) → Σ ℕ P)
ind-ℕ′-full {P} pz ps n = r-ℕ {Σ ℕ P} xz xs n where
    xz : Σ ℕ P
    xz = (zero , pz)
    xs : Σ ℕ P → Σ ℕ P
    xs w = (suc (proj₁ w) , ps (proj₁ w) (proj₂ w))

ind-ℕ′-1 : {P : ℕ → Set}
    → P zero
    → ((n : ℕ) → P n → P (suc n))
    → ((n : ℕ) → ℕ)
ind-ℕ′-1 pz ps n = proj₁ (ind-ℕ′-full pz ps n)

ind-ℕ′-1-β : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′-1 pz ps n ≡ n
ind-ℕ′-1-β pz ps n = trans (helper n) (r-ℕ-η-id n) where
    helper : (n : ℕ) → ind-ℕ′-1 pz ps n ≡ r-ℕ 0 suc n
    helper = r-ℕ-η zero suc (ind-ℕ′-1 pz ps) refl es where
        es : (n : ℕ) → ind-ℕ′-1 pz ps (suc n) ≡ suc (ind-ℕ′-1 pz ps n)
        es n = refl
-- ind-ℕ′-1-β pz ps n = trans (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) refl (λ _ → refl) n) (sym (r-ℕ-η zero suc id refl (λ _ → refl) n))

ind-ℕ′ : {P : ℕ → Set} -- standard induction from categorical recursion
    → P zero
    → ((n : ℕ) → P n → P (suc n))
    → ((n : ℕ) → P n)
ind-ℕ′ {P} pz ps n = subst P (ind-ℕ′-1-β pz ps n) (proj₂ (ind-ℕ′-full pz ps n))
-- ind-ℕ′ pz ps n rewrite sym (ind-ℕ′-1-β pz ps n) = proj₂ (ind-ℕ′-full pz ps n)

ind-ℕ′-βz : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → ind-ℕ′ pz ps zero ≡ pz
ind-ℕ′-βz pz ps = refl

ind-ℕ′-βs-test1 : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → ind-ℕ′ pz ps 1 ≡ ps 0 (ind-ℕ′ pz ps 0)
ind-ℕ′-βs-test1 pz ps = refl

ind-ℕ′-βs-test2 : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → ind-ℕ′ pz ps 2 ≡ ps 1 (ind-ℕ′ pz ps 1)
ind-ℕ′-βs-test2 pz ps = refl

congd : {A : Set} → {B : A → Set} → (f : (x : A) → B x) → {x y : A}
    → (e : x ≡ y)
    → subst B e (f x) ≡ f y
congd f refl = refl -- HoTT Book Lemma 2.3.4

curry : {A : Set} → {B : A → Set} → {C : Σ A B → Set}
    → (f : (w : Σ A B) → C w)
    → (x : A) → (y : B x) → C (x , y)
curry f x y = f (x , y)

uncurry : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set}
    → (f : (x : A) → (y : B x) → C x y)
    → (w : Σ A B) → C (proj₁ w) (proj₂ w)
uncurry f w = f (proj₁ w) (proj₂ w)

lift : {A : Set} → {B : A → Set} → {a x : A} → (b : B a) → (e : a ≡ x)
    → (a , b) ≡ (x , subst B e b)
lift b refl = refl -- HoTT Book Lemma 2.3.2

lift-proj₁ : {A : Set} → {B : A → Set} → {a x : A} → (b : B a)→ (e : a ≡ x)
    → cong proj₁ (lift {A} {B} b e) ≡ e
lift-proj₁ b refl = refl -- HoTT Book Lemma 2.3.2

subst-cong : {A B : Set} → {f : A → B} → (P : B → Set) → {x y : A} → {u : P (f x)} → (e : x ≡ y)
    → subst P (cong f e) u ≡ subst (λ x → P (f x)) e u -- this is HoTT Book Lemma 2.3.10
subst-cong P refl = refl

cong-trans : {A B : Set} → {f : A → B} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
    → cong f (trans p q) ≡ trans (cong f p) (cong f q)
cong-trans refl refl = refl

cong-sym : {A B : Set} → {f : A → B} → {x y : A} → (p : x ≡ y)
    → cong f (sym p) ≡ sym (cong f p)
cong-sym refl = refl

ind-ℕ′-1-β-βz : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → ind-ℕ′-1-β pz ps zero ≡ refl
ind-ℕ′-1-β-βz pz ps = refl

ind-ℕ′-1-β-βs : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′-1-β pz ps (suc n) ≡ cong suc (ind-ℕ′-1-β pz ps n)
ind-ℕ′-1-β-βs pz ps n =
    begin
        ind-ℕ′-1-β pz ps (suc n)
    ≡⟨⟩
        trans (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) refl (λ _ → refl) (suc n)) (sym (r-ℕ-η zero suc id refl (λ _ → refl) (suc n)))
    -- ≡⟨⟩ -- see r-ℕ-η-βs
    ≡⟨ cong (λ e → trans e (sym (r-ℕ-η zero suc id refl (λ _ → refl) (suc n)))) (r-ℕ-η-βs zero suc (ind-ℕ′-1 pz ps) refl (λ _ → refl) n) ⟩ -- r-ℕ-η-βs xz xs f ez es n
        trans (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) refl (λ _ → refl) n)) (sym (r-ℕ-η zero suc id refl (λ _ → refl) (suc n)))
    -- ≡⟨⟩ -- see r-ℕ-η-βs
    ≡⟨ cong (λ e → trans (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) refl (λ _ → refl) n)) (sym e)) (r-ℕ-η-βs zero suc id refl (λ _ → refl) n) ⟩
        trans (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) refl (λ _ → refl) n)) (sym (cong suc (r-ℕ-η zero suc id refl (λ _ → refl) n)))
    ≡⟨ cong (λ e → trans (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) refl (λ _ → refl) n)) e) (sym (cong-sym (r-ℕ-η zero suc id refl (λ _ → refl) n))) ⟩
        trans (cong suc (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) refl (λ _ → refl) n)) (cong suc (sym (r-ℕ-η zero suc id refl (λ _ → refl) n)))
    ≡⟨ sym (cong-trans (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) refl (λ _ → refl) n) (sym (r-ℕ-η zero suc id refl (λ _ → refl) n))) ⟩
        cong suc (trans (r-ℕ-η zero suc (ind-ℕ′-1 pz ps) refl (λ _ → refl) n) (sym (r-ℕ-η zero suc id refl (λ _ → refl) n)))
    ≡⟨⟩
        cong suc (ind-ℕ′-1-β pz ps n)
    ∎

ind-ℕ′-βs : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′ pz ps (suc n) ≡ ps n (ind-ℕ′ pz ps n)
ind-ℕ′-βs {P} pz ps n =
    begin
        ind-ℕ′ pz ps (suc n)
    ≡⟨⟩
        subst P (ind-ℕ′-1-β pz ps (suc n)) (ps (proj₁ (ind-ℕ′-full pz ps n)) (proj₂ (ind-ℕ′-full pz ps n)))
    ≡⟨⟩ -- use uncurry and η-rule for Σ
        subst P (ind-ℕ′-1-β pz ps (suc n)) (uncurry ps (ind-ℕ′-full pz ps n))
    ≡⟨ cong (λ e → subst P e (uncurry ps (ind-ℕ′-full pz ps n))) (ind-ℕ′-1-β-βs pz ps n) ⟩ -- key step: ind-ℕ′-1-β-βs
        subst P (cong suc (ind-ℕ′-1-β pz ps n)) (uncurry ps (ind-ℕ′-full pz ps n))
    ≡⟨ subst-cong P (ind-ℕ′-1-β pz ps n) ⟩ -- HoTT Book Lemma 2.3.10
        subst (λ n → P (suc n)) (ind-ℕ′-1-β pz ps n) (uncurry ps (ind-ℕ′-full pz ps n))
    ≡⟨ cong (λ e → subst (λ n → P (suc n)) e (uncurry ps (ind-ℕ′-full pz ps n))) (sym (lift-proj₁ (proj₂ (ind-ℕ′-full pz ps n)) (ind-ℕ′-1-β pz ps n))) ⟩ -- HoTT Book Lemma 2.3.2
        subst (λ n → P (suc n)) (cong proj₁ (lift (proj₂ (ind-ℕ′-full pz ps n)) (ind-ℕ′-1-β pz ps n))) (uncurry ps (ind-ℕ′-full pz ps n))
    ≡⟨ subst-cong (λ n → P (suc n)) (lift (proj₂ (ind-ℕ′-full pz ps n)) (ind-ℕ′-1-β pz ps n)) ⟩ -- HoTT Book Lemma 2.3.10
        subst (λ w → P (suc (proj₁ w))) (lift (proj₂ (ind-ℕ′-full pz ps n)) (ind-ℕ′-1-β pz ps n)) (uncurry ps (ind-ℕ′-full pz ps n))
    ≡⟨ congd (uncurry ps) (lift (proj₂ (ind-ℕ′-full pz ps n)) (ind-ℕ′-1-β pz ps n)) ⟩ -- HoTT Book Lemma 2.3.4
        uncurry ps (n , subst P (ind-ℕ′-1-β pz ps n) (proj₂ (ind-ℕ′-full pz ps n)))
    ≡⟨⟩
        ps n (subst P (ind-ℕ′-1-β pz ps n) (proj₂ (ind-ℕ′-full pz ps n)))
    ≡⟨⟩
        ps n (ind-ℕ′ pz ps n)
    ∎

ind-ℕ′≡ind-ℕ : {P : ℕ → Set}
    → (pz : P zero)
    → (ps : (n : ℕ) → P n → P (suc n))
    → (n : ℕ) → ind-ℕ′ pz ps n ≡ ind-ℕ pz ps n
ind-ℕ′≡ind-ℕ pz ps zero rewrite ind-ℕ′-βz pz ps = refl
ind-ℕ′≡ind-ℕ pz ps (suc n) rewrite ind-ℕ′-βs pz ps n | ind-ℕ′≡ind-ℕ pz ps n = refl

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
        to = λ { f → ((proj₁ ∘ f) , proj₂ ∘ f) };
        from = λ { (g , h) → λ { x → (g x , h x) } };
        from∘to = λ { f → extensionality λ { x → η-× (f x) } };
        to∘from = λ { (g , h) → refl }
    }

×-distrib-+ : {A B C : Set} → (A + B) × C ≃ (A × C) + (B × C)
×-distrib-+ .to (inj₁ x , z) = inj₁ (x , z)
×-distrib-+ .to (inj₂ y , z) = inj₂ (y , z)
×-distrib-+ .from (inj₁ (x , z)) = (inj₁ x , z)
×-distrib-+ .from (inj₂ (y , z)) = (inj₂ y , z)
×-distrib-+ .from∘to (inj₁ x , z) = refl
×-distrib-+ .from∘to (inj₂ y , z) = refl
×-distrib-+ .to∘from (inj₁ (x , z)) = refl
×-distrib-+ .to∘from (inj₂ (y , z)) = refl

+-distrib-× : {A B C : Set} → (A × B) + C ≲ (A + C) × (B + C)
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

+-weak-× : {A B C : Set} → (A + B) × C → A + (B × C)
+-weak-× (inj₁ x , z) = inj₁ x
+-weak-× (inj₂ y , z) = inj₂ (y , z)

+×-implies-×+ : {A B C D : Set} → (A × B) + (C × D) → (A + C) × (B + D) -- converse does not hold, try (A,B,C,D) = (Empty,Unit,Unit,Empty)
+×-implies-×+ (inj₁ (x , y)) = (inj₁ x , inj₁ y)
+×-implies-×+ (inj₂ (z , w)) = (inj₂ z , inj₂ w)

-- import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
-- import Data.Unit using (⊤; tt)
-- import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
-- import Data.Empty using (⊥; ⊥-elim)
-- import Function.Equivalence using (_⇔_)
