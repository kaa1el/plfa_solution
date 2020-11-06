module plfa.part1.Equality where

-- Equality

data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- Congruence and Substitution

cong : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} → (f : A → B → C) → {x u : A} → {y v : B}
    → x ≡ u → y ≡ v → f x y ≡ f u v
cong₂ f refl refl = refl

cong-app : {A B : Set} → {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl

subst : {A : Set} → {x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl a = a

subst-cong : {A B : Set} → {f : A → B} → (P : B → Set) → {x y : A} → {u : P (f x)} → (e : x ≡ y)
    → subst (λ x → P (f x)) e u ≡ subst P (cong f e) u
subst-cong P refl = refl

congd : {A : Set} → {B : A → Set} → (f : (x : A) → B x) → {x y : A} → (e : x ≡ y) → subst B e (f x) ≡ f y
congd f refl = refl

trans-identity-l : {A : Set} → {x y : A} → (p : x ≡ y) → trans refl p ≡ p
trans-identity-l refl = refl

trans-identity-r : {A : Set} → {x y : A} → (p : x ≡ y) → trans p refl ≡ p
trans-identity-r refl = refl

trans-sym-l : {A : Set} → {x y : A} → (p : x ≡ y) → trans (sym p) p ≡ refl
trans-sym-l refl = refl

trans-sym-r : {A : Set} → {x y : A} → (p : x ≡ y) → trans p (sym p) ≡ refl
trans-sym-r refl = refl

sym-involution : {A : Set} → {x y : A} → (p : x ≡ y) → sym (sym p) ≡ p
sym-involution refl = refl

trans-assoc : {A : Set} → {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w)
    → trans (trans p q) r ≡ trans p (trans q r)
trans-assoc refl refl refl = refl

id : {A : Set} → A → A
id x = x

cong-trans : {A B : Set} → {f : A → B} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
    → cong f (trans p q) ≡ trans (cong f p) (cong f q)
cong-trans refl refl = refl

cong-sym : {A B : Set} → {f : A → B} → {x y : A} → (p : x ≡ y)
    → cong f (sym p) ≡ sym (cong f p)
cong-sym refl = refl

cong-cong : {A B C : Set} → {f : A → B} → {g : B → C} → {x y : A} → (p : x ≡ y)
    → cong g (cong f p) ≡ cong (λ x → g (f x)) p
cong-cong refl = refl

cong-id : {A : Set} → {x y : A} → (p : x ≡ y) → cong id p ≡ p
cong-id refl = refl

homotopy-natural : {A B : Set}
    → (f g : A → B) → (h : (x : A) → f x ≡ g x)
    → (x y : A) → (e : x ≡ y)
    → trans (h x) (cong g e) ≡ trans (cong f e) (h y)
homotopy-natural f g h x .x refl = trans (trans-identity-r (h x)) (sym (trans-identity-l (h x)))

homotopy-natural-d : {A : Set} → {B : A → Set}
    → (f g : (x : A) → B x) → (h : (x : A) → f x ≡ g x)
    → (x y : A) → (e : x ≡ y)
    → trans (cong (subst B e) (h x)) (congd g e) ≡ trans (congd f e) (h y)
homotopy-natural-d f g h x .x refl = trans (cong (λ e → trans e refl) (cong-id (h x))) (trans (trans-identity-r (h x)) (sym (trans-identity-l (h x))))

H : {A : Set} → {x : A} → {D : (y : A) → x ≡ y → Set}
    → D x refl
    → (y : A) → (e : x ≡ y) → D y e
H d y refl = d

J : {A : Set} → {C : (x y : A) → x ≡ y → Set}
    → ((x : A) → C x x refl)
    → (x y : A) → (e : x ≡ y) → C x y e
J c x .x refl = c x

record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
        π₁ : A
        π₂ : B π₁
open Σ
infixr 4 _,_

lift : {A : Set} → {B : A → Set} → {a x : A} → (b : B a)→ (e : a ≡ x) → (a , b) ≡ (x , subst B e b)
lift {A} {B} {a} {x} b e = J {A} {λ (a x : A) (e : a ≡ x) → (b : B a) → (a , b) ≡ (x , subst B e b)}
    (λ x b → refl) a x e b
-- lift b refl = refl

lift-π₁ : {A : Set} → {B : A → Set} → {a x : A} → (b : B a)→ (e : a ≡ x) → cong π₁ (lift {A} {B} b e) ≡ e
lift-π₁ {A} {B} {a} {x} b e = J {A} {λ (a x : A) (e : a ≡ x) → (b : B a) → cong π₁ (lift {A} {B} b e) ≡ e}
    (λ x b → refl) a x e b
-- lift-π₁ b refl = refl

singleton : {A : Set} → (x : A) → Set
singleton {A} x = Σ A (λ y → x ≡ y)

lift-singleton : {A : Set} → {x y : A} → (e : x ≡ y) → (x , refl {A} {x}) ≡ (y , e)
lift-singleton {A} {x} {y} e = J {A} {λ (x y : A) (e : x ≡ y) → (x , refl {A} {x}) ≡ (y , e)}
    (λ x → refl) x y e

H-from-J : {A : Set} → {x : A} → {D : (y : A) → x ≡ y → Set}
    → D x refl
    → (y : A) → (e : x ≡ y) → D y e
H-from-J {A} {x} {D} d y e = subst D′ (lift-singleton e) d where
    D′ : singleton x → Set
    D′ w = D (π₁ w) (π₂ w)

H-from-J≡H : {A : Set} → {x : A} → {D : (y : A) → x ≡ y → Set}
    → (d : D x refl)
    → (y : A) → (e : x ≡ y)
    → H-from-J {A} {x} {D} d y e ≡ H {A} {x} {D} d y e
H-from-J≡H d y refl = refl

J-from-H : {A : Set} → {C : (x y : A) → x ≡ y → Set}
    → ((x : A) → C x x refl)
    → (x y : A) → (e : x ≡ y) → C x y e
J-from-H c x = H (c x)

J-from-H≡J : {A : Set} → {C : (x y : A) → x ≡ y → Set}
    → (c : (x : A) → C x x refl)
    → (x y : A) → (e : x ≡ y)
    → J-from-H {A} {C} c x y e ≡ J {A} {C} c x y e
J-from-H≡J c x .x refl = refl

-- Chains of Equations

module ≡-Reasoning {A : Set} where

    infix 1 begin_
    infixr 2 _≡⟨⟩_ _≡⟨_⟩_
    infix 3 _∎

    begin_ : {x y : A} → x ≡ y → x ≡ y
    begin x≡y = x≡y

    _≡⟨⟩_ : (x : A) → {y : A} → x ≡ y → x ≡ y
    x ≡⟨⟩ x≡y = x≡y

    _≡⟨_⟩_ : (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
    x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

    _∎ : (x : A) → x ≡ x
    x ∎ = refl

open ≡-Reasoning

trans′ : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′ {x = x} {y = y} {z = z} x≡y y≡z =
    begin
        x
    ≡⟨ x≡y ⟩
        y
    ≡⟨ y≡z ⟩
        z
    ∎

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

postulate
    +-identity : (m : ℕ) → m + zero ≡ m
    +-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
    begin
        m + zero
    ≡⟨ +-identity m ⟩
        m
    ≡⟨⟩
        zero + m
    ∎
+-comm m (suc n) =
    begin
        m + suc n
    ≡⟨ +-suc m n ⟩
        suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
        suc (n + m)
    ≡⟨⟩
        suc n + m
    ∎

data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {n m : ℕ} → n ≤ m → suc n ≤ suc m

infix 4 _≤_

≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

module ≤-Reasoning where

    infix 1 begin≤_
    infixr 2 _≤⟨⟩_ _≤⟨_⟩_
    infix 3 _≤∎

    begin≤_ : {x y : ℕ} → x ≤ y → x ≤ y
    begin≤ x≤y = x≤y

    _≤⟨⟩_ : (x : ℕ) → {y : ℕ} → x ≤ y → x ≤ y
    x ≤⟨⟩ x≤y = x≤y

    _≤⟨_⟩_ : (x : ℕ) → {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
    x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

    _≤∎ : (x : ℕ) → x ≤ x
    x ≤∎ = ≤-refl

open ≤-Reasoning

+-monoʳ-≤ : (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q =
    begin≤
        p
    ≤⟨ p≤q ⟩
        q
    ≤∎
+-monoʳ-≤ (suc n) p q p≤q =
    begin≤
        suc (n + p)
    ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
        suc (n + q)
    ≤∎

+-monoˡ-≤ : (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p =
    begin≤
        p + m
    ≤⟨ +-monoʳ-≤ p m n m≤n ⟩
        p + n
    ≤∎

+-mono-≤ : (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
    begin≤
        m + p
    ≤⟨ +-monoʳ-≤ m p q p≤q ⟩
        m + q
    ≤⟨ +-monoˡ-≤ m n q m≤n ⟩
        n + q
    ≤∎

-- Rewriting

data Even : ℕ → Set
data Odd : ℕ → Set
data Even where
    zero : Even zero
    suc : {n : ℕ} → Odd n → Even (suc n)
data Odd where
    suc : {n : ℕ} → Even n → Odd (suc n)

even-comm : (m n : ℕ) → Even (m + n) → Even (n + m)
even-comm m n e rewrite +-comm m n = e

-- Multiple Rewrites

+-comm′ : (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identity n = refl
+-comm′ (suc m) n
    rewrite +-suc n m
    | +-comm′ m n = refl

-- Rewriting Expanded

even-comm′ : (m n : ℕ) → Even (m + n) → Even (n + m)
even-comm′ m n e with m + n | +-comm m n -- how "with" works?
... | .(n + m) | refl = e
-- ... | _ | refl = e -- this also works!

test : {P : ℕ → Set} → (m n : ℕ) → P (m + n) → P (n + m)
test m n t with m + n | +-comm m n -- order matters!
-- test m n t | x | y = ? -- match y first to force x to be (n + m)
test m n t | .(n + m) | refl = t 

test2 : {P : ℕ → Set} → (m n : ℕ) → P (m + n) → P (n + m)
test2 m n t rewrite +-comm m n = t

even-comm″ : (m n : ℕ) → Even (m + n) → Even (n + m)
even-comm″ m n = subst Even (+-comm m n)

-- Leibniz Equality

_≐_ : {A : Set} → (x y : A) → Set₁
_≐_ {A} x y = (P : A → Set) → P x → P y

refl-≐ : {A : Set} → {x : A} → x ≐ x
refl-≐ P Px = Px

trans-≐ : {A : Set} → {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : {A : Set} → {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

sym-≐′ : {A : Set} → {x y : A} → x ≐ y → y ≐ x
sym-≐′ {x = x} {y = y} x≐y P = x≐y (λ z → P z → P x) (refl-≐ P)

≡-implies-≐ : {A : Set} → {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : {A : Set} → {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {x = x} {y = y} x≐y = x≐y (λ z → x ≡ z) refl

-- Universe Polymorphism

open import Level using (Level; _⊔_; Setω) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
    refl′ : x ≡′ x

sym′ : ∀ {ℓ} → {A : Set ℓ} {x y : A} → x ≡′ y → y ≡′ x -- ∀ x stands for (x : _)
sym′ refl′ = refl′

_≐′_ : ∀ {ℓ} → {A : Set ℓ} → (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = (P : A → Set ℓ) → P x → P y

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} → {B : Set ℓ₂} → {C : Set ℓ₃}
    → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
