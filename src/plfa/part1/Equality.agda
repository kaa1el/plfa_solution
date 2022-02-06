{-# OPTIONS --without-K #-}

module plfa.part1.Equality where

open import Agda.Primitive

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Function using (id; _∘_)

private
    variable
        i j k l m n : Level

-- Equality

-- data _≡_ {A : Set} (x : A) : A → Set where
--     refl : x ≡ x

-- infix 4 _≡_

-- {-# BUILTIN EQUALITY _≡_ #-}

_ : {A : Set i} → {x : A} → x ≡ x
_ = refl

-- sym : {A : Set i} → {x y : A} → x ≡ y → y ≡ x -- HoTT Book Lemma 2.1.1
-- sym refl = refl

-- trans : {A : Set i} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z -- HoTT Book Lemma 2.1.2
-- trans refl refl = refl

-- Congruence and Substitution

-- cong : {A : Set i} → {B : Set j} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y -- HoTT Book Lemma 2.2.1, also called (ap)
-- cong f refl = refl

-- cong₂ : {A : Set i} → {B : Set j} → {C : Set k}
--     → (f : A → B → C) → {x₁ x₂ : A} → {y₁ y₂ : B}
--     → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
-- cong₂ f refl refl = refl

cong₃ : {A : Set i} → {B : Set j} → {C : Set k} → {D : Set l}
    → (f : A → B → C → D) → {x₁ x₂ : A} → {y₁ y₂ : B} → {z₁ z₂ : C}
    → x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
cong₃ f refl refl refl = refl

cong-app : {A : Set i} → {B : Set j}
    → {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl

cong-app-d : {A : Set i} → {B : A → Set j}
    → {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x -- HoTT Book Formula 2.9.2, also called (happly)
cong-app-d refl x = refl

-- subst : {A : Set i} → (P : A → Set j)
--     → {x y : A} → x ≡ y → P x → P y -- HoTT Book Lemma 2.3.1, also called (transport)
-- subst P refl a = a

subst-inv : {A : Set i} → (P : A → Set j)
    → {x y : A} → x ≡ y → P y → P x
subst-inv P refl a = a

subst-trans : {A : Set i} → (P : A → Set j)
    → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → {a : P x}
    → subst P (trans p q) a ≡ subst P q (subst P p a) -- HoTT Book Lemma 2.3.9
subst-trans P refl refl = refl

subst-sym : {A : Set i} → (P : A → Set j)
    → {x y : A} → (p : x ≡ y) → {v : P y}
    → subst P (sym p) v ≡ subst-inv P p v
subst-sym P refl = refl

subst-cong : {A : Set i} → {B : Set j} → (P : B → Set k)
    → {f : A → B} → {x y : A} → (e : x ≡ y) → {u : P (f x)}
    → subst P (cong f e) u ≡ subst (λ x → P (f x)) e u -- HoTT Book Lemma 2.3.10
subst-cong P refl = refl

subst₂ : {A : Set i} → {B : Set j} → (P : A → B → Set k)
    → {x₁ x₂ : A} → {y₁ y₂ : B}
    → x₁ ≡ x₂ → y₁ ≡ y₂ → P x₁ y₁ → P x₂ y₂
subst₂ P refl refl a = a

subst₂-d : {A : Set i} → {B : A → Set j} → (P : (x : A) → B x → Set k)
    → {x₁ x₂ : A} → {y₁ : B x₁} → {y₂ : B x₂}
    → (e₁ : x₁ ≡ x₂) → subst B e₁ y₁ ≡ y₂ → P x₁ y₁ → P x₂ y₂
subst₂-d P refl refl a = a

subst₃ : {A : Set i} → {B : Set j} → {C : Set k} → (P : A → B → C → Set l)
    → {x₁ x₂ : A} → {y₁ y₂ : B} → {z₁ z₂ : C}
    → x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → P x₁ y₁ z₁ → P x₂ y₂ z₂
subst₃ P refl refl refl a = a

subst₃-d : {A : Set i} → {B : A → Set j} → {C : (x : A) → B x → Set k} → (P : (x : A) → (y : B x) → C x y → Set l)
    → {x₁ x₂ : A} → {y₁ : B x₁} → {y₂ : B x₂} → {z₁ : C x₁ y₁} → {z₂ : C x₂ y₂}
    → (e₁ : x₁ ≡ x₂) → (e₂ : subst B e₁ y₁ ≡ y₂) → (e₃ : subst₂-d C e₁ e₂ z₁ ≡ z₂) → P x₁ y₁ z₁ → P x₂ y₂ z₂
subst₃-d P refl refl refl a = a

subst₃-d₂ : {A : Set i} → {B : Set j} → {C : A → B → Set k} → (P : (x : A) → (y : B) → C x y → Set l)
    → {x₁ x₂ : A} → {y₁ y₂ : B} → {z₁ : C x₁ y₁} → {z₂ : C x₂ y₂}
    → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → subst₂ C e₁ e₂ z₁ ≡ z₂ → P x₁ y₁ z₁ → P x₂ y₂ z₂
subst₃-d₂ P refl refl refl a = a

subst-cong₂ : {A : Set i} → {B : Set j} → {C : Set k} → (P : C → Set l)
    → {f : A → B → C} → {x₁ x₂ : A} → {y₁ y₂ : B}
    → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → {u : P (f x₁ y₁)}
    → subst P (cong₂ f e₁ e₂) u ≡ subst₂ (λ x y → P (f x y)) e₁ e₂ u
subst-cong₂ P refl refl = refl

subst-cong₃ : {A : Set i} → {B : Set j} → {C : Set k} → {D : Set l} → (P : D → Set m)
    → {f : A → B → C → D} → {x₁ x₂ : A} → {y₁ y₂ : B} → {z₁ z₂ : C}
    → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → (e₃ : z₁ ≡ z₂) → {u : P (f x₁ y₁ z₁)}
    → subst P (cong₃ f e₁ e₂ e₃) u ≡ subst₃ (λ x y z → P (f x y z)) e₁ e₂ e₃ u
subst-cong₃ P refl refl refl = refl

subst₂-downgrade : {A : Set i} → {B : Set j} → (P : A → B → Set k)
    → {x : A} → {y₁ y₂ : B}
    → (e : y₁ ≡ y₂) → {a : P x y₁}
    → subst₂ P refl e a ≡ subst (P x) e a
subst₂-downgrade P refl = refl

subst₃-d₂-downgrade : {A : Set i} → {B : Set j} → {C : A → B → Set k} → (P : (x : A) → (y : B) → C x y → Set l)
    → {x : A} → {y : B} → {z₁ : C x y} → {z₂ : C x y}
    → (e : z₁ ≡ z₂) → {a : P x y z₁}
    → subst₃-d₂ P refl refl e a ≡ subst (P x y) e a
subst₃-d₂-downgrade P refl = refl

subst-const : {A : Set i} → (P : Set j)
    → {x y : A} → (e : x ≡ y) → {a : P}
    → subst (λ _ → P) e a ≡ a
subst-const P refl = refl

subst₂-const-r : {A : Set i} → {B : Set j} → (P : A → Set k)
    → {x₁ x₂ : A} → {y₁ y₂ : B}
    → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → {u : P x₁}
    → subst₂ (λ x _ → P x) e₁ e₂ u ≡ subst P e₁ u
subst₂-const-r P refl refl = refl

subst₂-const-l : {A : Set i} → {B : Set j} → (P : B → Set k)
    → {x₁ x₂ : A} → {y₁ y₂ : B}
    → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → {v : P y₁}
    → subst₂ (λ _ y → P y) e₁ e₂ v ≡ subst P e₂ v
subst₂-const-l P refl refl = refl

subst₂-const : {A : Set i} → {B : Set j} → (P : Set k)
    → {x₁ x₂ : A} → {y₁ y₂ : B}
    → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → {a : P}
    → subst₂ (λ _ _ → P) e₁ e₂ a ≡ a
subst₂-const P refl refl = refl

subst₂-d-const : {A : Set i} → {B : A → Set j} → (P : Set k)
    → {x₁ x₂ : A} → {y₁ : B x₁} → {y₂ : B x₂}
    → (e₁ : x₁ ≡ x₂) → (e₂ : subst B e₁ y₁ ≡ y₂) → {a : P}
    → subst₂-d (λ _ _ → P) e₁ e₂ a ≡ a
subst₂-d-const P refl refl = refl

subst₃-d₂-const : {A : Set i} → {B : Set j} → {C : A → B → Set k} → (P : A → B → Set l)
    → {x₁ x₂ : A} → {y₁ y₂ : B} → {z₁ : C x₁ y₁} → {z₂ : C x₂ y₂}
    → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → (e₃ : subst₂ C e₁ e₂ z₁ ≡ z₂) → {a : P x₁ y₁}
    → subst₃-d₂ (λ x y _ → P x y) e₁ e₂ e₃ a ≡ subst₂ P e₁ e₂ a
subst₃-d₂-const P refl refl refl = refl

subst₂-trans : {A : Set i} → {B : Set j} → (P : A → B → Set k)
    → {x₁ x₂ x₃ : A} → {y₁ y₂ y₃ : B}
    → (e₁₁ : x₁ ≡ x₂) → (e₁₂ : x₂ ≡ x₃) → (e₂₁ : y₁ ≡ y₂) → (e₂₂ : y₂ ≡ y₃) → {a : P x₁ y₁}
    → subst₂ P (trans e₁₁ e₁₂) (trans e₂₁ e₂₂) a ≡ subst₂ P e₁₂ e₂₂ (subst₂ P e₁₁ e₂₁ a)
subst₂-trans P refl refl refl refl = refl

subst₂-d-trans : {A : Set i} → {B : A → Set j} → (P : (x : A) → B x → Set k)
    → {x₁ x₂ x₃ : A} → {y₁ : B x₁} → {y₂ : B x₂} → {y₃ : B x₃}
    → (e₁₁ : x₁ ≡ x₂) → (e₁₂ : x₂ ≡ x₃) → (e₂₁ : subst B e₁₁ y₁ ≡ y₂) → (e₂₂ : subst B e₁₂ y₂ ≡ y₃) → {a : P x₁ y₁}
    → subst₂-d P (trans e₁₁ e₁₂) (trans (trans (subst-trans B e₁₁ e₁₂) (cong (subst B e₁₂) e₂₁)) e₂₂) a ≡ subst₂-d P e₁₂ e₂₂ (subst₂-d P e₁₁ e₂₁ a)
subst₂-d-trans P refl refl refl refl = refl

subst₃-d-trans : {A : Set i} → {B : A → Set j} → {C : (x : A) → B x → Set k} → (P : (x : A) → (y : B x) → C x y → Set l)
    → {x₁ x₂ x₃ : A} → {y₁ : B x₁} → {y₂ : B x₂} → {y₃ : B x₃} → {z₁ : C x₁ y₁} → {z₂ : C x₂ y₂} → {z₃ : C x₃ y₃}
    → (e₁₁ : x₁ ≡ x₂) → (e₁₂ : x₂ ≡ x₃) → (e₂₁ : subst B e₁₁ y₁ ≡ y₂) → (e₂₂ : subst B e₁₂ y₂ ≡ y₃)
    → (e₃₁ : subst₂-d C e₁₁ e₂₁ z₁ ≡ z₂) → (e₃₂ : subst₂-d C e₁₂ e₂₂ z₂ ≡ z₃) → {a : P x₁ y₁ z₁}
    → subst₃-d P
        (trans e₁₁ e₁₂)
        (trans (trans (subst-trans B e₁₁ e₁₂) (cong (subst B e₁₂) e₂₁)) e₂₂)
        (trans (trans (subst₂-d-trans C e₁₁ e₁₂ e₂₁ e₂₂) (cong (subst₂-d C e₁₂ e₂₂) e₃₁)) e₃₂)
        a ≡ subst₃-d P e₁₂ e₂₂ e₃₂ (subst₃-d P e₁₁ e₂₁ e₃₁ a)
subst₃-d-trans P refl refl refl refl refl refl = refl

subst₃-d₂-trans : {A : Set i} → {B : Set j} → {C : A → B → Set k} → (P : (x : A) → (y : B) → C x y → Set l)
    → {x₁ x₂ x₃ : A} → {y₁ y₂ y₃ : B} → {z₁ : C x₁ y₁} → {z₂ : C x₂ y₂} → {z₃ : C x₃ y₃}
    → (e₁₁ : x₁ ≡ x₂) → (e₁₂ : x₂ ≡ x₃) → (e₂₁ : y₁ ≡ y₂) → (e₂₂ : y₂ ≡ y₃)
    → (e₃₁ : subst₂ C e₁₁ e₂₁ z₁ ≡ z₂) → (e₃₂ : subst₂ C e₁₂ e₂₂ z₂ ≡ z₃) → {a : P x₁ y₁ z₁}
    → subst₃-d₂ P
        (trans e₁₁ e₁₂)
        (trans e₂₁ e₂₂)
        (trans (trans (subst₂-trans C e₁₁ e₁₂ e₂₁ e₂₂) (cong (subst₂ C e₁₂ e₂₂) e₃₁)) e₃₂)
        a ≡ subst₃-d₂ P e₁₂ e₂₂ e₃₂ (subst₃-d₂ P e₁₁ e₂₁ e₃₁ a)
subst₃-d₂-trans P refl refl refl refl refl refl = refl

subst≡subst×subst : {A : Set i} → (P : A → Set j) → (Q : A → Set k)
    → {x₁ x₂ : A} → (e : x₁ ≡ x₂) → {u : P x₁} → {v : Q x₁}
    → subst (λ x → P x × Q x) e (u , v) ≡ (subst P e u , subst Q e v)
subst≡subst×subst P Q refl = refl

subst₂≡subst₂×subst₂ : {A : Set i} → {B : Set j} → (P : A → B → Set k) → (Q : A → B → Set l)
    → {x₁ x₂ : A} → {y₁ y₂ : B} → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → {u : P x₁ y₁} → {v : Q x₁ y₁}
    → subst₂ (λ x y → P x y × Q x y) e₁ e₂ (u , v) ≡ (subst₂ P e₁ e₂ u , subst₂ Q e₁ e₂ v)
subst₂≡subst₂×subst₂ P Q refl refl = refl

subst₂≡subst×subst : {A : Set i} → {B : Set j} → (P : A → Set k) → (Q : B → Set l)
    → {x₁ x₂ : A} → {y₁ y₂ : B} → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → {u : P x₁} → {v : Q y₁}
    → subst₂ (λ x y → P x × Q y) e₁ e₂ (u , v) ≡ (subst P e₁ u , subst Q e₂ v)
subst₂≡subst×subst P Q refl refl = refl
-- subst₂≡subst×subst P Q e₁ e₂ {u} {v} =
--     begin
--         subst₂ (λ x y → P x × Q y) e₁ e₂ (u , v)
--     ≡⟨ subst₂≡subst₂×subst₂ (λ x _ → P x) (λ _ y → Q y) e₁ e₂ ⟩
--         subst₂ (λ x _ → P x) e₁ e₂ u , subst₂ (λ _ y → Q y) e₁ e₂ v
--     ≡⟨ cong₂ _,_ (subst₂-const-r P e₁ e₂) (subst₂-const-l Q e₁ e₂) ⟩
--         subst P e₁ u , subst Q e₂ v
--     ∎

subst₂≡id×subst₂ : {A : Set i} → {B : Set j} → (P : Set k) → (Q : A → B → P → Set l)
    → {x₁ x₂ : A} → {y₁ y₂ : B} → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → {u : P} → {v : Q x₁ y₁ u}
    → subst₂ (λ x y → Σ P (λ z → Q x y z)) e₁ e₂ (u , v) ≡ (u , subst₂ (λ x y → Q x y u) e₁ e₂ v)
subst₂≡id×subst₂ P Q refl refl = refl

subst₂≡subst₂×subst₃-d₂ :{A : Set i} → {B : Set j} → (P : A → B → Set k) → (Q : (x : A) → (y : B) → P x y → Set l)
    → {x₁ x₂ : A} → {y₁ y₂ : B} → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → {u : P x₁ y₁} → {v : Q x₁ y₁ u}
    → subst₂ (λ x y → Σ (P x y) (λ z → Q x y z)) e₁ e₂ (u , v) ≡ (subst₂ P e₁ e₂ u , subst₃-d₂ Q e₁ e₂ refl v)
subst₂≡subst₂×subst₃-d₂ P Q refl refl = refl

subst₂-d≡subst₂-d×subst₃-d : {A : Set i} → {B : A → Set j} → (P : (x : A) → B x → Set k) → (Q : (x : A) → (y : B x) → P x y → Set l)
    → {x₁ x₂ : A} → {y₁ : B x₁} → {y₂ : B x₂} → (e₁ : x₁ ≡ x₂) → (e₂ : subst B e₁ y₁ ≡ y₂) → {u : P x₁ y₁} → {v : Q x₁ y₁ u}
    → subst₂-d (λ x y → Σ (P x y) (λ z → Q x y z)) e₁ e₂ (u , v) ≡ (subst₂-d P e₁ e₂ u , subst₃-d Q e₁ e₂ refl v)
subst₂-d≡subst₂-d×subst₃-d P Q refl refl = refl

subst₃≡subst×subst×subst : {A : Set i} → {B : Set j} → {C : Set k} → (P : A → Set l) → (Q : B → Set m) → (R : C → Set n)
    → {x₁ x₂ : A} → {y₁ y₂ : B} → {z₁ z₂ : C} → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → (e₃ : z₁ ≡ z₂)
    → {u : P x₁} → {v : Q y₁} → {w : R z₁}
    → subst₃ (λ x y z → P x × Q y × R z) e₁ e₂ e₃ (u , v , w) ≡ (subst P e₁ u , subst Q e₂ v , subst R e₃ w)
subst₃≡subst×subst×subst P Q R refl refl refl = refl

subst₃-d₂≡subst₃-d₂×subst₃-d₂ :  {A : Set i} → {B : Set j} → {C : A → B → Set k} → (P : (x : A) → (y : B) → C x y → Set l) → (Q : (x : A) → (y : B) → C x y → Set m)
    → {x₁ x₂ : A} → {y₁ y₂ : B} → {z₁ : C x₁ y₁} → {z₂ : C x₂ y₂}
    → (e₁ : x₁ ≡ x₂) → (e₂ : y₁ ≡ y₂) → (e₃ : subst₂ C e₁ e₂ z₁ ≡ z₂)
    → {u : P x₁ y₁ z₁} → {v : Q x₁ y₁ z₁}
    → subst₃-d₂ (λ x y z → P x y z × Q x y z) e₁ e₂ e₃ (u , v) ≡ (subst₃-d₂ P e₁ e₂ e₃ u , subst₃-d₂ Q e₁ e₂ e₃ v)
subst₃-d₂≡subst₃-d₂×subst₃-d₂ P Q refl refl refl = refl

cong-d : {A : Set i} → {P : A → Set j}
    → (f : (x : A) → P x)
    → {x y : A} → (e : x ≡ y)
    → subst P e (f x) ≡ f y -- HoTT Book Lemma 2.3.4
cong-d f refl = refl

cong₂-d : {A : Set i} → {B : A → Set j} → {P : (x : A) → B x → Set k}
    → (f : (x : A) → (y : B x) → P x y)
    → {x₁ x₂ : A} → {y₁ : B x₁} → {y₂ : B x₂} → (e₁ : x₁ ≡ x₂) → (e₂ : subst B e₁ y₁ ≡ y₂)
    → subst₂-d P e₁ e₂ (f x₁ y₁) ≡ f x₂ y₂
cong₂-d f refl refl = refl

cong₃-d : {A : Set i} → {B : A → Set j} → {C : (x : A) → B x → Set k} → {P : (x : A) → (y : B x) → C x y → Set l}
    → (f : (x : A) → (y : B x) → (z : C x y) → P x y z)
    → {x₁ x₂ : A} → {y₁ : B x₁} → {y₂ : B x₂} → {z₁ : C x₁ y₁} → {z₂ : C x₂ y₂}
    → (e₁ : x₁ ≡ x₂) → (e₂ : subst B e₁ y₁ ≡ y₂) → (e₃ : subst₂-d C e₁ e₂ z₁ ≡ z₂)
    → subst₃-d P e₁ e₂ e₃ (f x₁ y₁ z₁) ≡ f x₂ y₂ z₂
cong₃-d f refl refl refl = refl

trans-identity-l : {A : Set i}
    → {x y : A} → (p : x ≡ y)
    → trans refl p ≡ p -- HoTT Book Lemma 2.1.4 (i) (b)
trans-identity-l refl = refl

trans-identity-r : {A : Set i}
    → {x y : A} → (p : x ≡ y)
    → trans p refl ≡ p -- HoTT Book Lemma 2.1.4 (i) (a)
trans-identity-r refl = refl

trans-sym-l : {A : Set i}
    → {x y : A} → (p : x ≡ y)
    → trans (sym p) p ≡ refl -- HoTT Book Lemma 2.1.4 (ii) (a)
trans-sym-l refl = refl

trans-sym-r : {A : Set i}
    → {x y : A} → (p : x ≡ y)
    → trans p (sym p) ≡ refl -- HoTT Book Lemma 2.1.4 (ii) (b)
trans-sym-r refl = refl

trans-assoc : {A : Set i}
    → {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w)
    → trans (trans p q) r ≡ trans p (trans q r) -- HoTT Book Lemma 2.1.4 (iv)
trans-assoc refl refl refl = refl

trans-cong : {A : Set i} → {B : Set j}
    → {f : A → B} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
    → trans (cong f p) (cong f q) ≡ cong f (trans p q) -- HoTT Book Lemma 2.2.2 (i)
trans-cong refl refl = refl

sym-trans : {A : Set i}
    → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
    → sym (trans p q) ≡ trans (sym q) (sym p)
sym-trans refl refl = refl

sym-involution : {A : Set i}
    → {x y : A} → (p : x ≡ y)
    → sym (sym p) ≡ p -- HoTT Book Lemma 2.1.4 (iii)
sym-involution refl = refl

sym-cong : {A : Set i} → {B : Set j}
    → {f : A → B} → {x y : A} → (p : x ≡ y)
    → sym (cong f p) ≡ cong f (sym p) -- HoTT Book Lemma 2.2.2 (ii)
sym-cong refl = refl

cong-cong : {A : Set i} → {B : Set j} → {C : Set k}
    → {f : A → B} → {g : B → C} → {x y : A} → (p : x ≡ y)
    → cong g (cong f p) ≡ cong (g ∘ f) p -- HoTT Book Lemma 2.2.2 (iii)
cong-cong refl = refl

-- id : {A : Set i} → A → A
-- id x = x

cong-id : {A : Set i}
    → {x y : A} → (p : x ≡ y)
    → cong id p ≡ p -- HoTT Book Lemma 2.2.2 (iv)
cong-id refl = refl

subst-eq-r : {A : Set i}
    → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
    → subst (x ≡_) q p ≡ trans p q -- HoTT Book Lemma 2.11.2 (a)
subst-eq-r refl refl = refl
-- subst-eq-r p refl = sym (trans-identity-r p)

subst-eq-l : {A : Set i}
    → {x y z : A} → (p : x ≡ z) → (q : x ≡ y)
    → subst (_≡ z) q p ≡ trans (sym q) p -- HoTT Book Lemma 2.11.2 (b)
subst-eq-l refl refl = refl
-- subst-eq-l p refl = sym (trans-identity-l p) 

subst-eq-diag : {A : Set i}
    → {x y z : A} → (p : x ≡ x) → (q : x ≡ y)
    → subst (λ z → z ≡ z) q p ≡ trans (sym q) (trans p q) -- HoTT Book Lemma 2.11.2 (c)
subst-eq-diag p refl = trans (sym (trans-identity-r p)) (sym (trans-identity-l (trans p refl)))

subst-refl-l : {A : Set i}
    → {x y : A} → (e : x ≡ y)
    → subst (_≡ x) e refl ≡ sym e
-- subst-refl-l refl = refl
subst-refl-l e = trans (subst-eq-l refl e) (trans-identity-r (sym e))

subst-refl-r : {A : Set i}
    → {x y : A} → (e : x ≡ y)
    → subst (x ≡_) e refl ≡ e
subst-refl-r refl = refl
-- subst-refl-r e = trans (subst-eq-r refl e) (trans-identity-l e)

homotopy-natural : {A : Set i} → {B : Set j}
    → {f g : A → B} → (h : (x : A) → f x ≡ g x)
    → {x y : A} → (p : x ≡ y)
    → trans (h x) (cong g p) ≡ trans (cong f p) (h y) -- HoTT Book Lemma 2.4.3
homotopy-natural h {x} {.x} refl =
    trans
        (trans-identity-r (h x))
        (sym (trans-identity-l (h x)))

homotopy-natural-variation : {A : Set i} → {B : Set j}
    → {f g : A → B} → (h : (x : A) → f x ≡ g x)
    → {x y : A} → (p : x ≡ y)
    → trans (sym (h x)) (trans (cong f p) (h y)) ≡ cong g p -- a variation of HoTT Book Lemma 2.4.3
homotopy-natural-variation h {x} {.x} refl = trans-sym-l (h x)

homotopy-natural-d : {A : Set i} → {B : A → Set j}
    → (f g : (x : A) → B x) → (h : (x : A) → f x ≡ g x)
    → (x y : A) → (p : x ≡ y)
    → trans (cong (subst B p) (h x)) (cong-d g p) ≡ trans (cong-d f p) (h y) -- HoTT Book Exercise 2.18
homotopy-natural-d f g h x .x refl =
    trans
        (cong (λ e → trans e refl) (cong-id (h x)))
        (trans
            (trans-identity-r (h x))
            (sym (trans-identity-l (h x))))

-- Chains of Equations

module ≡-Reasoning {A : Set i} where

    infix 1 begin_
    infixr 2 _≡⟨⟩_ _≡⟨_⟩_
    infix 3 _∎

    begin_ : {x y : A} → x ≡ y → x ≡ y
    begin x≡y = x≡y

    _≡⟨⟩_ : (x : A) → {y : A} → x ≡ y → x ≡ y
    x ≡⟨⟩ x≡y = x≡y

    _≡⟨_⟩_ : (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
    x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

    _∎ : (x : A) → x ≡ x
    x ∎ = refl

open ≡-Reasoning

trans′ : {A : Set i} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
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

-- _∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} → {B : Set ℓ₂} → {C : Set ℓ₃}
--     → (B → C) → (A → B) → (A → C)
-- (g ∘ f) x = g (f x)

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
