module plfa.demo.IdentityProperties where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Function using (id; _∘_)

_ : {A : Set} → {x : A} → x ≡ x
_ = refl

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x -- HoTT Book Lemma 2.1.1
sym refl = refl

trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z -- HoTT Book Lemma 2.1.2
trans refl refl = refl

cong : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y -- HoTT Book Lemma 2.2.1
cong f refl = refl

cong₂ : {A B C : Set} → (f : A → B → C) → {x u : A} → {y v : B}
    → x ≡ u → y ≡ v → f x y ≡ f u v
cong₂ f refl refl = refl

cong-app : {A B : Set} → {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl

subst : {A : Set} → {x y : A} → (P : A → Set) → x ≡ y → P x → P y -- HoTT Book Lemma 2.3.1
subst P refl a = a

subst-inv : {A : Set} → {x y : A} → (P : A → Set) → x ≡ y → P y → P x
subst-inv P refl a = a

subst-trans : {A : Set} → (P : A → Set) → {x y z : A} → {u : P x} → (p : x ≡ y) → (q : y ≡ z)
    → subst P (trans p q) u ≡ subst P q (subst P p u) -- HoTT Book Lemma 2.3.9
subst-trans P refl refl = refl

subst-sym : {A : Set} → (P : A → Set) → {x y : A} → {v : P y} → (p : x ≡ y)
    → subst P (sym p) v ≡ subst-inv P p v
subst-sym P refl = refl

subst-cong : {A B : Set} → {f : A → B} → (P : B → Set) → {x y : A} → {u : P (f x)} → (e : x ≡ y)
    → subst P (cong f e) u ≡ subst (λ x → P (f x)) e u -- HoTT Book Lemma 2.3.10
subst-cong P refl = refl

congd : {A : Set} → {B : A → Set} → (f : (x : A) → B x) → {x y : A} → (e : x ≡ y)
    → subst B e (f x) ≡ f y -- HoTT Book Lemma 2.3.4
congd f refl = refl

trans-identity-l : {A : Set} → {x y : A} → (p : x ≡ y) → trans refl p ≡ p -- HoTT Book Lemma 2.1.4 (i) (b)
trans-identity-l refl = refl

trans-identity-r : {A : Set} → {x y : A} → (p : x ≡ y) → trans p refl ≡ p -- HoTT Book Lemma 2.1.4 (i) (a)
trans-identity-r refl = refl

trans-sym-l : {A : Set} → {x y : A} → (p : x ≡ y) → trans (sym p) p ≡ refl -- HoTT Book Lemma 2.1.4 (ii) (a)
trans-sym-l refl = refl

trans-sym-r : {A : Set} → {x y : A} → (p : x ≡ y) → trans p (sym p) ≡ refl -- HoTT Book Lemma 2.1.4 (ii) (b)
trans-sym-r refl = refl

trans-assoc : {A : Set} → {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w)
    → trans (trans p q) r ≡ trans p (trans q r) -- HoTT Book Lemma 2.1.4 (iv)
trans-assoc refl refl refl = refl

trans-cong : {A B : Set} → {f : A → B} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
    → trans (cong f p) (cong f q) ≡ cong f (trans p q) -- HoTT Book Lemma 2.2.2 (i)
trans-cong refl refl = refl

sym-trans : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
    → sym (trans p q) ≡ trans (sym q) (sym p)
sym-trans refl refl = refl

sym-involution : {A : Set} → {x y : A} → (p : x ≡ y) → sym (sym p) ≡ p -- HoTT Book Lemma 2.1.4 (iii)
sym-involution refl = refl

sym-cong : {A B : Set} → {f : A → B} → {x y : A} → (p : x ≡ y)
    → sym (cong f p) ≡ cong f (sym p) -- HoTT Book Lemma 2.2.2 (ii)
sym-cong refl = refl

cong-cong : {A B C : Set} → {f : A → B} → {g : B → C} → {x y : A} → (p : x ≡ y)
    → cong g (cong f p) ≡ cong (g ∘ f) p -- HoTT Book Lemma 2.2.2 (iii)
cong-cong refl = refl

cong-id : {A : Set} → {x y : A} → (p : x ≡ y) → cong id p ≡ p -- HoTT Book Lemma 2.2.2 (iv)
cong-id refl = refl

homotopy-natural : {A B : Set}
    → (f g : A → B) → (h : (x : A) → f x ≡ g x)
    → (x y : A) → (e : x ≡ y)
    → trans (h x) (cong g e) ≡ trans (cong f e) (h y) -- HoTT Book Lemma 2.4.3
homotopy-natural f g h x .x refl =
    trans
        (trans-identity-r (h x))
        (sym (trans-identity-l (h x)))

homotopy-natural-d : {A : Set} → {B : A → Set}
    → (f g : (x : A) → B x) → (h : (x : A) → f x ≡ g x)
    → (x y : A) → (e : x ≡ y)
    → trans (cong (subst B e) (h x)) (congd g e) ≡ trans (congd f e) (h y) -- HoTT Book Corollary 2.4.4
homotopy-natural-d f g h x .x refl =
    trans
        (cong (λ e → trans e refl) (cong-id (h x)))
        (trans
            (trans-identity-r (h x))
            (sym (trans-identity-l (h x))))

lift : {A : Set} → {B : A → Set} → {a x : A}→ (b : B a) → (e : a ≡ x)
    → (a , b) ≡ (x , subst B e b) -- HoTT Book Lemma 2.3.2 (a)
lift b refl = refl

lift-proj₁ : {A : Set} → {B : A → Set} → {a x : A} → (b : B a) → (e : a ≡ x)
    → cong proj₁ (lift {A} {B} b e) ≡ e -- HoTT Book Lemma 2.3.2 (b)
lift-proj₁ b refl = refl
