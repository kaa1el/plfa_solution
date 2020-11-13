{-# OPTIONS --without-K #-}

module plfa.demo.HoTT where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Nat using (ℕ; zero; suc)
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

Set∙ : Set₁
Set∙ = Σ Set id -- pointed types, HoTT Book Definition 2.1.7

test-ℕ∙ : Set∙
test-ℕ∙ = (ℕ , zero)

Ω : Set∙ → Set∙ -- loop space, HoTT Book Definition 2.1.8
Ω (A , x) = ((x ≡ x) , refl)

Ω^_ : ℕ → Set∙ → Set∙
(Ω^ zero) A∙ = A∙
(Ω^ suc n) A∙ = Ω ((Ω^ n) A∙)

module Whiskering {A : Set} {x y z : A} where

    whisker-l : {r s : y ≡ z}
        (p : x ≡ y) → r ≡ s
        → trans p r ≡ trans p s
    whisker-l {r} {s} refl β =
        trans
            (trans (trans-identity-l r) β)
            (sym (trans-identity-l s))

    whisker-r : {p q : x ≡ y}
        → p ≡ q → (r : y ≡ z)
        → trans p r ≡ trans q r
    whisker-r {p} {q} α refl =
        trans
            (trans (trans-identity-r p) α)
            (sym (trans-identity-r q))

    htrans-l : {p q : x ≡ y} → {r s : y ≡ z}
        → p ≡ q → r ≡ s
        → trans p r ≡ trans q s
    htrans-l {_} {q} {r} {_} α β = trans (whisker-r α r) (whisker-l q β)

    htrans-r : {p q : x ≡ y} → {r s : y ≡ z}
        → p ≡ q → r ≡ s
        → trans p r ≡ trans q s
    htrans-r {p} {_} {_} {s} α β = trans (whisker-l p β) (whisker-r α s)

    htrans-identity : {p q : x ≡ y} → {r s : y ≡ z}
        → (α : p ≡ q) → (β : r ≡ s)
        → htrans-l α β ≡ htrans-r α β
    htrans-identity {refl} {.refl} {refl} {.refl} refl refl = refl

open Whiskering

eckmann-hilton-l : {A∙ : Set∙}
    → (α β : (Ω^ 2) A∙ .proj₁)
    → htrans-l α β ≡ trans α β
eckmann-hilton-l α β =
    begin
        htrans-l α β
    ≡⟨⟩
        trans
            (whisker-r α refl)
            (whisker-l refl β)
    ≡⟨⟩
        trans
            (trans
                (trans (trans-identity-r refl) α)
                (sym (trans-identity-r refl)))
            (trans
                (trans (trans-identity-l refl) β)
                (sym (trans-identity-l refl)))
    ≡⟨⟩
        trans
            (trans
                (trans refl α)
                refl)
            (trans
                (trans refl β)
                refl)
    ≡⟨ cong₂ trans (trans-identity-r (trans refl α)) (trans-identity-r (trans refl β)) ⟩
        trans
            (trans refl α)
            (trans refl β)
    ≡⟨ cong₂ trans (trans-identity-l α) (trans-identity-l β) ⟩
        trans α β
    ∎

eckmann-hilton-r : {A∙ : Set∙}
    → (α β : (Ω^ 2) A∙ .proj₁)
    → htrans-r α β ≡ trans β α
eckmann-hilton-r α β =
    begin
        htrans-r α β
    ≡⟨⟩
        trans
            (whisker-l refl β)
            (whisker-r α refl)
    ≡⟨⟩
        trans
            (trans
                (trans (trans-identity-l refl) β)
                (sym (trans-identity-l refl)))
            (trans
                (trans (trans-identity-r refl) α)
                (sym (trans-identity-r refl)))
    ≡⟨⟩
        trans
            (trans
                (trans refl β)
                refl)
            (trans
                (trans refl α)
                refl)
    ≡⟨ cong₂ trans (trans-identity-r (trans refl β)) (trans-identity-r (trans refl α)) ⟩
        trans
            (trans refl β)
            (trans refl α)
    ≡⟨ cong₂ trans (trans-identity-l β) (trans-identity-l α) ⟩
        trans β α
    ∎

eckmann-hilton : {A∙ : Set∙}
    → (α β : (Ω^ 2) A∙ .proj₁)
    → trans α β ≡ trans β α -- second loop (bubble) space is commutative, HoTT Book Theorem 2.1.6
eckmann-hilton α β =
    begin
        trans α β
    ≡⟨ sym (eckmann-hilton-l α β) ⟩
        htrans-l α β
    ≡⟨ htrans-identity α β ⟩
        htrans-r α β
    ≡⟨ eckmann-hilton-r α β ⟩
        trans β α
    ∎
-- {-# OPTIONS --without-K #-} is needed, otherwise the following "proof" would be accepted
-- this is due to the default dependent pattern matching is using axiom K
-- and the fact that pattern match of p : x ≡ x with refl is not allowed without K
-- however p : x ≡ y can be pattern matched with refl
-- without axiom K, dependent pattern matching cannot do unification on x ≡ x

-- eckmann-hilton refl refl = refl

UIP : Set₁
UIP = {A : Set} → {a b : A} → (p q : a ≡ b) → p ≡ q

K : Set₁
K = {A : Set} → {x : A} → {P : x ≡ x → Set} → P refl → (e : x ≡ x) → P e

-- uip : {A : Set} → {x y : A}
--     → (p q : x ≡ y)
--     → p ≡ q
-- uip refl refl = refl

-- k : {A : Set} → {x : A} → {P : x ≡ x → Set}
--     → P refl
--     → (e : x ≡ x) → P e
-- k r refl = r

uip-to-k : UIP → K -- HoTT Book Theorem 7.2.1 (a)
uip-to-k uip {P = P} r e = subst P (uip refl e) r

k-to-uip : K → UIP -- HoTT Book Theorem 7.2.1 (b)
k-to-uip k {A} {x} {.x} refl q = k {P = λ q → refl ≡ q} refl q
