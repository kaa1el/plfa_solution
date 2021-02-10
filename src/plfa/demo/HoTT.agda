{-# OPTIONS --without-K #-}

module plfa.demo.HoTT where

open import Agda.Primitive

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (id; _∘_)

private
    variable
        i j k : Level

_ : {A : Set i} → {x : A} → x ≡ x
_ = refl

sym : {A : Set i} → {x y : A} → x ≡ y → y ≡ x -- HoTT Book Lemma 2.1.1
sym refl = refl

trans : {A : Set i} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z -- HoTT Book Lemma 2.1.2
trans refl refl = refl

cong : {A : Set i} → {B : Set j} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y -- HoTT Book Lemma 2.2.1
cong f refl = refl

cong₂ : {A : Set i} → {B : Set j} → {C : Set k} → (f : A → B → C) → {x u : A} → {y v : B}
    → x ≡ u → y ≡ v → f x y ≡ f u v
cong₂ f refl refl = refl

cong-app : {A : Set i} → {B : Set j} → {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl

subst : {A : Set i} → {x y : A} → (P : A → Set j) → x ≡ y → P x → P y -- HoTT Book Lemma 2.3.1
subst P refl a = a

subst-inv : {A : Set i} → {x y : A} → (P : A → Set j) → x ≡ y → P y → P x
subst-inv P refl a = a

subst-trans : {A : Set i} → (P : A → Set j) → {x y z : A} → {u : P x} → (p : x ≡ y) → (q : y ≡ z)
    → subst P (trans p q) u ≡ subst P q (subst P p u) -- HoTT Book Lemma 2.3.9
subst-trans P refl refl = refl

subst-sym : {A : Set i} → (P : A → Set j) → {x y : A} → {v : P y} → (p : x ≡ y)
    → subst P (sym p) v ≡ subst-inv P p v
subst-sym P refl = refl

subst-cong : {A : Set i} → {B : Set j} → {f : A → B} → (P : B → Set k) → {x y : A} → {u : P (f x)} → (e : x ≡ y)
    → subst P (cong f e) u ≡ subst (λ x → P (f x)) e u -- HoTT Book Lemma 2.3.10
subst-cong P refl = refl

congd : {A : Set i} → {B : A → Set j} → (f : (x : A) → B x) → {x y : A} → (e : x ≡ y)
    → subst B e (f x) ≡ f y -- HoTT Book Lemma 2.3.4
congd f refl = refl

trans-identity-l : {A : Set i} → {x y : A} → (p : x ≡ y) → trans refl p ≡ p -- HoTT Book Lemma 2.1.4 (i) (b)
trans-identity-l refl = refl

trans-identity-r : {A : Set i} → {x y : A} → (p : x ≡ y) → trans p refl ≡ p -- HoTT Book Lemma 2.1.4 (i) (a)
trans-identity-r refl = refl

trans-sym-l : {A : Set i} → {x y : A} → (p : x ≡ y) → trans (sym p) p ≡ refl -- HoTT Book Lemma 2.1.4 (ii) (a)
trans-sym-l refl = refl

trans-sym-r : {A : Set i} → {x y : A} → (p : x ≡ y) → trans p (sym p) ≡ refl -- HoTT Book Lemma 2.1.4 (ii) (b)
trans-sym-r refl = refl

trans-assoc : {A : Set i} → {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w)
    → trans (trans p q) r ≡ trans p (trans q r) -- HoTT Book Lemma 2.1.4 (iv)
trans-assoc refl refl refl = refl

trans-cong : {A : Set i} → {B : Set j} → {f : A → B} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
    → trans (cong f p) (cong f q) ≡ cong f (trans p q) -- HoTT Book Lemma 2.2.2 (i)
trans-cong refl refl = refl

sym-trans : {A : Set i} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
    → sym (trans p q) ≡ trans (sym q) (sym p)
sym-trans refl refl = refl

sym-involution : {A : Set i} → {x y : A} → (p : x ≡ y) → sym (sym p) ≡ p -- HoTT Book Lemma 2.1.4 (iii)
sym-involution refl = refl

sym-cong : {A : Set i} → {B : Set j} → {f : A → B} → {x y : A} → (p : x ≡ y)
    → sym (cong f p) ≡ cong f (sym p) -- HoTT Book Lemma 2.2.2 (ii)
sym-cong refl = refl

cong-cong : {A : Set i} → {B : Set j} → {C : Set k} → {f : A → B} → {g : B → C} → {x y : A} → (p : x ≡ y)
    → cong g (cong f p) ≡ cong (g ∘ f) p -- HoTT Book Lemma 2.2.2 (iii)
cong-cong refl = refl

cong-id : {A : Set i} → {x y : A} → (p : x ≡ y) → cong id p ≡ p -- HoTT Book Lemma 2.2.2 (iv)
cong-id refl = refl

homotopy-natural : {A : Set i} → {B : Set j}
    → (f g : A → B) → (h : (x : A) → f x ≡ g x)
    → (x y : A) → (p : x ≡ y)
    → trans (h x) (cong g p) ≡ trans (cong f p) (h y) -- HoTT Book Lemma 2.4.3
homotopy-natural f g h x .x refl =
    trans
        (trans-identity-r (h x))
        (sym (trans-identity-l (h x)))

homotopy-natural-d : {A : Set i} → {B : A → Set j}
    → (f g : (x : A) → B x) → (h : (x : A) → f x ≡ g x)
    → (x y : A) → (p : x ≡ y)
    → trans (cong (subst B p) (h x)) (congd g p) ≡ trans (congd f p) (h y) -- HoTT Book Corollary 2.4.4
homotopy-natural-d f g h x .x refl =
    trans
        (cong (λ e → trans e refl) (cong-id (h x)))
        (trans
            (trans-identity-r (h x))
            (sym (trans-identity-l (h x))))

curry : {A : Set i} → {B : A → Set j} → {C : Σ A B → Set k}
    → (f : (w : Σ A B) → C w)
    → (x : A) → (y : B x) → C (x , y)
curry f x y = f (x , y)

uncurry : {A : Set i} → {B : A → Set j} → {C : (x : A) → B x → Set k}
    → (f : (x : A) → (y : B x) → C x y)
    → (w : Σ A B) → C (proj₁ w) (proj₂ w)
uncurry f w = f (proj₁ w) (proj₂ w)

lift : {A : Set i} → {B : A → Set j}
    → {a x : A} → (b : B a) → (p : a ≡ x)
    → (a , b) ≡ (x , subst B p b) -- HoTT Book Lemma 2.3.2 (a)
lift b refl = refl

lift-proj₁ : {A : Set i} → {B : A → Set j}
    → {a x : A} → (b : B a) → (p : a ≡ x)
    → cong proj₁ (lift {A = A} {B = B} b p) ≡ p -- HoTT Book Lemma 2.3.2 (b)
lift-proj₁ b refl = refl

-- H is the based path induction, it corresponds to the standard definition of identity type using
-- a parameterized indexed type family (parameterized inductive family), i.e., x is a parameter, y is an index

H : {A : Set i} → {x : A} → {D : (y : A) → x ≡ y → Set j}
    → D x refl
    → (y : A) → (p : x ≡ y) → D y p
H d y refl = d

H-η : {A : Set i} → {x : A} → {D : (y : A) → x ≡ y → Set j}
    → (d : D x refl)
    → (f : (y : A) → (p : x ≡ y) → D y p)
    → (f x refl ≡ d)
    → ((y : A) → (p : x ≡ y) → f y p ≡ H {D = D} d y p)
H-η {D = D} d f pd = H {D = λ y p → f y p ≡ H {D = D} d y p} pd
-- H-η d f pd y refl = pd

-- J is the path induction, it corresponds to the definition of identity type using inductive family on its both indices x and y

J : {A : Set i} → {C : (x y : A) → x ≡ y → Set j}
    → ((x : A) → C x x refl)
    → (x y : A) → (p : x ≡ y) → C x y p
J c x .x refl = c x

J-η : {A : Set i} → {C : (x y : A) → x ≡ y → Set j}
    → (c : (x : A) → C x x refl)
    → (f : (x y : A) → (p : x ≡ y) → C x y p)
    → ((x : A) → f x x refl ≡ c x)
    → ((x y : A) → (p : x ≡ y) → f x y p ≡ J {C = C} c x y p)
J-η {C = C} c f pc = J {C = λ x y p → f x y p ≡ J {C = C} c x y p} pc
-- J-η c f pc x .x refl = pc x

-- deriving J from H

J′ : {A : Set i} → {C : (x y : A) → x ≡ y → Set j}
    → ((x : A) → C x x refl)
    → (x y : A) → (p : x ≡ y) → C x y p
J′ c x = H (c x)

J′≡J : {A : Set i} → {C : (x y : A) → x ≡ y → Set j}
    → (c : (x : A) → C x x refl)
    → (x y : A) → (p : x ≡ y)
    → J′ {C = C} c x y p ≡ J {C = C} c x y p
J′≡J {C = C} c = J-η {C = C} c (J′ {C = C} c) (λ x → refl)
-- J′≡J c x .x refl = refl

-- deriving H from J

H′ : {A : Set i} → {x : A} → {D : (y : A) → x ≡ y → Set j}
    → D x refl
    → (y : A) → (p : x ≡ y) → D y p
H′ {i} {j} {A} {x} {D} d y p = J {i = i} {j = i ⊔ lsuc j} {C = C} c x y p D d where
    C : (x y : A) → x ≡ y → Set (i ⊔ lsuc j) -- here we used polymorphic universe version of J with j = i ⊔ lsuc j
    C x y p = (D : (y : A) → x ≡ y → Set j) → D x refl → D y p
    c : (x : A) → C x x refl
    c x D = id

H′≡H : {A : Set i} → {x : A} → {D : (y : A) → x ≡ y → Set j}
    → (d : D x refl)
    → (y : A) → (p : x ≡ y)
    → H′ {D = D} d y p ≡ H {D = D} d y p
H′≡H d = H-η d (H′ d) refl

-- deriving H from J without using universe polymorphism

Singleton : {A : Set i} → (x : A) → Set i
Singleton {A = A} x = Σ A (λ y → x ≡ y)

Contractible : Set i → Set i -- HoTT Book Definition 3.11.1
Contractible A = Σ A (λ x → (y : A) → x ≡ y)

singleton-contractible : {A : Set i} → (x : A) → Contractible (Singleton x) -- HoTT Book Lemma 3.11.8
singleton-contractible x .proj₁ .proj₁ = x
singleton-contractible x .proj₁ .proj₂ = refl
singleton-contractible {A = A} x .proj₂ (y , p) =
    J {C = λ (x y : A) (p : x ≡ y) → (x , refl {x = x}) ≡ (y , p)}
    (λ x → refl) x y p
-- singleton-contractible x .proj₂ (.x , refl) = refl

singleton-lift : {A : Set i} → {x y : A} → (p : x ≡ y) → (x , refl) ≡ (y , p) -- extract the lifted path in (Singleton x) from singleton-contractible
singleton-lift {A = A} {x} {y} p = singleton-contractible x .proj₂ (y , p)

-- singleton-lift : {A : Set i} → {x y : A} → (p : x ≡ y) → (x , refl {x = x}) ≡ (y , p)
-- singleton-lift {A = A} {x} {.x} refl = refl

H″ : {A : Set i} → {x : A} → {D : (y : A) → x ≡ y → Set j}
    → D x refl
    → (y : A) → (p : x ≡ y) → D y p
H″ {D = D} d y p = subst (uncurry D) (singleton-lift p) d

H″≡H : {A : Set i} → {x : A} → {D : (y : A) → x ≡ y → Set j}
    → (d : D x refl)
    → (y : A) → (p : x ≡ y)
    → H″ {D = D} d y p ≡ H {D = D} d y p
H″≡H d = H-η d (H″ d) refl
-- H″≡H d y refl = refl

Pointed : Set (lsuc i)
Pointed {i} = Σ (Set i) id -- pointed types, HoTT Book Definition 2.1.7

Set∙ : Set₁
Set∙ = Σ Set id

test-ℕp : Pointed
test-ℕp = (ℕ , zero)

Ω : Pointed {i} → Pointed {i} -- loop space, HoTT Book Definition 2.1.8
Ω (A , x) = ((x ≡ x) , refl)

Ω^_ : ℕ → Pointed {i} → Pointed {i}
(Ω^ zero) Ap = Ap
(Ω^ suc n) Ap = Ω ((Ω^ n) Ap)

module Whiskering {A : Set i} {x y z : A} where

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

eckmann-hilton-l : {Ap : Pointed {i}}
    → (α β : (Ω^ 2) Ap .proj₁)
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

eckmann-hilton-r : {Ap : Pointed {i}}
    → (α β : (Ω^ 2) Ap .proj₁)
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

eckmann-hilton : {Ap : Pointed {i}}
    → (α β : (Ω^ 2) Ap .proj₁)
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
-- {-# OPTIONS --without-K #-} is needed, otherwise the following "proof" would be accepted (even for first loop space)
-- this is due to the default dependent pattern matching is using axiom-K
-- and the fact that pattern match of p : x ≡ x with refl is not allowed without K
-- however p : x ≡ y can be pattern matched with refl
-- without axiom-K, dependent pattern matching cannot do unification on x ≡ x
-- one way to look at this is the fact that induction on p : x ≡ y happens on (y , p) simultaneously
-- on the base case (x , refl) instead of fixing y = x and induct on a general p : x ≡ x,
-- an analogy in topology: imagine on the punctured disk (S¹ × I), a general p : x ≡ x
-- could loop around the puncture so it is not equivalent to refl : x ≡ x,
-- however for a general p : x ≡ y, it can continuously deformed into refl : x ≡ x

-- eckmann-hilton refl refl = refl

UIP : Set (lsuc i)
UIP {i} = {A : Set i} → {a b : A} → (p q : a ≡ b) → p ≡ q

K : Set (lsuc (i ⊔ j))
K {i} {j} = {A : Set i} → {x : A} → {P : x ≡ x → Set j} → P refl → (e : x ≡ x) → P e

-- uip : {A : Set i} → {x y : A}
--     → (p q : x ≡ y)
--     → p ≡ q
-- uip refl refl = refl

-- k : {A : Set i} → {x : A} → {P : x ≡ x → Set j}
--     → P refl
--     → (e : x ≡ x) → P e
-- k r refl = r

uip-to-k : UIP {i} → K {i} {j} -- HoTT Book Theorem 7.2.1 (a)
uip-to-k uip {P = P} r e = subst P (uip refl e) r

k-to-uip : K {i} {i} → UIP {i} -- HoTT Book Theorem 7.2.1 (b)
k-to-uip k {A} {x} {.x} refl q = k {P = λ q → refl ≡ q} refl q
