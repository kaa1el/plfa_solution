{-# OPTIONS --without-K #-}

module plfa.demo.EckmannHilton where

open import Agda.Primitive

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import plfa.part1.Equality using (trans-identity-l; trans-identity-r)

private
    variable
        i j k l : Level

curry : {A : Set i} → {B : A → Set j} → {C : (x : A) → B x → Set k}
    → (f : (w : Σ A B) → C (proj₁ w) (proj₂ w))
    → (x : A) → (y : B x) → C x y
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

Is-Contractible : Set i → Set i -- HoTT Book Definition 3.11.1
Is-Contractible A = Σ A (λ x → (y : A) → x ≡ y)

Singleton-Is-Contractible : {A : Set i} → (x : A) → Is-Contractible (Singleton x) -- HoTT Book Lemma 3.11.8
Singleton-Is-Contractible x .proj₁ .proj₁ = x
Singleton-Is-Contractible x .proj₁ .proj₂ = refl
Singleton-Is-Contractible {A = A} x .proj₂ (y , p) =
    J {C = λ (x y : A) (p : x ≡ y) → (x , refl {x = x}) ≡ (y , p)}
    (λ x → refl) x y p
-- Singleton-Is-Contractible x .proj₂ (.x , refl) = refl

singleton-lift : {A : Set i} → {x y : A} → (p : x ≡ y) → (x , refl) ≡ (y , p) -- extract the lifted path in (Singleton x) from Singleton-Is-Contractible
singleton-lift {A = A} {x} {y} p = Singleton-Is-Contractible x .proj₂ (y , p)

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
