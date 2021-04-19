{-# OPTIONS --without-K #-}

module plfa.part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; +-comm; *-assoc; *-identityˡ; *-identityʳ; *-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Level using (Level)

open import plfa.part1.Isomorphism using (_≅_; extensionality; Π-extensionality; _⇔_)

data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A
infixr 5 _∷_
{-# BUILTIN LIST List #-}

record Stream (A : Set) : Set where
    coinductive
    constructor cons
    field
        head : A
        tail : Stream A

record CoList (A : Set) : Set where
    coinductive
    field
        unfold : Maybe (A × CoList A)

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

data List′ : Set → Set₁ where -- note if we disable --without-K, List′ can be defined at Set → Set
    []′  : {A : Set} → List′ A -- see https://agda.readthedocs.io/en/latest/language/without-k.html
    _∷′_ : {A : Set} → A → List′ A → List′ A -- also https://github.com/HoTT/HoTT/issues/842

-- currently I do not understand the difference between this indexed inductive family definition and the above parameterized inductive definition under --without-K
-- see https://stackoverflow.com/questions/66254425/why-does-universe-level-restriction-behave-differently-between-inductive-family

data _≡′_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
    refl : x ≡′ x

-- pattern [_] z = z ∷ []
-- pattern [_,_] y z = y ∷ z ∷ []
-- pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
-- pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
-- pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
-- pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

pattern [_] z = z ∷ []
pattern [_､_] y z = y ∷ z ∷ []
pattern [_､_､_] x y z = x ∷ y ∷ z ∷ []
pattern [_､_､_､_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_､_､_､_､_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_､_､_､_､_､_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_ : [ 0 ､ 1 ､ 2 ] ++ [ 3 ､ 4 ] ≡ [ 0 ､ 1 ､ 2 ､ 3 ､ 4 ]
_ =
    begin
        0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
    ≡⟨⟩
        0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
    ≡⟨⟩
        0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
    ≡⟨⟩
        0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
    ≡⟨⟩
        0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
    ∎

++-assoc : {A : Set} → (xs ys zs : List A)
    → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identityˡ : {A : Set} → (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

length : {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

_ : length [ 0 ､ 1 ､ 2 ] ≡ 3
_ = refl

_ : length {ℕ} [] ≡ 0
_ = refl

length-++ : {A : Set} → (xs ys : List A)
    → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

_ : reverse [ 0 ､ 1 ､ 2 ] ≡ [ 2 ､ 1 ､ 0 ]
_ = -- This reverse operation is O(n^2) due to the ++ operation is O(n) on the first list
    begin
        reverse (0 ∷ 1 ∷ 2 ∷ [])
    ≡⟨⟩
        reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
    ≡⟨⟩
        (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
    ≡⟨⟩
        ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
    ≡⟨⟩
        (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
    ≡⟨⟩
        (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
    ≡⟨⟩
        (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
    ≡⟨⟩
        2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
    ≡⟨⟩
        (2 ∷ 1 ∷ []) ++ 0 ∷ []
    ≡⟨⟩
        2 ∷ (1 ∷ [] ++ 0 ∷ [])
    ≡⟨⟩
        2 ∷ 1 ∷ ([] ++ 0 ∷ [])
    ≡⟨⟩
        2 ∷ 1 ∷ 0 ∷ []
    ∎

reverse-++-distrib : {A : Set} → (xs ys : List A)
    → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys = sym (++-identityʳ (reverse ys))
reverse-++-distrib (x ∷ xs) ys =
    begin
        reverse (xs ++ ys) ++ [ x ]
    ≡⟨ (cong (_++ [ x ]) (reverse-++-distrib xs ys)) ⟩
        (reverse ys ++ reverse xs) ++ [ x ]
    ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
        reverse ys ++ (reverse xs ++ [ x ])
    ∎

reverse-involutive : {A : Set} → (xs : List A)
    → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
    begin
        reverse (reverse xs ++ [ x ])
    ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
        reverse [ x ] ++ reverse (reverse xs)
    ≡⟨ cong (x ∷_) (reverse-involutive xs) ⟩
        x ∷ xs
    ∎

shunt : {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : {A : Set} → (xs ys : List A)
    → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys =
    begin
        shunt xs (x ∷ ys)
    ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
        reverse xs ++ ([ x ] ++ ys)
    ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
        reverse (x ∷ xs) ++ ys
    ∎

reverse′ : {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : {A : Set} → (xs : List A)
    → reverse′ xs ≡ reverse xs
reverses xs =
    begin
        shunt xs []
    ≡⟨ shunt-reverse xs [] ⟩
        reverse xs ++ []
    ≡⟨ ++-identityʳ (reverse xs) ⟩
        reverse xs
    ∎

_ : reverse′ [ 0 ､ 1 ､ 2 ] ≡ [ 2 ､ 1 ､ 0 ]
_ =
    begin
        reverse′ (0 ∷ 1 ∷ 2 ∷ [])
    ≡⟨⟩
        shunt (0 ∷ 1 ∷ 2 ∷ []) []
    ≡⟨⟩
        shunt (1 ∷ 2 ∷ []) (0 ∷ [])
    ≡⟨⟩
        shunt (2 ∷ []) (1 ∷ 0 ∷ [])
    ≡⟨⟩
        shunt [] (2 ∷ 1 ∷ 0 ∷ [])
    ≡⟨⟩
        2 ∷ 1 ∷ 0 ∷ []
    ∎

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_ : map suc [ 0 ､ 1 ､ 2 ] ≡ [ 1 ､ 2 ､ 3 ]
_ =
    begin
        map suc (0 ∷ 1 ∷ 2 ∷ [])
    ≡⟨⟩
        suc 0 ∷ map suc (1 ∷ 2 ∷ [])
    ≡⟨⟩
        suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
    ≡⟨⟩
        suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
    ≡⟨⟩
        suc 0 ∷ suc 1 ∷ suc 2 ∷ []
    ≡⟨⟩
        1 ∷ 2 ∷ 3 ∷ []
    ∎

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 ､ 1 ､ 2 ] ≡ [ 1 ､ 2 ､ 3 ]
_ =
    begin
        sucs [ 0 ､ 1 ､ 2 ]
    ≡⟨⟩
        map suc [ 0 ､ 1 ､ 2 ]
    ≡⟨⟩
        [ 1 ､ 2 ､ 3 ]
    ∎

map-compose : {A B C : Set}
    → (f : A → B) → (g : B → C)
    → (xs : List A)
    → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose f g [] = refl
map-compose f g (x ∷ xs) =
    begin
        (g ∘ f) x ∷ map (g ∘ f) xs
    ≡⟨ cong ((g ∘ f) x ∷_) (map-compose f g xs) ⟩
        (g ∘ f) x ∷ (map g ∘ map f) xs
    ≡⟨⟩
        (map g ∘ map f) (x ∷ xs)
    ∎

map-++-distribute : {A B : Set}
    → (f : A → B)
    → (xs ys : List A)
    → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys = cong (f x ∷_) (map-++-distribute f xs ys)

data Tree (A : Set) : Set where
    leaf : Tree A
    node : A → Tree A → Tree A → Tree A

record InfTree (A : Set) : Set where
    coinductive
    field
        value : A
        left : InfTree A
        right : InfTree A

record CoTree (A : Set) : Set where
    coinductive
    field
        unfold : Maybe (A × CoTree A × CoTree A)

mapTree : {A B : Set} → (A → B) → Tree A → Tree B
mapTree f leaf = leaf
mapTree f (node x t1 t2) = node (f x) (mapTree f t1) (mapTree f t2)

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

foldl : {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

_ : foldr _+_ 0 [ 1 ､ 2 ､ 3 ､ 4 ] ≡ 10
_ =
    begin
        foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
    ≡⟨⟩
        1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
    ≡⟨⟩
        1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
    ≡⟨⟩
        1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
    ≡⟨⟩
        1 + (2 + (3 + (4 + foldr _+_ 0 [])))
    ≡⟨⟩
        1 + (2 + (3 + (4 + 0)))
    ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 ､ 2 ､ 3 ､ 4 ] ≡ 10
_ = refl

product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 ､ 2 ､ 3 ､ 4 ] ≡ 24
_ = refl

foldr-++ : {A B : Set} → (_⊗_ : A → B → B) → (e : B)
    → (xs ys : List A)
    → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys = cong (x ⊗_) (foldr-++ _⊗_ e xs ys)

foldr-∷ : {A : Set} → (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) = cong (x ∷_) (foldr-∷ xs)

foldr-++-List : {A : Set} → (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
-- foldr-++-List [] ys = refl
-- foldr-++-List (x ∷ xs) ys = cong (x ∷_) (foldr-++-List xs ys)
foldr-++-List xs ys =
    begin
        xs ++ ys
    ≡⟨ sym (foldr-∷ (xs ++ ys)) ⟩
        foldr _∷_ [] (xs ++ ys)
    ≡⟨ foldr-++ _∷_ [] xs ys ⟩
        foldr _∷_ (foldr _∷_ [] ys) xs
    ≡⟨ cong (λ ys → foldr _∷_ ys xs) (foldr-∷ ys) ⟩
        foldr _∷_ ys xs
    ∎

map-foldr : {A B : Set} → (f : A → B) → (xs : List A)
    → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
map-foldr f [] = refl
map-foldr f (x ∷ xs) = cong (f x ∷_) (map-foldr f xs)

foldTree : {A B : Set}
    → B
    → (A → B → B → B)
    → Tree A → B
foldTree bleaf bnode leaf = bleaf
foldTree bleaf bnode (node x t1 t2) = bnode x (foldTree bleaf bnode t1) (foldTree bleaf bnode t2)

foldList : {A B : Set}
    → B
    → (A → B → B)
    → List A → B
foldList bnil bcons [] = bnil
foldList bnil bcons (x ∷ xs) = bcons x (foldList bnil bcons xs)

foldList-l : {A B : Set}
    → B
    → (B → A → B)
    → List A → B
foldList-l bnil bcons [] = bnil
foldList-l bnil bcons (x ∷ xs) = foldList-l (bcons bnil x) bcons xs

mapTree-foldTree : {A B : Set} → (f : A → B) → (t : Tree A)
    → mapTree f t ≡ foldTree leaf (λ x t1 t2 → node (f x) t1 t2) t
mapTree-foldTree f leaf = refl
mapTree-foldTree f (node x t1 t2) = cong₂ (node (f x)) (mapTree-foldTree f t1) (mapTree-foldTree f t2)

downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 ､ 1 ､ 0 ]
_ = refl

gauss : (n : ℕ) → sum (downFrom (suc n)) + sum (downFrom (suc n)) ≡ (suc n) * n
gauss zero = refl
gauss (suc n) =
    begin -- could use a ring solver
        sum (downFrom (suc (suc n))) + sum (downFrom (suc (suc n)))
    ≡⟨⟩
        (suc n + sum (downFrom (suc n))) + (suc n + sum (downFrom (suc n)))
    ≡⟨ sym (+-assoc (suc n + sum (downFrom (suc n))) (suc n) (sum (downFrom (suc n)))) ⟩
       ((suc n + sum (downFrom (suc n))) + suc n) + sum (downFrom (suc n))
    ≡⟨ cong (_+ sum (downFrom (suc n))) (+-comm (suc n + sum (downFrom (suc n))) (suc n)) ⟩
        (suc n + (suc n + sum (downFrom (suc n)))) + sum (downFrom (suc n))
    ≡⟨ cong (_+ sum (downFrom (suc n))) (sym (+-assoc (suc n) (suc n) (sum (downFrom (suc n))))) ⟩
        ((suc n + suc n) + sum (downFrom (suc n))) + sum (downFrom (suc n))
    ≡⟨ +-assoc (suc n + suc n) (sum (downFrom (suc n))) (sum (downFrom (suc n))) ⟩
        (suc n + suc n) + (sum (downFrom (suc n)) + sum (downFrom (suc n)))
    ≡⟨ cong ((suc n + suc n) +_) (gauss n) ⟩
        (suc n + suc n) + suc n * n
    ≡⟨ cong ((suc n + suc n) +_) (*-comm (suc n) n) ⟩
        (suc n + suc n) + n * suc n
    ≡⟨ +-assoc (suc n) (suc n) (n * suc n) ⟩
        suc n + (suc n + n * suc n)
    ≡⟨⟩
        (suc (suc n)) * suc n
    ∎

record Monoid (A : Set) (_⊗_ : A → A → A) (e : A) : Set where
    field
        assoc : (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
        identityˡ : (x : A) → e ⊗ x ≡ x
        identityʳ : (x : A) → x ⊗ e ≡ x
open Monoid

ℕ+-monoid : Monoid ℕ _+_ 0
ℕ+-monoid =
    record {
        assoc = +-assoc;
        identityˡ = +-identityˡ;
        identityʳ = +-identityʳ
    }

ℕ*-monoid : Monoid ℕ _*_ 1
ℕ*-monoid =
    record {
        assoc = *-assoc;
        identityˡ = *-identityˡ;
        identityʳ = *-identityʳ
    }

List++-monoid : {A : Set} → Monoid (List A) _++_ []
List++-monoid =
    record {
        assoc = ++-assoc;
        identityˡ = ++-identityˡ;
        identityʳ = ++-identityʳ
    }

foldr-monoid : {A : Set} → (_⊗_ : A → A → A) → (e : A)
    → Monoid A _⊗_ e
    → (xs : List A) → (y : A)
    → foldr _⊗_ y xs ≡ (foldr _⊗_ e xs) ⊗ y
foldr-monoid _⊗_ e A⊗-monoid [] y = sym (A⊗-monoid .identityˡ y)
foldr-monoid _⊗_ e A⊗-monoid (x ∷ xs) y =
    begin
        x ⊗ (foldr _⊗_ y xs)
    ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e A⊗-monoid xs y) ⟩
        x ⊗ ((foldr _⊗_ e xs) ⊗ y)
    ≡⟨ sym (A⊗-monoid .assoc x (foldr _⊗_ e xs) y) ⟩
        (x ⊗ foldr _⊗_ e xs) ⊗ y
    ∎

foldr-monoid-++ : {A : Set} → (_⊗_ : A → A → A) → (e : A)
    → Monoid A _⊗_ e
    → (xs ys : List A)
    → foldr _⊗_ e (xs ++ ys) ≡ (foldr _⊗_ e xs) ⊗ (foldr _⊗_ e ys)
-- foldr-monoid-++ _⊗_ e A⊗-monoid [] ys = sym (A⊗-monoid .identityˡ (foldr _⊗_ e ys))
-- foldr-monoid-++ _⊗_ e A⊗-monoid (x ∷ xs) ys = trans (cong (x ⊗_) (foldr-monoid-++ _⊗_ e A⊗-monoid xs ys)) (sym (A⊗-monoid .assoc x (foldr _⊗_ e xs) (foldr _⊗_ e ys)))
foldr-monoid-++ _⊗_ e A⊗-monoid xs ys =
    begin
        foldr _⊗_ e (xs ++ ys)
    ≡⟨ foldr-++ _⊗_ e xs ys ⟩
        foldr _⊗_ (foldr _⊗_ e ys) xs
    ≡⟨ foldr-monoid _⊗_ e A⊗-monoid xs (foldr _⊗_ e ys) ⟩
        (foldr _⊗_ e xs) ⊗ (foldr _⊗_ e ys)
    ∎

foldl-monoid : {A : Set} → (_⊗_ : A → A → A) → (e : A)
    → Monoid A _⊗_ e
    → (xs : List A) → (y : A)
    → foldl _⊗_ y xs ≡ y ⊗ (foldl _⊗_ e xs)
foldl-monoid _⊗_ e A⊗-monoid [] y = sym (A⊗-monoid .identityʳ y)
foldl-monoid _⊗_ e A⊗-monoid (x ∷ xs) y =
    begin
        foldl _⊗_ (y ⊗ x) xs
    ≡⟨ foldl-monoid _⊗_ e A⊗-monoid xs (y ⊗ x) ⟩
        (y ⊗ x) ⊗ (foldl _⊗_ e xs)
    ≡⟨ A⊗-monoid .assoc y x (foldl _⊗_ e xs) ⟩
        y ⊗ (x ⊗ (foldl _⊗_ e xs))
    ≡⟨ cong (y ⊗_) (sym (foldl-monoid _⊗_ e A⊗-monoid xs x)) ⟩
        y ⊗ (foldl _⊗_ x xs)
    ≡⟨ cong (λ x → y ⊗ (foldl _⊗_ x xs)) (sym (A⊗-monoid .identityˡ x)) ⟩
        y ⊗ foldl _⊗_ (e ⊗ x) xs
    ∎

monoid-foldr-foldl : {A : Set} → (_⊗_ : A → A → A) → (e : A)
    → Monoid A _⊗_ e
    → (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
monoid-foldr-foldl _⊗_ e A⊗-monoid [] = refl
monoid-foldr-foldl _⊗_ e A⊗-monoid (x ∷ xs) =
    begin
        x ⊗ foldr _⊗_ e xs
    ≡⟨ cong (x ⊗_) (monoid-foldr-foldl _⊗_ e A⊗-monoid xs) ⟩
        x ⊗ foldl _⊗_ e xs
    ≡⟨ sym (foldl-monoid _⊗_ e A⊗-monoid xs x) ⟩
        foldl _⊗_ x xs
    ≡⟨ cong (λ x → foldl _⊗_ x xs) (sym (A⊗-monoid .identityˡ x)) ⟩
        foldl _⊗_ (e ⊗ x) xs
    ∎

data All {A : Set} (P : A → Set) : List A → Set where
    [] : All P []
    _∷_ : {x : A} → {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 ､ 1 ､ 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

data Any {A : Set} (P : A → Set) : List A → Set where
    here : {x : A} → {xs : List A} → P x → Any P (x ∷ xs)
    there : {x : A} → {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : {A : Set} → (x : A) → (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} → (x : A) → (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 ､ 1 ､ 0 ､ 2 ]
_ = here refl

_ : 0 ∈ [ 0 ､ 1 ､ 0 ､ 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 ､ 1 ､ 0 ､ 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

All-++-⇔ : {A : Set} → {P : A → Set}
    → (xs ys : List A)
    → All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ {A} {P} xs ys = record {
        to = to xs ys;
        from = from xs ys
    } where
        to : (xs ys : List A)
            → All P (xs ++ ys) → (All P xs × All P ys)
        to [] ys ps = [] , ps
        to (x ∷ xs) ys (p ∷ ps) = p ∷ (to xs ys ps .proj₁) , to xs ys ps .proj₂
        -- to (x ∷ xs) ys (p ∷ ps) with to xs ys ps
        -- ... | psx , psy = p ∷ psx , psy

        from : (xs ys : List A)
            → (All P xs × All P ys) → All P (xs ++ ys)
        from [] ys ([] , psy) = psy
        from (x ∷ xs) ys (px ∷ psx , psy) = px ∷ from xs ys (psx , psy)

Any-++-⇔ : {A : Set} → {P : A → Set}
    → (xs ys : List A)
    → Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ {A} {P} xs ys = record {
        to = to xs ys;
        from = from xs ys
    } where
        to : (xs ys : List A)
            → Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
        to [] ys ps = inj₂ ps
        to (x ∷ xs) ys (here px) = inj₁ (here px)
        to (x ∷ xs) ys (there ps) with to xs ys ps
        ... | inj₁ psx = inj₁ (there psx)
        ... | inj₂ psy = inj₂ psy

        from : (xs ys : List A)
            → (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
        from [] ys (inj₂ psy) = psy
        from (x ∷ xs) ys (inj₁ (here px)) = here px
        from (x ∷ xs) ys (inj₁ (there psx)) = there (from xs ys (inj₁ psx))
        from (x ∷ xs) ys (inj₂ psy) = there (from xs ys (inj₂ psy))

All-++-≅ : {A : Set} → {P : A → Set}
    → (xs ys : List A)
    → All P (xs ++ ys) ≅ (All P xs × All P ys)
All-++-≅ {A} {P} xs ys = record {
        to = to xs ys;
        from = from xs ys;
        from∘to = from∘to xs ys;
        to∘from = to∘from xs ys
    } where
        to : (xs ys : List A)
            → All P (xs ++ ys) → (All P xs × All P ys)
        to [] ys ps = [] , ps
        to (x ∷ xs) ys (p ∷ ps) = p ∷ to xs ys ps .proj₁ , to xs ys ps .proj₂
        -- to (x ∷ xs) ys (p ∷ ps) with to xs ys ps
        -- ... | psx , psy = (p ∷ psx) , psy

        from : (xs ys : List A)
            → (All P xs × All P ys) → All P (xs ++ ys)
        from [] ys ([] , psy) = psy
        from (x ∷ xs) ys (px ∷ psx , psy) = px ∷ from xs ys (psx , psy)

        from∘to : (xs ys : List A)
            → (ps : All P (xs ++ ys)) → from xs ys (to xs ys ps) ≡ ps
        from∘to [] ys ps = refl
        from∘to (x ∷ xs) ys (px ∷ ps) = cong (px ∷_) (from∘to xs ys ps)

        to∘from : (xs ys : List A)
            → (ps : All P xs × All P ys) → to xs ys (from xs ys ps) ≡ ps
        to∘from [] ys ([] , psy) = refl
        to∘from (x ∷ xs) ys (px ∷ psx , psy) =
            cong₂ _,_
                (cong (px ∷_) (cong proj₁ (to∘from xs ys (psx , psy))))
                (cong proj₂ (to∘from xs ys (psx , psy)))

¬Any⇔All¬ : {A : Set} → {P : A → Set}
    → (xs : List A)
    → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ {A} {P} xs = record {
        to = to xs;
        from = from xs
    } where
        to : (xs : List A)
            → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
        to [] _ = []
        to (x ∷ xs) f = (λ p → f (here p)) ∷ to xs λ ps → f (there ps)

        from : (xs : List A)
            → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
        from [] [] ()
        from (x ∷ xs) (f ∷ fs) (here p) = f p
        from (x ∷ xs) (f ∷ fs) (there ps) = from xs fs ps

Any¬→¬All : {A : Set} → {P : A → Set}
    → (xs : List A)
    → Any (¬_ ∘ P) xs → (¬_ ∘ All P) xs
Any¬→¬All (x ∷ xs) (here f) (p ∷ ps) = f p
Any¬→¬All (x ∷ xs) (there fs) (p ∷ ps) = Any¬→¬All xs fs ps

-- The converse cannot be disproved, c.f., see the comments of Σ¬→¬Π in Quantifiers.agda
-- The converse should be logically equivalent to excluded middle as well.

¬Any≃All¬ : {A : Set} → {P : A → Set}
    → (xs : List A)
    → (¬_ ∘ Any P) xs ≅ All (¬_ ∘ P) xs
¬Any≃All¬ {A} {P} xs = record {
        to = to xs;
        from = from xs;
        from∘to = from∘to xs;
        to∘from = to∘from xs
    } where
        to : (xs : List A)
            → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
        to [] _ = []
        to (x ∷ xs) f = (λ p → f (here p)) ∷ to xs λ ps → f (there ps)

        from : (xs : List A)
            → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
        from [] [] ()
        from (x ∷ xs) (f ∷ fs) (here p) = f p
        from (x ∷ xs) (f ∷ fs) (there ps) = from xs fs ps

        from∘to : (xs : List A)
            → (f : (¬_ ∘ Any P) xs) → from xs (to xs f) ≡ f
        from∘to [] f = extensionality λ ()
        from∘to (x ∷ xs) f = extensionality λ {
                (here p) → refl;
                (there ps) → ⊥-elim (f (there ps))
                -- (there ps) → cong-app (from∘to xs (λ qs → f (there qs))) ps
            }

        to∘from : (xs : List A)
            → (fs : All (¬_ ∘ P) xs) → to xs (from xs fs) ≡ fs
        to∘from [] [] = refl
        to∘from (x ∷ xs) (f ∷ fs) = cong (f ∷_) (to∘from xs fs)

All-Π : {A : Set} → {P : A → Set}
    → (xs : List A)
    → All P xs ≅ ((x : A) → (x ∈ xs) → P x)
All-Π {A} {P} xs = record {
        to = to xs;
        from = from xs;
        from∘to = from∘to xs;
        to∘from = to∘from xs
    } where
        to : (xs : List A)
            → All P xs → ((x : A) → (x ∈ xs) → P x)
        to [] [] _ ()
        to (x ∷ xs) (p ∷ ps) y (here q) = subst P (sym  q) p
        to (x ∷ xs) (p ∷ ps) y (there qs) = to xs ps y qs

        from : (xs : List A)
            → ((x : A) → (x ∈ xs) → P x) → All P xs
        from [] f = []
        from (x ∷ xs) f = (f x (here refl)) ∷ from xs (λ y q → f y (there q))

        from∘to : (xs : List A)
            → (ps : All P xs) → from xs (to xs ps) ≡ ps
        from∘to [] [] = refl
        from∘to (x ∷ xs) (p ∷ ps) = cong (p ∷_) (from∘to xs ps)

        to∘from : (xs : List A)
            → (f : (x : A) → (x ∈ xs) → P x) → to xs (from xs f) ≡ f
        to∘from [] f = Π-extensionality λ x → extensionality λ ()
        to∘from (x ∷ xs) f = Π-extensionality λ x → extensionality λ {
                (here refl) → refl;
                (there qs) → (cong-app (cong-app (to∘from xs (λ y q → f y (there q))) x) qs)
            }

Any-Σ : {A : Set} → {P : A → Set}
    → (xs : List A)
    → Any P xs ≅ Σ A (λ x → x ∈ xs × P x)
Any-Σ {A} {P} xs = record {
        to = to xs;
        from = from xs;
        from∘to = from∘to xs;
        to∘from = to∘from xs
    } where
        to : (xs : List A)
            → Any P xs → Σ A (λ x → x ∈ xs × P x)
        to (x ∷ xs) (here p) = x , here refl , p
        to (x ∷ xs) (there ps) = to xs ps .proj₁ , there (to xs ps .proj₂ .proj₁) , to xs ps .proj₂ .proj₂

        from : (xs : List A)
            → Σ A (λ x → x ∈ xs × P x) → Any P xs
        from (x ∷ xs) (y , here p , q) = here (subst P p q)
        from (x ∷ xs) (y , there ps , q) = there (from xs (y , ps , q))

        from∘to : (xs : List A)
            → (ps : Any P xs) → from xs (to xs ps) ≡ ps
        from∘to (x ∷ xs) (here p) = refl
        from∘to (x ∷ xs) (there ps) = cong there (from∘to xs ps)

        to∘from : (xs : List A)
            → (pair : Σ A (λ x → x ∈ xs × P x)) → to xs (from xs pair) ≡ pair
        to∘from (x ∷ xs) (.x , here refl , q) = refl
        to∘from (x ∷ xs) (y , there ps , q) = cong (λ { (y , ps , q) → (y , there ps , q) }) (to∘from xs (y , ps , q))
        -- to∘from (x ∷ xs) (y , there ps , q) = cong (λ pair → (pair .proj₁ , there (pair .proj₂ .proj₁) , pair .proj₂ .proj₂)) (to∘from xs (y , ps , q))

all : {A : Set} → (A → Bool) → List A → Bool
all p = (foldr _∧_ true) ∘ (map p)

DecP : {A : Set} → (P : A → Set) → Set
DecP {A} P = (x : A) → Dec (P x)

All? : {A : Set} → {P : A → Set} → DecP P → DecP (All P)
All? P? [] = yes []
All? P? (x ∷ xs) with P? x | All? P? xs
... | no f | _ = no λ { (p ∷ ps) → f p }
... | yes _ | no g = no λ { (p ∷ ps) → g ps }
... | yes p | yes ps = yes (p ∷ ps)

Any? : {A : Set} → {P : A → Set} → DecP P → DecP (Any P)
Any? P? [] = no λ ()
Any? P? (x ∷ xs) with P? x | Any? P? xs
... | no f | no g = no λ { (here x) → f x; (there ps) → g ps }
... | no _ | yes ps = yes (there ps)
... | yes p | _ = yes (here p)

data IsMerge {A : Set} : List A → List A → List A → Set where
    [] : IsMerge [] [] []
    left-∷ : {x : A} → {xs ys zs : List A} → IsMerge xs ys zs → IsMerge (x ∷ xs) ys (x ∷ zs)
    right-∷ : {y : A} → {xs ys zs : List A} → IsMerge xs ys zs → IsMerge xs (y ∷ ys) (y ∷ zs)

_ : IsMerge [ 1 ､ 4 ] [ 2 ､ 3 ] [ 1 ､ 2 ､ 3 ､ 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))

split : {A : Set} → {P : A → Set}
    → (P? : DecP P) → (zs : List A)
    → Σ (List A) (λ xs → Σ (List A) (λ ys → IsMerge xs ys zs × All P xs × All (¬_ ∘ P) ys))
split P? [] = [] , [] , [] , [] , []
split P? (z ∷ zs) with P? z | split P? zs
... | no f | xs , ys , merge , ps , fs = xs , z ∷ ys , right-∷ merge , ps , f ∷ fs
... | yes p | xs , ys , merge , ps , fs = z ∷ xs , ys , left-∷ merge , p ∷ ps , fs

-- import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
-- import Data.List.Relation.Unary.All using (All; []; _∷_)
-- import Data.List.Relation.Unary.Any using (Any; here; there)
-- import Data.List.Membership.Propositional using (_∈_)
-- -- import Data.List.Properties (reverse-++-commute; map-compose; map-++-commute; foldr-++) renaming (mapIsFold to map-is-foldr)
-- import Algebra.Structures using (IsMonoid)
-- import Relation.Unary using (Decidable)
-- import Relation.Binary using (Decidable)
