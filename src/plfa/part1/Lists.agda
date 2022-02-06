{-# OPTIONS --without-K #-}
-- {-# OPTIONS --without-K --guardedness #-}

module plfa.part1.Lists where

open import Agda.Primitive

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; +-comm; *-assoc; *-identityˡ; *-identityʳ; *-comm)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Functional using (Vector)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import Level using (Level)

open import plfa.part1.Equality using (cong₃; subst-cong; subst₂; subst-cong₂; subst-const; subst₂-const; subst≡subst×subst; subst₂≡subst₂×subst₂; subst₂≡subst×subst; subst-refl-r)
open import plfa.part1.Isomorphism using (_≅_; extensionality; Π-extensionality; _⇔_; Is-hProp; Is-hSet; Is-hGroupoid; ⊤-Is-hProp; ⊥-Is-hProp; ×-Is-hProp; Unit; unit; Empty; Unit-Is-hProp; Empty-Is-hProp; ≅-Is-hProp; ≅-Is-hSet; hProp-iso)
open import plfa.part1.Quantifiers using (ℕ-Is-hSet)

private
    variable
        i j k l : Level

-- data List (A : Set i) : Set i where
--     [] : List A
--     _∷_ : A → List A → List A
-- infixr 5 _∷_
-- {-# BUILTIN LIST List #-}

-- record Stream (A : Set i) : Set i where
--     coinductive
--     constructor cons
--     field
--         head : A
--         tail : Stream A

-- record CoList (A : Set i) : Set i where
--     coinductive
--     field
--         unfold : Maybe (A × CoList A)

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

_ : List ℕ
_ = _∷_ {A = ℕ} 0 (_∷_ {A = ℕ} 1 (_∷_ {A = ℕ} 2 ([] {A = ℕ})))

data List′ {i} : Set i → Set (lsuc i) where -- note if we disable --without-K, List′ can be defined at Set i → Set i
    []′  : {A : Set i} → List′ A -- see https://agda.readthedocs.io/en/latest/language/without-k.html
    _∷′_ : {A : Set i} → A → List′ A → List′ A -- also https://github.com/HoTT/HoTT/issues/842

-- currently I do not understand the difference between this indexed inductive family definition and the above parameterized inductive definition under --without-K
-- see https://stackoverflow.com/questions/66254425/why-does-universe-level-restriction-behave-differently-between-inductive-family

-- data _≡′_ {ℓ} {A : Set ℓ} (x : A) : A → Set where
--     refl : x ≡′ x

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

-- infixr 5 _++_
-- _++_ : {A : Set i} → List A → List A → List A
-- [] ++ ys = ys
-- (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

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

++-assoc : {A : Set i} → (xs ys zs : List A)
    → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identityˡ : {A : Set i} → (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : {A : Set i} → (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

length : {A : Set i} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

_ : length [ 0 ､ 1 ､ 2 ] ≡ 3
_ = refl

_ : length {A = ℕ} [] ≡ 0
_ = refl

length-++ : {A : Set i} → (xs ys : List A)
    → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

reverse : {A : Set i} → List A → List A
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

reverse-++-distrib : {A : Set i} → (xs ys : List A)
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

reverse-involutive : {A : Set i} → (xs : List A)
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

shunt : {A : Set i} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : {A : Set i} → (xs ys : List A)
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

reverse′ : {A : Set i} → List A → List A
reverse′ xs = shunt xs []

reverses : {A : Set i} → (xs : List A)
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

map : {A : Set i} → {B : Set j} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-d : {A : Set i} → {B : A → Set j}
    → ((x : A) → B x) → List A → List (Σ A B)
map-d f [] = []
map-d f (x ∷ xs) = (x , f x) ∷ map-d f xs

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

map-compose : {A : Set i} → {B : Set j} → {C : Set k}
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

map-++-distribute : {A : Set i} → {B : Set j}
    → (f : A → B)
    → (xs ys : List A)
    → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys = cong (f x ∷_) (map-++-distribute f xs ys)

data Tree (A : Set i) : Set i where
    leaf : Tree A
    node : A → Tree A → Tree A → Tree A

-- record InfTree (A : Set i) : Set i where
--     coinductive
--     field
--         value : A
--         left : InfTree A
--         right : InfTree A

-- record CoTree (A : Set i) : Set i where
--     coinductive
--     field
--         unfold : Maybe (A × CoTree A × CoTree A)

mapTree : {A : Set i} → {B : Set j} → (A → B) → Tree A → Tree B
mapTree f leaf = leaf
mapTree f (node x t1 t2) = node (f x) (mapTree f t1) (mapTree f t2)

foldr : {A : Set i} → {B : Set j} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

foldl : {A : Set i} → {B : Set j} → (B → A → B) → B → List A → B
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

foldr-++ : {A : Set i} → {B : Set j} → (_⊗_ : A → B → B) → (e : B)
    → (xs ys : List A)
    → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys = cong (x ⊗_) (foldr-++ _⊗_ e xs ys)

foldr-∷ : {A : Set i} → (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) = cong (x ∷_) (foldr-∷ xs)

foldr-++-List : {A : Set i} → (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
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

map-foldr : {A : Set i} → {B : Set j} → (f : A → B) → (xs : List A)
    → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
map-foldr f [] = refl
map-foldr f (x ∷ xs) = cong (f x ∷_) (map-foldr f xs)

foldTree : {A : Set i} → {B : Set j}
    → B
    → (A → B → B → B)
    → Tree A → B
foldTree bleaf bnode leaf = bleaf
foldTree bleaf bnode (node x t1 t2) = bnode x (foldTree bleaf bnode t1) (foldTree bleaf bnode t2)

foldList : {A : Set i} → {B : Set j}
    → B
    → (A → B → B)
    → List A → B
foldList bnil bcons [] = bnil
foldList bnil bcons (x ∷ xs) = bcons x (foldList bnil bcons xs)

foldList-l : {A : Set i} → {B : Set j}
    → B
    → (B → A → B)
    → List A → B
foldList-l bnil bcons [] = bnil
foldList-l bnil bcons (x ∷ xs) = foldList-l (bcons bnil x) bcons xs

mapTree-foldTree : {A : Set i} → {B : Set j} → (f : A → B) → (t : Tree A)
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

record Monoid (A : Set i) (_⊗_ : A → A → A) (e : A) : Set i where
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

List++-monoid : {A : Set i} → Monoid (List A) _++_ []
List++-monoid =
    record {
        assoc = ++-assoc;
        identityˡ = ++-identityˡ;
        identityʳ = ++-identityʳ
    }

foldr-monoid : {A : Set i} → (_⊗_ : A → A → A) → (e : A)
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

foldr-monoid-++ : {A : Set i} → (_⊗_ : A → A → A) → (e : A)
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

foldl-monoid : {A : Set i} → (_⊗_ : A → A → A) → (e : A)
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

monoid-foldr-foldl : {A : Set i} → (_⊗_ : A → A → A) → (e : A)
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

-- data All {A : Set i} (P : A → Set j) : List A → Set (i ⊔ j) where
--     [] : All P []
--     _∷_ : {x : A} → {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 ､ 1 ､ 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

-- data Any {A : Set i} (P : A → Set j) : List A → Set (i ⊔ j) where
--     here : {x : A} → {xs : List A} → P x → Any P (x ∷ xs)
--     there : {x : A} → {xs : List A} → Any P xs → Any P (x ∷ xs)

-- infix 4 _∈_ _∉_

-- _∈_ : {A : Set i} → (x : A) → (xs : List A) → Set i
-- x ∈ xs = Any (x ≡_) xs

-- _∉_ : {A : Set i} → (x : A) → (xs : List A) → Set i
-- x ∉ xs = ¬ (x ∈ xs)

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

All-++-⇔ : {A : Set i} → {P : A → Set j}
    → (xs ys : List A)
    → All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ {A = A} {P} xs ys = record {
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

Any-++-⇔ : {A : Set i} → {P : A → Set j}
    → (xs ys : List A)
    → Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ {A = A} {P} xs ys = record {
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

All-++-≅ : {A : Set i} → {P : A → Set j}
    → (xs ys : List A)
    → All P (xs ++ ys) ≅ (All P xs × All P ys)
All-++-≅ {A = A} {P} xs ys = record {
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

Any-++-≅ : {A : Set i} → {P : A → Set j}
    → (xs ys : List A)
    → Any P (xs ++ ys) ≅ (Any P xs ⊎ Any P ys)
Any-++-≅ {A = A} {P} xs ys = record {
        to = to xs ys;
        from = from xs ys;
        from∘to = from∘to xs ys;
        to∘from = to∘from xs ys
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

        from∘to : (xs ys : List A)
            → (ps : Any P (xs ++ ys)) → from xs ys (to xs ys ps) ≡ ps
        from∘to [] ys ps = refl
        from∘to (x ∷ xs) ys (here px) = refl
        from∘to (x ∷ xs) ys (there ps) with to xs ys ps | from∘to xs ys ps -- use simultaneous with: https://agda.readthedocs.io/en/latest/language/with-abstraction.html#simultaneous-abstraction
        ... | inj₁ psx | refl = refl
        ... | inj₂ psy | refl = refl
        -- from∘to (x ∷ xs) ys (there ps) with to xs ys ps in eq -- another option is using with abstraction equality: https://agda.readthedocs.io/en/latest/language/with-abstraction.html#with-abstraction-equality
        -- ... | inj₁ psx = cong there (trans (cong (from xs ys) (sym eq)) (from∘to xs ys ps))
        -- ... | inj₂ psy = cong there (trans (cong (from xs ys) (sym eq)) (from∘to xs ys ps))

        to∘from : (xs ys : List A)
            → (ps : Any P xs ⊎ Any P ys) → to xs ys (from xs ys ps) ≡ ps
        to∘from [] ys (inj₂ psy) = refl
        to∘from (x ∷ xs) ys (inj₁ (here px)) = refl
        to∘from (x ∷ xs) ys (inj₁ (there psx)) with to xs ys (from xs ys (inj₁ psx)) | to∘from xs ys (inj₁ psx)
        ... | .(inj₁ psx) | refl = refl
        -- to∘from (x ∷ xs) ys (inj₁ (there psx)) with to xs ys (from xs ys (inj₁ psx)) in eq
        -- ... | inj₁ psx′ = cong (inj₁ ∘ there) (inj₁-injective (sym (trans (sym (to∘from xs ys (inj₁ psx))) eq)))
        -- ... | inj₂ psy′ with trans (sym (to∘from xs ys (inj₁ psx))) eq
        -- ... | ()
        to∘from (x ∷ xs) ys (inj₂ psy) with to xs ys (from xs ys (inj₂ psy)) | to∘from xs ys (inj₂ psy)
        ... | .(inj₂ psy) | refl = refl
        -- to∘from (x ∷ xs) ys (inj₂ psy) with to xs ys (from xs ys (inj₂ psy)) in eq
        -- ... | inj₁ psx′ with trans (sym (to∘from xs ys (inj₂ psy))) eq
        -- ... | ()
        -- to∘from (x ∷ xs) ys (inj₂ psy) | inj₂ psy′ = cong inj₂ (inj₂-injective (sym (trans (sym (to∘from xs ys (inj₂ psy))) eq)))

¬Any⇔All¬ : {A : Set i} → {P : A → Set j}
    → (xs : List A)
    → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ {A = A} {P} xs = record {
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

Any¬→¬All : {A : Set i} → {P : A → Set j}
    → (xs : List A)
    → Any (¬_ ∘ P) xs → (¬_ ∘ All P) xs
Any¬→¬All (x ∷ xs) (here f) (p ∷ ps) = f p
Any¬→¬All (x ∷ xs) (there fs) (p ∷ ps) = Any¬→¬All xs fs ps

-- The converse cannot be disproved, c.f., see the comments of Σ¬→¬Π in Quantifiers.agda
-- The converse should be logically equivalent to excluded middle as well.

¬Any≃All¬ : {A : Set i} → {P : A → Set j}
    → (xs : List A)
    → (¬_ ∘ Any P) xs ≅ All (¬_ ∘ P) xs
¬Any≃All¬ {A = A} {P} xs = record {
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

All-Π : {A : Set i} → {P : A → Set j}
    → (xs : List A)
    → All P xs ≅ ((x : A) → (x ∈ xs) → P x)
All-Π {A = A} {P} xs = record {
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

Any-Σ : {A : Set i} → {P : A → Set j}
    → (xs : List A)
    → Any P xs ≅ Σ A (λ x → x ∈ xs × P x)
Any-Σ {A = A} {P} xs = record {
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

all : {A : Set i} → (A → Bool) → List A → Bool
all p = (foldr _∧_ true) ∘ (map p)

DecP : {A : Set i} → (P : A → Set j) → Set (i ⊔ j)
DecP {A = A} P = (x : A) → Dec (P x)

All? : {A : Set i} → {P : A → Set j} → DecP P → DecP (All P)
All? P? [] = yes []
All? P? (x ∷ xs) with P? x | All? P? xs
... | no f | _ = no λ { (p ∷ ps) → f p }
... | yes _ | no g = no λ { (p ∷ ps) → g ps }
... | yes p | yes ps = yes (p ∷ ps)

Any? : {A : Set i} → {P : A → Set j} → DecP P → DecP (Any P)
Any? P? [] = no λ ()
Any? P? (x ∷ xs) with P? x | Any? P? xs
... | no f | no g = no λ { (here x) → f x; (there ps) → g ps }
... | no _ | yes ps = yes (there ps)
... | yes p | _ = yes (here p)

data IsMerge {A : Set i} : List A → List A → List A → Set i where
    [] : IsMerge [] [] []
    left-∷ : {x : A} → {xs ys zs : List A} → IsMerge xs ys zs → IsMerge (x ∷ xs) ys (x ∷ zs)
    right-∷ : {y : A} → {xs ys zs : List A} → IsMerge xs ys zs → IsMerge xs (y ∷ ys) (y ∷ zs)

_ : IsMerge [ 1 ､ 4 ] [ 2 ､ 3 ] [ 1 ､ 2 ､ 3 ､ 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))

split : {A : Set i} → {P : A → Set j}
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

-- Bonus: use encode-decode to prove List-Is-hSet, Tree-Is-hSet, Vec-Is-hSet

CodeList : {A : Set i} → List A → List A → Set i
CodeList [] [] = Unit
CodeList [] (x ∷ ys) = Empty
CodeList (x ∷ xs) [] = Empty
CodeList (x ∷ xs) (y ∷ ys) = x ≡ y × CodeList xs ys

rList : {A : Set i} → (xs : List A) → CodeList xs xs
rList [] = unit
rList (x ∷ xs) = refl , (rList xs)

List-eq≅CodeList : {A : Set i} → (xs ys : List A) → xs ≡ ys ≅ CodeList xs ys
List-eq≅CodeList xs ys = record {
        to = encodeList xs ys;
        from = decodeList xs ys;
        from∘to = decodeList-encodeList xs ys;
        to∘from = encodeList-decodeList xs ys
    } where
        encodeList : {A : Set i} → (xs ys : List A) → xs ≡ ys → CodeList xs ys
        encodeList xs .xs refl = rList xs
        -- encodeList xs ys ps = subst (CodeList xs) ps (rList xs)

        decodeList : {A : Set i} → (xs ys : List A) → CodeList xs ys → xs ≡ ys
        decodeList [] [] unit = refl
        decodeList (x ∷ xs) (.x ∷ ys) (refl , code) = cong (x ∷_) (decodeList xs ys code)
        -- decodeList (x ∷ xs) (y ∷ ys) (p , code) = cong₂ _∷_ p (decodeList xs ys code)

        decodeList-encodeList : {A : Set i} → (xs ys : List A) → (ps : xs ≡ ys)
            → decodeList xs ys (encodeList xs ys ps) ≡ ps
        decodeList-encodeList [] [] refl = refl
        decodeList-encodeList (x ∷ xs) (.x ∷ .xs) refl = cong (cong (x ∷_)) (decodeList-encodeList xs xs refl)
        -- decodeList-encodeList (x ∷ xs) (.x ∷ .xs) refl = cong (cong₂ _∷_ refl) (decodeList-encodeList xs xs refl)

        encodeList-decodeList : {A : Set i} → (xs ys : List A) → (code : CodeList xs ys)
            → encodeList xs ys (decodeList xs ys code) ≡ code
        encodeList-decodeList [] [] unit = refl
        encodeList-decodeList (x ∷ xs) (.x ∷ ys) (refl , code) with decodeList xs ys code | encodeList-decodeList xs ys code
        ... | refl | refl = refl

        -- encodeList-decodeList : {A : Set i} → (xs ys : List A) → (code : CodeList xs ys)
        --     → encodeList xs ys (decodeList xs ys code) ≡ code
        -- encodeList-decodeList [] [] unit = refl
        -- encodeList-decodeList (x ∷ xs) (.x ∷ ys) (refl , code) =
        --     begin
        --         encodeList (x ∷ xs) (x ∷ ys) (decodeList (x ∷ xs) (x ∷ ys) (refl , code))
        --     ≡⟨⟩
        --         encodeList (x ∷ xs) (x ∷ ys) (cong (x ∷_) (decodeList xs ys code))
        --     ≡⟨⟩
        --         subst (CodeList (x ∷ xs)) (cong (x ∷_) (decodeList xs ys code)) (rList (x ∷ xs))
        --     ≡⟨ subst-cong (CodeList (x ∷ xs)) (decodeList xs ys code) ⟩
        --         subst (λ ys → CodeList (x ∷ xs) (x ∷ ys)) (decodeList xs ys code) (rList (x ∷ xs))
        --     ≡⟨⟩
        --         subst (λ ys → x ≡ x × CodeList xs ys) (decodeList xs ys code) (refl , (rList xs))
        --     ≡⟨ subst≡subst×subst (λ ys → x ≡ x) (CodeList xs) (decodeList xs ys code) ⟩
        --         subst (λ _ → x ≡ x) (decodeList xs ys code) refl , subst (CodeList xs) (decodeList xs ys code) (rList xs)
        --     ≡⟨⟩
        --         subst (λ _ → x ≡ x) (decodeList xs ys code) refl , encodeList xs ys (decodeList xs ys code)
        --     ≡⟨ cong₂ _,_ (subst-const (x ≡ x) (decodeList xs ys code)) (encodeList-decodeList xs ys code) ⟩
        --         refl , code
        --     ∎

        -- encodeList-decodeList : {A : Set i} → (xs ys : List A) → (code : CodeList xs ys)
        --     → encodeList xs ys (decodeList xs ys code) ≡ code
        -- encodeList-decodeList [] [] unit = refl
        -- encodeList-decodeList (x ∷ xs) (.x ∷ ys) (refl , code) =
        --     begin
        --         encodeList (x ∷ xs) (y ∷ ys) (decodeList (x ∷ xs) (y ∷ ys) (p , code))
        --     ≡⟨⟩
        --         encodeList (x ∷ xs) (y ∷ ys) (cong₂ _∷_ p (decodeList xs ys code))
        --     ≡⟨⟩
        --         subst (CodeList (x ∷ xs)) (cong₂ _∷_ p (decodeList xs ys code)) (rList (x ∷ xs))
        --     ≡⟨ subst-cong₂ (CodeList (x ∷ xs)) p (decodeList xs ys code) ⟩
        --         subst₂ (λ y ys → CodeList (x ∷ xs) (y ∷ ys)) p (decodeList xs ys code) (rList (x ∷ xs))
        --     ≡⟨⟩
        --         subst₂ (λ y ys → x ≡ y × CodeList xs ys) p (decodeList xs ys code) (refl , (rList xs))
        --     ≡⟨ subst₂≡subst×subst (x ≡_) (CodeList xs) p (decodeList xs ys code) ⟩
        --         subst (x ≡_) p refl , subst (CodeList xs) (decodeList xs ys code) (rList xs)
        --     ≡⟨⟩
        --         subst (x ≡_) p refl , encodeList xs ys (decodeList xs ys code)
        --     ≡⟨ cong₂ _,_ (subst-refl-r p) (encodeList-decodeList xs ys code) ⟩
        --         p , code
        --     ∎

CodeList-Is-hProp : {A : Set i} → Is-hSet A → (xs ys : List A) → Is-hProp (CodeList xs ys)
CodeList-Is-hProp is-hSet [] [] = Unit-Is-hProp
CodeList-Is-hProp is-hSet (x ∷ xs) (y ∷ ys) = ×-Is-hProp (is-hSet x y) (CodeList-Is-hProp is-hSet xs ys)

List-Is-hSet : {A : Set i} → Is-hSet A → Is-hSet (List A)
List-Is-hSet is-hSet xs ys = ≅-Is-hProp (List-eq≅CodeList xs ys) (CodeList-Is-hProp is-hSet xs ys)

All-Is-hProp : {A : Set i} → {P : A → Set j} → ({x : A} → Is-hProp (P x)) → {xs : List A} → Is-hProp (All P xs)
All-Is-hProp are-hProps {[]} [] [] = refl
All-Is-hProp are-hProps {x ∷ xs} (p ∷ ps) (q ∷ qs) = cong₂ _∷_ (are-hProps p q) (All-Is-hProp are-hProps ps qs)

CodeTree : {A : Set i} → Tree A → Tree A → Set i
CodeTree leaf leaf = Unit
CodeTree leaf (node y tree₂₁ tree₂₂) = Empty
CodeTree (node x tree₁₁ tree₁₂) leaf = Empty
CodeTree (node x tree₁₁ tree₁₂) (node y tree₂₁ tree₂₂) = x ≡ y × CodeTree tree₁₁ tree₂₁ × CodeTree tree₁₂ tree₂₂

rTree : {A : Set i} → (tree : Tree A) → CodeTree tree tree
rTree leaf = unit
rTree (node x tree₁ tree₂) = refl , rTree tree₁ , rTree tree₂

Tree-eq≅CodeTree : {A : Set i} → (tree₁ tree₂ : Tree A) → tree₁ ≡ tree₂ ≅ CodeTree tree₁ tree₂
Tree-eq≅CodeTree tree₁ tree₂ = record {
        to = encodeTree tree₁ tree₂;
        from = decodeTree tree₁ tree₂;
        from∘to = decodeTree-encodeTree tree₁ tree₂;
        to∘from = encodeTree-decodeTree tree₁ tree₂
    } where
        encodeTree : {A : Set i} → (tree₁ tree₂ : Tree A) → tree₁ ≡ tree₂ → CodeTree tree₁ tree₂
        encodeTree tree₁ .tree₁ refl = rTree tree₁
        -- encodeTree tree₁ tree₂ p = subst (CodeTree tree₁) p (rTree tree₁)

        decodeTree : {A : Set i} → (tree₁ tree₂ : Tree A) → CodeTree tree₁ tree₂ → tree₁ ≡ tree₂
        decodeTree leaf leaf unit = refl
        decodeTree (node x tree₁₁ tree₁₂) (node .x tree₂₁ tree₂₂) (refl , code₁ , code₂) = cong₂ (node x) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂)

        decodeTree-encodeTree : {A : Set i} → (tree₁ tree₂ : Tree A) → (p : tree₁ ≡ tree₂)
            → decodeTree tree₁ tree₂ (encodeTree tree₁ tree₂ p) ≡ p
        decodeTree-encodeTree leaf leaf refl = refl
        decodeTree-encodeTree (node x tree₁₁ tree₁₂) (node .x .tree₁₁ .tree₁₂) refl = cong₂ (cong₂ (node x)) (decodeTree-encodeTree tree₁₁ tree₁₁ refl) (decodeTree-encodeTree tree₁₂ tree₁₂ refl)
            -- begin
            --     decodeTree (node x tree₁₁ tree₁₂) (node x tree₁₁ tree₁₂) (encodeTree (node x tree₁₁ tree₁₂) (node x tree₁₁ tree₁₂) refl)
            -- ≡⟨⟩
            --     decodeTree (node x tree₁₁ tree₁₂) (node x tree₁₁ tree₁₂) (refl , rTree tree₁₁ , rTree tree₁₂)
            -- ≡⟨⟩
            --     cong₂ (node x) (decodeTree tree₁₁ tree₁₁ (rTree tree₁₁)) (decodeTree tree₁₂ tree₁₂ (rTree tree₁₂))
            -- ≡⟨⟩
            --     cong₂ (node x) (decodeTree tree₁₁ tree₁₁ (encodeTree tree₁₁ tree₁₁ refl)) (decodeTree tree₁₂ tree₁₂ (encodeTree tree₁₂ tree₁₂ refl))
            -- ≡⟨ cong₂ (cong₂ (node x)) (decodeTree-encodeTree tree₁₁ tree₁₁ refl) (decodeTree-encodeTree tree₁₂ tree₁₂ refl) ⟩
            --     cong₂ (node x) refl refl
            -- ≡⟨⟩
            --     refl
            -- ∎

        encodeTree-decodeTree : {A : Set i} → (tree₁ tree₂ : Tree A) → (code : CodeTree tree₁ tree₂)
            → encodeTree tree₁ tree₂ (decodeTree tree₁ tree₂ code) ≡ code
        encodeTree-decodeTree leaf leaf unit = refl
        encodeTree-decodeTree (node x tree₁₁ tree₁₂) (node .x tree₂₁ tree₂₂) (refl , code₁ , code₂)
            with
                decodeTree tree₁₁ tree₂₁ code₁ |
                decodeTree tree₁₂ tree₂₂ code₂ |
                encodeTree-decodeTree tree₁₁ tree₂₁ code₁ |
                encodeTree-decodeTree tree₁₂ tree₂₂ code₂
        ... | refl | refl | refl | refl = refl

        -- encodeTree-decodeTree : {A : Set i} → (tree₁ tree₂ : Tree A) → (code : CodeTree tree₁ tree₂)
        --     → encodeTree tree₁ tree₂ (decodeTree tree₁ tree₂ code) ≡ code
        -- encodeTree-decodeTree leaf leaf unit = refl
        -- encodeTree-decodeTree (node x tree₁₁ tree₁₂) (node .x tree₂₁ tree₂₂) (refl , code₁ , code₂) =
        --     begin
        --         encodeTree (node x tree₁₁ tree₁₂) (node x tree₂₁ tree₂₂) (decodeTree (node x tree₁₁ tree₁₂) (node x tree₂₁ tree₂₂) (refl , code₁ , code₂))
        --     ≡⟨⟩
        --         encodeTree (node x tree₁₁ tree₁₂) (node x tree₂₁ tree₂₂) (cong₂ (node x) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂))
        --     ≡⟨⟩
        --         subst (CodeTree (node x tree₁₁ tree₁₂)) (cong₂ (node x) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂)) (refl , rTree tree₁₁ , rTree tree₁₂)
        --     ≡⟨ subst-cong₂ (CodeTree (node x tree₁₁ tree₁₂)) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) ⟩
        --         subst₂ (λ tree₂₁ tree₂₂ → CodeTree (node x tree₁₁ tree₁₂) (node x tree₂₁ tree₂₂)) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) (refl , rTree tree₁₁ , rTree tree₁₂)
        --     ≡⟨⟩
        --         subst₂ (λ tree₂₁ tree₂₂ → x ≡ x × CodeTree tree₁₁ tree₂₁ × CodeTree tree₁₂ tree₂₂) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) (refl , rTree tree₁₁ , rTree tree₁₂)
        --     ≡⟨ subst₂≡subst₂×subst₂ (λ _ _ → x ≡ x) (λ tree₂₁ tree₂₂ → CodeTree tree₁₁ tree₂₁ × CodeTree tree₁₂ tree₂₂) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) ⟩
        --         subst₂ (λ tree₂₁ tree₂₂ → x ≡ x) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) refl , subst₂ (λ tree₂₁ tree₂₂ → CodeTree tree₁₁ tree₂₁ × CodeTree tree₁₂ tree₂₂) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) (rTree tree₁₁ , rTree tree₁₂)
        --     ≡⟨ cong (subst₂ (λ tree₂₁ tree₂₂ → x ≡ x) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) refl ,_) (subst₂≡subst×subst (CodeTree tree₁₁) (CodeTree tree₁₂) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂)) ⟩
        --         subst₂ (λ tree₂₁ tree₂₂ → x ≡ x) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) refl , subst (CodeTree tree₁₁) (decodeTree tree₁₁ tree₂₁ code₁) (rTree tree₁₁) , subst (CodeTree tree₁₂) (decodeTree tree₁₂ tree₂₂ code₂) (rTree tree₁₂)
        --     ≡⟨⟩
        --         subst₂ (λ tree₂₁ tree₂₂ → x ≡ x) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂) refl , encodeTree tree₁₁ tree₂₁ (decodeTree tree₁₁ tree₂₁ code₁) , encodeTree tree₁₂ tree₂₂ (decodeTree tree₁₂ tree₂₂ code₂)
        --     ≡⟨ cong₃ (λ a b c → a , b , c) (subst₂-const (x ≡ x) (decodeTree tree₁₁ tree₂₁ code₁) (decodeTree tree₁₂ tree₂₂ code₂)) (encodeTree-decodeTree tree₁₁ tree₂₁ code₁) (encodeTree-decodeTree tree₁₂ tree₂₂ code₂) ⟩
        --         refl , code₁ , code₂
        --     ∎

CodeTree-Is-hProp : {A : Set i} → Is-hSet A → (xs ys : Tree A) → Is-hProp (CodeTree xs ys)
CodeTree-Is-hProp is-hSet leaf leaf = Unit-Is-hProp
CodeTree-Is-hProp is-hSet (node x tree₁₁ tree₁₂) (node y tree₂₁ tree₂₂) = ×-Is-hProp (is-hSet x y) (×-Is-hProp (CodeTree-Is-hProp is-hSet tree₁₁ tree₂₁) (CodeTree-Is-hProp is-hSet tree₁₂ tree₂₂))

Tree-Is-hSet : {A : Set i} → Is-hSet A → Is-hSet (Tree A)
Tree-Is-hSet is-hSet tree₁ tree₂ = ≅-Is-hProp (Tree-eq≅CodeTree tree₁ tree₂) (CodeTree-Is-hProp is-hSet tree₁ tree₂)

-- data Vec (A : Set i) : ℕ → Set i where
--     [] : Vec A zero
--     _∷_ : {k : ℕ} → (x : A) → (xs : Vec A k) → Vec A (suc n)

CodeVec : {A : Set i} → {k : ℕ} → Vec A k → Vec A k → Set i
CodeVec [] [] = Unit
CodeVec (x ∷ xs) (y ∷ ys) = x ≡ y × (CodeVec xs ys)

rVec : {A : Set i} → {k : ℕ} → (xs : Vec A k) → CodeVec xs xs
rVec [] = unit
rVec (x ∷ xs) = refl , (rVec xs)

Vec-eq≅CodeVec : {A : Set i} → {k : ℕ} → (xs ys : Vec A k) → xs ≡ ys ≅ CodeVec xs ys
Vec-eq≅CodeVec xs ys = record {
        to = encodeVec xs ys;
        from = decodeVec xs ys;
        from∘to = decodeVec-encodeVec xs ys;
        to∘from = encodeVec-decodeVec xs ys
    } where
        encodeVec : {A : Set i} → {k : ℕ} → (xs ys : Vec A k) → xs ≡ ys → CodeVec xs ys
        encodeVec xs .xs refl = rVec xs
        -- encodeVec xs ys ps = subst (CodeVec xs) ps (rVec xs)

        decodeVec : {A : Set i} → {k : ℕ} → (xs ys : Vec A k) → CodeVec xs ys → xs ≡ ys
        decodeVec [] [] unit = refl
        decodeVec (x ∷ xs) (.x ∷ ys) (refl , code) = cong (x ∷_) (decodeVec xs ys code)

        decodeVec-encodeVec : {A : Set i} → {k : ℕ} → (xs ys : Vec A k) → (ps : xs ≡ ys)
            → decodeVec xs ys (encodeVec xs ys ps) ≡ ps
        decodeVec-encodeVec [] [] refl = refl
        decodeVec-encodeVec (x ∷ xs) (.x ∷ .xs) refl = cong (cong (x ∷_)) (decodeVec-encodeVec xs xs refl)

        encodeVec-decodeVec : {A : Set i} → {k : ℕ} → (xs ys : Vec A k) → (code : CodeVec xs ys)
            → encodeVec xs ys (decodeVec xs ys code) ≡ code
        encodeVec-decodeVec [] [] unit = refl
        encodeVec-decodeVec (x ∷ xs) (.x ∷ ys) (refl , code) with decodeVec xs ys code | encodeVec-decodeVec xs ys code
        ... | refl | refl = refl -- use with-abstraction to avoid long equality reasoning?!

        -- encodeVec-decodeVec : {A : Set i} → {k : ℕ} → (xs ys : Vec A k) → (code : CodeVec xs ys)
        --     → encodeVec xs ys (decodeVec xs ys code) ≡ code
        -- encodeVec-decodeVec [] [] unit = refl
        -- encodeVec-decodeVec (x ∷ xs) (.x ∷ ys) (refl , code) =
        --     begin
        --         encodeVec (x ∷ xs) (x ∷ ys) (decodeVec (x ∷ xs) (x ∷ ys) (refl , code))
        --     ≡⟨⟩
        --         encodeVec (x ∷ xs) (x ∷ ys) (cong (x ∷_) (decodeVec xs ys code))
        --     ≡⟨⟩
        --         subst (CodeVec (x ∷ xs)) (cong (x ∷_) (decodeVec xs ys code)) (rVec (x ∷ xs))
        --     ≡⟨ subst-cong (CodeVec (x ∷ xs)) (decodeVec xs ys code) ⟩
        --         subst (λ ys → CodeVec (x ∷ xs) (x ∷ ys)) (decodeVec xs ys code) (rVec (x ∷ xs))
        --     ≡⟨⟩
        --         subst (λ ys → x ≡ x × CodeVec xs ys) (decodeVec xs ys code) (refl , (rVec xs))
        --     ≡⟨ subst≡subst×subst (λ ys → x ≡ x) (CodeVec xs) (decodeVec xs ys code) ⟩
        --         subst (λ _ → x ≡ x) (decodeVec xs ys code) refl , subst (CodeVec xs) (decodeVec xs ys code) (rVec xs)
        --     ≡⟨⟩
        --         subst (λ _ → x ≡ x) (decodeVec xs ys code) refl , encodeVec xs ys (decodeVec xs ys code)
        --     ≡⟨ cong₂ _,_ (subst-const (x ≡ x) (decodeVec xs ys code)) (encodeVec-decodeVec xs ys code) ⟩
        --         refl , code
        --     ∎

CodeVec-Is-hProp : {A : Set i} → {k : ℕ} → Is-hSet A → (xs ys : Vec A k) → Is-hProp (CodeVec xs ys)
CodeVec-Is-hProp is-hSet [] [] = Unit-Is-hProp
CodeVec-Is-hProp is-hSet (x ∷ xs) (y ∷ ys) = ×-Is-hProp (is-hSet x y) (CodeVec-Is-hProp is-hSet xs ys)

Vec-Is-hSet : {A : Set i} → {k : ℕ} → Is-hSet A → Is-hSet (Vec A k)
Vec-Is-hSet is-hSet xs ys = ≅-Is-hProp (Vec-eq≅CodeVec xs ys) (CodeVec-Is-hProp is-hSet xs ys)

Vec≅ListWithLength : {A : Set i} → {k : ℕ}
    → Vec A k ≅ Σ (List A) (λ xs → length xs ≡ k)
Vec≅ListWithLength = record {
        to = to;
        from = from;
        from∘to = from∘to;
        to∘from = to∘from
    } where
        to : {A : Set i} → {k : ℕ} → Vec A k → Σ (List A) (λ xs → length xs ≡ k)
        to [] = [] , refl
        to (x ∷ xs) with to xs
        ... | xs , refl = (x ∷ xs) , refl
        -- to (x ∷ xs) = x ∷ to xs .proj₁ , cong suc (to xs .proj₂)

        from : {A : Set i} → {k : ℕ} → Σ (List A) (λ xs → length xs ≡ k) → Vec A k
        from ([] , refl) = []
        from (x ∷ xs , refl) = x ∷ from (xs , refl)
        -- from {A = A} (x ∷ xs , p) = subst (Vec A) p (x ∷ (from (xs , refl)))

        from∘to : {A : Set i} → {k : ℕ} → (xs : Vec A k) → from (to xs) ≡ xs
        from∘to [] = refl
        from∘to (x ∷ xs) with to xs | from∘to xs
        ... | xs , refl | refl = refl

        to∘from : {A : Set i} → {k : ℕ} → (w : Σ (List A) (λ xs → length xs ≡ k)) → to (from w) ≡ w
        to∘from ([] , refl) = refl
        to∘from (x ∷ xs , refl) with to (from (xs , refl)) | to∘from (xs , refl)
        ... | .(xs , refl) | refl = refl
        -- to∘from (x ∷ xs , refl) = cong (λ w → x ∷ w .proj₁ , cong suc (w .proj₂)) (to∘from (xs , refl))

-- Another formulation of Vec:

-- data Fin : ℕ → Set where
--     zero : {k : ℕ} → Fin (suc k)
--     suc : {k : ℕ} → Fin n → Fin (suc k)

-- Vector : Set i → ℕ → Set i
-- Vector A k = Fin k → A

CodeFin : {k : ℕ} → Fin k → Fin k → Set
CodeFin zero zero = ⊤
CodeFin zero (suc m) = ⊥
CodeFin (suc n) zero = ⊥
CodeFin (suc n) (suc m) = CodeFin n m

rFin : {k : ℕ} → (n : Fin k) → CodeFin n n
rFin zero = tt
rFin (suc n) = rFin n

Fin-eq≅CodeFin : {k : ℕ} → (n m : Fin k) → n ≡ m ≅ CodeFin n m
Fin-eq≅CodeFin n m = record {
        to = encodeFin n m;
        from = decodeFin n m;
        from∘to = decodeFin-encodeFin n m;
        to∘from = encodeFin-decodeFin n m
    } where
        encodeFin : {k : ℕ} → (n m : Fin k) → n ≡ m → CodeFin n m
        encodeFin n .n refl = rFin n

        decodeFin : {k : ℕ} → (n m : Fin k) → CodeFin n m → n ≡ m
        decodeFin zero zero tt = refl
        decodeFin (suc n) (suc m) code = cong suc (decodeFin n m code)

        decodeFin-encodeFin : {k : ℕ} → (n m : Fin k) → (p : n ≡ m) → decodeFin n m (encodeFin n m p) ≡ p
        decodeFin-encodeFin zero .zero refl = refl
        decodeFin-encodeFin (suc n) .(suc n) refl = cong (cong suc) (decodeFin-encodeFin n n refl)
        
        encodeFin-decodeFin : {k : ℕ} → (n m : Fin k) → (code : CodeFin n m) → encodeFin n m (decodeFin n m code) ≡ code
        encodeFin-decodeFin zero zero tt = refl
        encodeFin-decodeFin (suc n) (suc m) code with decodeFin n m code | encodeFin-decodeFin n m code
        ... | refl | refl = refl

CodeFin-Is-hProp : {k : ℕ} → (n m : Fin k) → Is-hProp (CodeFin n m)
CodeFin-Is-hProp zero zero = ⊤-Is-hProp
CodeFin-Is-hProp (suc n) (suc m) = CodeFin-Is-hProp n m

Fin-Is-hSet : {k : ℕ} → Is-hSet (Fin k)
Fin-Is-hSet n m = ≅-Is-hProp (Fin-eq≅CodeFin n m) (CodeFin-Is-hProp n m)

Vector≅Vec : {A : Set i} → {k : ℕ} → Vector A k ≅ Vec A k
Vector≅Vec = record {
        to = to;
        from = from;
        from∘to = from∘to;
        to∘from = to∘from
    } where
        to : {A : Set i} → {k : ℕ} → Vector A k → Vec A k
        to {k = zero} f = []
        to {k = suc k} f = f zero ∷ (to (f ∘ suc))

        from : {A : Set i} → {k : ℕ} → Vec A k → Vector A k
        from [] ()
        from (x ∷ xs) zero = x
        from (x ∷ xs) (suc n) = from xs n

        from∘to : {A : Set i} → {k : ℕ} → (f : Vector A k) → from (to f) ≡ f
        from∘to {k = zero} f = extensionality λ { () }
        from∘to {k = suc k} f = extensionality λ { zero → refl; (suc n) → cong-app (from∘to (f ∘ suc)) n }

        to∘from : {A : Set i} → {k : ℕ} → (xs : Vec A k) → to (from xs) ≡ xs
        to∘from [] = refl
        to∘from (x ∷ xs) = cong (x ∷_) (to∘from xs)

-- Vector-Is-hSet : {A : Set i} → {k : ℕ} → Is-hSet A → Is-hSet (Vector A k)
-- Vector-Is-hSet is-hSet = →-Is-hSet is-hSet -- TODO

Vector-Is-hSet′ : {A : Set i} → {k : ℕ} → Is-hSet A → Is-hSet (Vector A k)
Vector-Is-hSet′ is-hSet = ≅-Is-hSet Vector≅Vec (Vec-Is-hSet is-hSet)

CodeAll : {A : Set i} → {P : A → Set j}
    → {xs : List A} → All P xs → All P xs → Set (i ⊔ j)
CodeAll [] [] = Unit
CodeAll (p ∷ ps) (q ∷ qs) = p ≡ q × CodeAll ps qs

rAll : {A : Set i} → {P : A → Set j} → {xs : List A} → (ps : All P xs) → CodeAll ps ps
rAll [] = unit
rAll (p ∷ ps) = refl , (rAll ps)

All-eq≅CodeAll : {A : Set i} → {P : A → Set j}
    → {xs : List A} → (ps qs : All P xs)
    → ps ≡ qs ≅ CodeAll ps qs
All-eq≅CodeAll ps qs = record {
        to = encodeAll ps qs;
        from = decodeAll ps qs;
        from∘to = decodeAll-encodeAll ps qs;
        to∘from = encodeAll-decodeAll ps qs
    } where
        encodeAll : {A : Set i} → {P : A → Set j}
            → {xs : List A} → (ps qs : All P xs)
            → ps ≡ qs → CodeAll ps qs
        encodeAll ps .ps refl = rAll ps
        -- encodeAll ps qs e = subst (CodeAll ps) e (rAll ps)

        decodeAll : {A : Set i} → {P : A → Set j}
            → {xs : List A} → (ps qs : All P xs)
            → CodeAll ps qs → ps ≡ qs
        decodeAll [] [] unit = refl
        decodeAll (p ∷ ps) (.p ∷ qs) (refl , code) = cong (p ∷_) (decodeAll ps qs code)

        decodeAll-encodeAll : {A : Set i} → {P : A → Set j}
            → {xs : List A} → (ps qs : All P xs)
            → (e : ps ≡ qs) → decodeAll ps qs (encodeAll ps qs e) ≡ e
        decodeAll-encodeAll [] .[] refl = refl
        decodeAll-encodeAll (p ∷ ps) .(p ∷ ps) refl = cong (cong (p ∷_)) (decodeAll-encodeAll ps ps refl)

        encodeAll-decodeAll : {A : Set i} → {P : A → Set j}
            → {xs : List A} → (ps qs : All P xs)
            → (code : CodeAll ps qs) → encodeAll ps qs (decodeAll ps qs code) ≡ code
        encodeAll-decodeAll [] [] unit = refl
        encodeAll-decodeAll (p ∷ ps) (.p ∷ qs) (refl , code) with decodeAll ps qs code | encodeAll-decodeAll ps qs code
        ... | refl | refl = refl

CodeAll-Is-hProp : {A : Set i} → {P : A → Set j}
    → ({x : A} → Is-hSet (P x)) → {xs : List A}
    → (ps qs : All P xs) → Is-hProp (CodeAll ps qs)
CodeAll-Is-hProp are-hSets [] [] = Unit-Is-hProp
CodeAll-Is-hProp are-hSets (p ∷ ps) (q ∷ qs) = ×-Is-hProp (are-hSets p q) (CodeAll-Is-hProp are-hSets ps qs)

All-Is-hSet : {A : Set i} → {P : A → Set j}
    → ({x : A} → Is-hSet (P x)) → {xs : List A}
    → Is-hSet (All P xs)
All-Is-hSet are-hSets ps qs = ≅-Is-hProp (All-eq≅CodeAll ps qs) (CodeAll-Is-hProp are-hSets ps qs)

CodeAny : {A : Set i} → {P : A → Set j}
    → {xs : List A} → Any P xs → Any P xs → Set j
CodeAny (here p) (here q) = p ≡ q
CodeAny (here p) (there qs) = Empty
CodeAny (there ps) (here q) = Empty
CodeAny (there ps) (there qs) = CodeAny ps qs

rAny : {A : Set i} → {P : A → Set j} → {xs : List A} → (ps : Any P xs) → CodeAny ps ps
rAny (here p) = refl
rAny (there ps) = rAny ps

Any-eq≅CodeAny : {A : Set i} → {P : A → Set j}
    → {xs : List A} → (ps qs : Any P xs)
    → ps ≡ qs ≅ CodeAny ps qs
Any-eq≅CodeAny ps qs = record {
        to = encodeAny ps qs;
        from = decodeAny ps qs;
        from∘to = decodeAny-encodeAny ps qs;
        to∘from = encodeAny-decodeAny ps qs
    } where
        encodeAny : {A : Set i} → {P : A → Set j}
            → {xs : List A} → (ps qs : Any P xs)
            → ps ≡ qs → CodeAny ps qs
        encodeAny ps .ps refl = rAny ps

        decodeAny : {A : Set i} → {P : A → Set j}
            → {xs : List A} → (ps qs : Any P xs)
            → CodeAny ps qs → ps ≡ qs
        decodeAny (here p) (here .p) refl = refl
        decodeAny (there ps) (there qs) code = cong there (decodeAny ps qs code)

        decodeAny-encodeAny : {A : Set i} → {P : A → Set j}
            → {xs : List A} → (ps qs : Any P xs)
            → (e : ps ≡ qs) → decodeAny ps qs (encodeAny ps qs e) ≡ e
        decodeAny-encodeAny (here p) .(here p) refl = refl
        decodeAny-encodeAny (there ps) .(there ps) refl = cong (cong there) (decodeAny-encodeAny ps ps refl)

        encodeAny-decodeAny : {A : Set i} → {P : A → Set j}
            → {xs : List A} → (ps qs : Any P xs)
            → (code : CodeAny ps qs) → encodeAny ps qs (decodeAny ps qs code) ≡ code
        encodeAny-decodeAny (here p) (here .p) refl = refl
        encodeAny-decodeAny (there ps) (there qs) code with decodeAny ps qs code | encodeAny-decodeAny ps qs code
        ... | refl | refl = refl

CodeAny-Is-hProp : {A : Set i} → {P : A → Set j}
    → ({x : A} → Is-hSet (P x)) → {xs : List A}
    → (ps qs : Any P xs) → Is-hProp (CodeAny ps qs)
CodeAny-Is-hProp are-hSets (here p) (here q) = are-hSets p q
CodeAny-Is-hProp are-hSets (there ps) (there qs) = CodeAny-Is-hProp are-hSets ps qs

Any-Is-hSet : {A : Set i} → {P : A → Set j}
    → ({x : A} → Is-hSet (P x)) → {xs : List A}
    → Is-hSet (Any P xs)
Any-Is-hSet are-hSets ps qs = ≅-Is-hProp (Any-eq≅CodeAny ps qs) (CodeAny-Is-hProp are-hSets ps qs)

Membership-Is-hSet : {A : Set i}
    → Is-hGroupoid A → {x : A} → {xs : List A}
    → Is-hSet (x ∈ xs)
Membership-Is-hSet is-hGroupoid {x} = Any-Is-hSet λ {y} → is-hGroupoid x y
