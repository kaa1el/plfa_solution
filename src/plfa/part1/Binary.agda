module plfa.part1.Binary where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; +-identityʳ)

data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

bsuc : Bin → Bin
bsuc ⟨⟩ = ⟨⟩ I
bsuc (b O) = b I
bsuc (b I) = (bsuc b) O

_ : bsuc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = bsuc (to n)

_ : to 0 ≡ ⟨⟩ O
_ = refl

_ : to 1 ≡ ⟨⟩ I
_ = refl

_ : to 2 ≡ ⟨⟩ I O
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = from b + from b
from (b I) = suc (from b + from b)

_ : from (⟨⟩ O) ≡ 0
_ = refl

_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl

from-bsuc : (b : Bin) → from (bsuc b) ≡ suc (from b)
from-bsuc ⟨⟩ = refl
from-bsuc (b O) = refl
from-bsuc (b I) rewrite from-bsuc b | +-suc (from b) (from b) = refl

from-to : (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n) rewrite from-bsuc (to n) | from-to n = refl

badd : Bin → Bin → Bin
badd ⟨⟩ y = y
badd (x O) ⟨⟩ = x O
badd (x O) (y O) = (badd x y) O
badd (x O) (y I) = (badd x y) I
badd (x I) ⟨⟩ = x I
badd (x I) (y O) = (badd x y) I
badd (x I) (y I) = (bsuc (badd x y)) O -- carry

_ : badd (⟨⟩ I O I I) (⟨⟩ I O I I) ≡ ⟨⟩ I O I I O
_ = refl

bzero : Bin
bzero = ⟨⟩ O

bone : Bin
bone = ⟨⟩ I

badd-bsuc-l : (x y : Bin) → badd (bsuc x) y ≡ bsuc (badd x y)
badd-bsuc-l ⟨⟩ ⟨⟩ = refl
badd-bsuc-l ⟨⟩ (y O) = refl
badd-bsuc-l ⟨⟩ (y I) = refl
badd-bsuc-l (x O) ⟨⟩ = refl
badd-bsuc-l (x O) (y O) = refl
badd-bsuc-l (x O) (y I) = refl
badd-bsuc-l (x I) ⟨⟩ = refl
badd-bsuc-l (x I) (y O) rewrite badd-bsuc-l x y = refl
badd-bsuc-l (x I) (y I) rewrite badd-bsuc-l x y = refl

badd-comm : (x y : Bin) → badd x y ≡ badd y x
badd-comm ⟨⟩ ⟨⟩ = refl
badd-comm ⟨⟩ (y O) = refl
badd-comm ⟨⟩ (y I) = refl
badd-comm (x O) ⟨⟩ = refl
badd-comm (x O) (y O) rewrite badd-comm x y = refl
badd-comm (x O) (y I) rewrite badd-comm x y = refl
badd-comm (x I) ⟨⟩ = refl
badd-comm (x I) (y O) rewrite badd-comm x y = refl
badd-comm (x I) (y I) rewrite badd-comm x y = refl

badd-bsuc-r : (x y : Bin) → badd x (bsuc y) ≡ bsuc (badd x y)
badd-bsuc-r x y
    rewrite badd-comm x y
    | badd-comm x (bsuc y)
    | badd-bsuc-l y x = refl

badd-bzero-bsuc : (x : Bin) → badd bzero (bsuc x) ≡ bsuc x
badd-bzero-bsuc ⟨⟩ = refl
badd-bzero-bsuc (x O) = refl
badd-bzero-bsuc (x I) = refl

to-hom-+' : (n m : ℕ) → to (n + m) ≡ badd (to n) (to m)
to-hom-+' zero zero = refl
to-hom-+' zero (suc m) = sym (badd-bzero-bsuc (to m))
to-hom-+' (suc n) zero
    rewrite badd-comm (bsuc (to n)) bzero
    | badd-bzero-bsuc (to n)
    | +-identityʳ n = refl
to-hom-+' (suc n) (suc m)
    rewrite badd-bsuc-l (to n) (bsuc (to m))
    | badd-bsuc-r (to n) (to m)
    | +-suc n m
    | to-hom-+' n m = refl

helper : (a b c d : ℕ) → ((a + b) + (c + d)) ≡ ((a + c) + (b + d))
helper a b c d
    rewrite +-assoc a b (c + d)
    | sym (+-assoc b c d)
    | +-comm b c
    | +-assoc c b d
    | sym (+-assoc a c (b + d)) = refl

from-hom : (x y : Bin) → from (badd x y) ≡ from x + from y
from-hom ⟨⟩ y = refl
from-hom (x O) ⟨⟩ rewrite +-identityʳ (from x + from x) = refl
from-hom (x O) (y O)
    rewrite from-hom x y
    | helper (from x) (from y) (from x) (from y) = refl
from-hom (x O) (y I)
    rewrite from-hom x y
    | +-suc (from x + from x) (from y + from y)
    | helper (from x) (from y) (from x) (from y) = refl
from-hom (x I) ⟨⟩ rewrite +-identityʳ (from x + from x) = refl
from-hom (x I) (y O)
    rewrite from-hom x y
    | helper (from x) (from y) (from x) (from y) = refl
from-hom (x I) (y I)
    rewrite from-bsuc (badd x y)
    | from-hom x y
    | +-suc (from x + from y) (from x + from y)
    | +-suc (from x + from x) (from y + from y)
    | helper (from x) (from y) (from x) (from y) = refl

data One : Bin → Set where
    justI : One (⟨⟩ I)
    caseO : {b : Bin} → One b → One (b O)
    caseI : {b : Bin} → One b → One (b I)

data Can : Bin → Set where
    justO : Can (⟨⟩ O)
    fromOne : {b : Bin} → One b → Can b

one-bsuc : {b : Bin} → One b → One (bsuc b)
one-bsuc justI = caseO justI
one-bsuc (caseO p) = caseI p
one-bsuc (caseI p) = caseO (one-bsuc p)

can-bsuc : {b : Bin} → Can b → Can (bsuc b)
can-bsuc justO = fromOne justI
can-bsuc (fromOne p) = fromOne (one-bsuc p)

one-to : (n : ℕ) → One (to (suc n))
one-to zero = justI
one-to (suc n) = one-bsuc (one-to n)

can-to : (n : ℕ) → Can (to n)
can-to zero = justO
can-to (suc n) = fromOne (one-to n)

badd-bzero : (b : Bin) → Can b → badd bzero b ≡ b
badd-bzero _ justO = refl
badd-bzero (b O) (fromOne p) = refl
badd-bzero (b I) (fromOne p) = refl

to-hom-+ : (n m : ℕ) → to (n + m) ≡ badd (to n) (to m)
to-hom-+ zero m rewrite badd-bzero (to m) (can-to m) = refl
to-hom-+ (suc n) m
    rewrite badd-bsuc-l (to n) (to m)
    | to-hom-+ n m = refl

badd-double : (b : Bin) → One b → badd b b ≡ b O
badd-double _ justI = refl
badd-double (b O) (caseO p) rewrite badd-double b p = refl
badd-double (b I) (caseI p) rewrite badd-double b p = refl

one-to-from : (b : Bin) → One b → to (from b) ≡ b
one-to-from _ justI = refl
one-to-from (b O) (caseO p)
    rewrite to-hom-+ (from b) (from b)
    | one-to-from b p
    | badd-double b p = refl
one-to-from (b I) (caseI p)
    rewrite to-hom-+ (from b) (from b)
    | one-to-from b p
    | badd-double b p = refl

can-to-from : (b : Bin) → Can b → to (from b) ≡ b
can-to-from _ justO = refl
can-to-from b (fromOne p) = one-to-from b p
