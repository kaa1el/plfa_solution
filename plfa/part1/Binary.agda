module Binary where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

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
badd (x I) (y I) = (badd (bsuc x) y) O -- carry

_ : badd (⟨⟩ I O I I) (⟨⟩ I O I I) ≡ ⟨⟩ I O I I O
_ = refl

bzero : Bin
bzero = ⟨⟩ O

bone : Bin
bone = ⟨⟩ I

badd-bone : (x : Bin) → badd bone x ≡ bsuc x
badd-bone ⟨⟩ = refl
badd-bone (x O) = refl
badd-bone (x I) rewrite badd-bone x = refl

badd-bsuc : (x y : Bin) → badd (bsuc x) y ≡ bsuc (badd x y)
badd-bsuc ⟨⟩ ⟨⟩ = refl
badd-bsuc ⟨⟩ (y O) = refl
badd-bsuc ⟨⟩ (y I) rewrite badd-bone y = refl
badd-bsuc (x O) ⟨⟩ = refl
badd-bsuc (x O) (y O) = refl
badd-bsuc (x O) (y I) rewrite badd-bsuc x y = refl
badd-bsuc (x I) ⟨⟩ = refl
badd-bsuc (x I) (y O) rewrite badd-bsuc x y = refl
badd-bsuc (x I) (y I) = refl

badd-comm : (x y : Bin) → badd x y ≡ badd y x
badd-comm ⟨⟩ ⟨⟩ = refl
badd-comm ⟨⟩ (y O) = refl
badd-comm ⟨⟩ (y I) = refl
badd-comm (x O) ⟨⟩ = refl
badd-comm (x O) (y O) rewrite badd-comm x y = refl
badd-comm (x O) (y I) rewrite badd-comm x y = refl
badd-comm (x I) ⟨⟩ = refl
badd-comm (x I) (y O) rewrite badd-comm x y = refl
badd-comm (x I) (y I) rewrite badd-bsuc x y | badd-bsuc y x | badd-comm x y = refl

badd-bsuc-r : (x y : Bin) → badd x (bsuc y) ≡ bsuc (badd x y)
badd-bsuc-r x y rewrite badd-comm x y | badd-comm x (bsuc y) = badd-bsuc y x

badd-bzero-bsuc : (x : Bin) → badd bzero (bsuc x) ≡ bsuc x
badd-bzero-bsuc ⟨⟩ = refl
badd-bzero-bsuc (x O) = refl
badd-bzero-bsuc (x I) = refl

badd-to : (n m : ℕ) → badd (to n) (to m) ≡ to (n + m)
badd-to zero zero = refl
badd-to zero (suc m) = badd-bzero-bsuc (to m)
badd-to (suc n) zero
    rewrite badd-comm (bsuc (to n)) bzero
    | +-identityʳ n
    | badd-bzero-bsuc (to n) = refl
badd-to (suc n) (suc m)
    rewrite badd-bsuc (to n) (bsuc (to m))
    | badd-bsuc-r (to n) (to m)
    | badd-to n m
    | +-suc n m = refl

helper : (a b c d : ℕ) → ((a + b) + (c + d)) ≡ ((a + c) + (b + d))
helper a b c d
    rewrite +-assoc a b (c + d)
    | sym (+-assoc b c d)
    | +-comm b c
    | +-assoc c b d
    | sym (+-assoc a c (b + d)) = refl

from-badd : (x y : Bin) → from (badd x y) ≡ from x + from y
from-badd ⟨⟩ y = refl
from-badd (x O) ⟨⟩ rewrite +-identityʳ (from x + from x) = refl
from-badd (x O) (y O)
    rewrite from-badd x y
    | helper (from x) (from y) (from x) (from y) = refl
from-badd (x O) (y I)
    rewrite from-badd x y
    | +-suc (from x + from x) (from y + from y)
    | helper (from x) (from y) (from x) (from y) = refl
from-badd (x I) ⟨⟩ rewrite +-identityʳ (from x + from x) = refl
from-badd (x I) (y O)
    rewrite from-badd x y
    | helper (from x) (from y) (from x) (from y) = refl
from-badd (x I) (y I)
    rewrite badd-bsuc x y
    | from-bsuc (badd x y)
    | from-badd x y
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

can-to-from : (b : Bin) → Can (to (from b))
can-to-from ⟨⟩ = justO
can-to-from (b O) = can-to (from b + from b)
can-to-from (b I) = can-bsuc (can-to (from b + from b))

badd-double : (b : Bin) → One b → badd b b ≡ b O
badd-double (⟨⟩ I) justI = refl
badd-double (b O) (caseO p) rewrite badd-double b p = refl
badd-double (b I) (caseI p) rewrite badd-bsuc b b | badd-double b p = refl

to-from-one : (b : Bin) → One b → to (from b) ≡ b
to-from-one (⟨⟩ I) justI = refl
to-from-one (b O) (caseO p)
    rewrite sym (badd-to (from b) (from b))
    | to-from-one b p
    | badd-double b p = refl
to-from-one (b I) (caseI p)
    rewrite sym (badd-to (from b) (from b))
    | to-from-one b p
    | badd-double b p = refl

to-from-can : (b : Bin) → Can b → to (from b) ≡ b
to-from-can (⟨⟩ O) justO = refl
to-from-can b (fromOne p) = to-from-one b p
