module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _+_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Maybe

open import plfa.part1.Relations using (_<_; _>_)
open import plfa.part1.Isomorphism using (_≃_; extensionality; id)
open import plfa.part1.Connectives using (→-distrib-+)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : {A : Set} → ¬ A → A → ⊥
¬-elim ¬x = ¬x

infix 3 ¬_

¬¬-intro : {A : Set} → A → ¬ ¬ A
¬¬-intro x ¬x = ¬x x

¬¬¬-elim : {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : {n : ℕ} → zero ≢ suc n
peano ()

id′ : ⊥ → ⊥
id′ x = x

id″ : ⊥ → ⊥
id″ ()

id′≡id″ : id′ ≡ id″
id′≡id″ = extensionality λ ()

assimilation : {A : Set} → (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ x → ⊥-elim (¬x x)

open _<_

<-irreflexive : {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s p) = <-irreflexive p

data Trichotomy (m n : ℕ) : Set where
    <-case : (m < n) → ¬ (m ≡ n) → ¬ (m > n) → Trichotomy m n
    ≡-case : (m ≡ n) → ¬ (m < n) → ¬ (m > n) → Trichotomy m n
    >-case : (m > n) → ¬ (m < n) → ¬ (m ≡ n) → Trichotomy m n

<-trichotomy : (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = ≡-case refl (λ ()) (λ ())
<-trichotomy zero (suc n) = <-case z<s (λ ()) (λ ())
<-trichotomy (suc m) zero = >-case z<s (λ ()) (λ ())
<-trichotomy (suc m) (suc n) with <-trichotomy m n
... | <-case m<n m≢n m≯n = <-case (s<s m<n) (λ { refl → m≢n refl }) (λ { (s<s e) → m≯n e })
... | ≡-case m≡n m≮n m≯n rewrite m≡n = ≡-case refl (λ { (s<s e) → m≮n e }) (λ { (s<s e) → m≯n e })
... | >-case m>n m≮n m≢n = >-case (s<s m>n) (λ { (s<s e) → m≮n e }) (λ { refl → m≢n refl })

open _≃_

+-dual-× : {A B : Set} → ¬ (A + B) ≃ (¬ A) × (¬ B)
+-dual-× = →-distrib-+

¬+¬-implies-¬× : {A B : Set} → (¬ A) + (¬ B) → ¬ (A × B)
¬+¬-implies-¬× (inj₁ f) (x , y) = f x
¬+¬-implies-¬× (inj₂ g) (x , y) = g y

postulate
    em : {A : Set} → A + ¬ A

em-irrefutable : {A : Set} → ¬ ¬ (A + ¬ A)
em-irrefutable f = f (inj₂ λ x → f (inj₁ x))

module Classical where

    ExcludedMiddle : Set₁
    ExcludedMiddle = (A : Set) → A + ¬ A

    DoubleNegationElimination : Set₁
    DoubleNegationElimination = (A : Set) → ¬ ¬ A → A

    PeirceLaw : Set₁
    PeirceLaw = (A B : Set) → ((A → B) → A) → A

    ImplicationAsDisjunction : Set₁
    ImplicationAsDisjunction = (A B : Set) → (A → B) → B + ¬ A

    DeMorgan : Set₁
    DeMorgan = (A B : Set) → ¬ (¬ A × ¬ B) → A + B

    em-implies-dne : ExcludedMiddle → DoubleNegationElimination
    em-implies-dne em A f with em A
    ... | inj₁ x = x
    ... | inj₂ g = ⊥-elim (f g)

    dne-implies-em : DoubleNegationElimination → ExcludedMiddle
    dne-implies-em dne A = dne (A + ¬ A) em-irrefutable

    em-implies-peirce : ExcludedMiddle → PeirceLaw
    em-implies-peirce em A B f with em A
    ... | inj₁ x = x
    ... | inj₂ g = f (λ x → ⊥-elim (g x))

    peirce-implies-em : PeirceLaw → ExcludedMiddle
    peirce-implies-em peirce A = peirce (A + ¬ A) A λ f → inj₁ (peirce A ⊥ λ g → f (inj₂ g))

    em-implies-iad : ExcludedMiddle → ImplicationAsDisjunction
    em-implies-iad em A B f with em A
    ... | inj₁ x = inj₁ (f x)
    ... | inj₂ g = inj₂ g

    iad-implies-em : ImplicationAsDisjunction → ExcludedMiddle
    iad-implies-em iad A = iad A A id

    em-implies-dm : ExcludedMiddle → DeMorgan
    em-implies-dm em A B f with em A
    ... | inj₁ x = inj₁ x
    ... | inj₂ g with em B
    ... | inj₁ y = inj₂ y
    ... | inj₂ h = ⊥-elim (f (g , h))

    dm-implies-em : DeMorgan → ExcludedMiddle
    dm-implies-em dm A = dm A (¬ A) λ w → proj₂ w (proj₁ w)

    dne-implies-peirce : DoubleNegationElimination → PeirceLaw
    dne-implies-peirce dne A B f = dne A λ g → g (f λ x → dne B λ _ → g x)

    peirce-implies-dne : PeirceLaw → DoubleNegationElimination
    peirce-implies-dne peirce A f = peirce A ⊥ λ g → ⊥-elim (f g)
    -- peirce-implies-dne peirce A f = peirce A (¬ A) (λ g → ⊥-elim (f λ x → g x x))

    dne-implies-iad : DoubleNegationElimination → ImplicationAsDisjunction
    dne-implies-iad dne A B f = dne (B + ¬ A) λ g → g (inj₁ (f (dne A λ h → g (inj₂ h))))

    iad-implies-dne : ImplicationAsDisjunction → DoubleNegationElimination
    iad-implies-dne iad A f with iad A A id
    ... | inj₁ x = x
    ... | inj₂ g = ⊥-elim (f g)

    dne-implies-dm : DoubleNegationElimination → DeMorgan
    dne-implies-dm dne A B f = dne (A + B) λ g → f ((λ x → g (inj₁ x)) , λ y → g (inj₂ y))

    dm-implies-dne : DeMorgan → DoubleNegationElimination
    dm-implies-dne dm A f with dm A ⊥ λ w → f (proj₁ w)
    ... | inj₁ x = x

    peirce-implies-iad : PeirceLaw → ImplicationAsDisjunction
    peirce-implies-iad peirce A B f = peirce (B + ¬ A) ⊥ λ g → inj₂ λ x → g (inj₁ (f x))

    iad-implies-peirce : ImplicationAsDisjunction → PeirceLaw
    iad-implies-peirce iad A B f with iad A A id
    ... | inj₁ x = x
    ... | inj₂ g = f (λ x → ⊥-elim (g x))

    peirce-implies-dm : PeirceLaw → DeMorgan
    peirce-implies-dm peirce A B f = peirce (A + B) ⊥ λ g → ⊥-elim (f ((λ x → g (inj₁ x)) , (λ y → g (inj₂ y))))

    dm-implies-peirce : DeMorgan → PeirceLaw
    dm-implies-peirce dm A B f with dm A ⊥ λ w → proj₁ w (f λ x → ⊥-elim (proj₁ w x))
    ... | inj₁ x = x

    iad-implies-dm : ImplicationAsDisjunction → DeMorgan
    iad-implies-dm iad A B f with iad A A id
    ... | inj₁ x = inj₁ x
    ... | inj₂ g with iad B B id
    ... | inj₁ y = inj₂ y
    ... | inj₂ h = ⊥-elim (f (g , h))

    dm-implies-iad : DeMorgan → ImplicationAsDisjunction
    dm-implies-iad dm A B f = dm B (¬ A) λ w → proj₂ w λ x → proj₁ w (f x)

    Decidable : Set → Set
    Decidable A = A + ¬ A

    Stable : Set → Set
    Stable A = ¬ ¬ A → A

    stable-¬ : {A : Set} → Stable (¬ A)
    stable-¬ = ¬¬¬-elim

    stable-× : {A B : Set} → Stable A → Stable B → Stable (A × B)
    stable-× s t f = (s (λ g → f (λ w → g (proj₁ w))) , t (λ h → f (λ w → h (proj₂ w))))

    decidable-implies-stable : {A : Set} → Decidable A → Stable A
    decidable-implies-stable dec f with dec
    ... | inj₁ x = x
    ... | inj₂ g = ⊥-elim (f g)

×-implies-¬→¬ : {A B : Set} → A × B → ¬ (A → ¬ B)
×-implies-¬→¬ w f = f (proj₁ w) (proj₂ w)
