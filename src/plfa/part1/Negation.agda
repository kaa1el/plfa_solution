{-# OPTIONS --without-K #-}

module plfa.part1.Negation where

open import Agda.Primitive

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; _≢_)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _+_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Maybe
open import Function using (_∘_; id)

open import plfa.part1.Relations using (_<_; _>_)
open import plfa.part1.Isomorphism using (_≅_; extensionality; Π-extensionality)
open import plfa.part1.Connectives using (→-distrib-+)

private
    variable
        i j k l : Level

¬_ : Set i → Set i
¬ A = A → ⊥

¬-elim : {A : Set i} → ¬ A → A → ⊥
¬-elim ¬x = ¬x

infix 3 ¬_

¬¬-intro : {A : Set i} → A → ¬ ¬ A
¬¬-intro x ¬x = ¬x x

¬¬¬-elim : {A : Set i} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : {A : Set i} → {B : Set j} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

-- _≢_ : {A : Set i} → A → A → Set i
-- x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : {n : ℕ} → zero ≢ suc n
peano ()

false≢true : false ≢ true
false≢true ()

0≢1 : 0 ≢ 1
0≢1 ()

Bool≢ℕ : ℕ ≢ Bool
Bool≢ℕ p = ¬Bool-Has-Three (subst Has-Three p ℕ-Has-Three) where
    Has-Three : Set → Set
    Has-Three A = Σ A λ x → Σ A λ y → Σ A λ z → (x ≢ y × x ≢ z × y ≢ z)

    ℕ-Has-Three : Has-Three ℕ
    ℕ-Has-Three = 0 , 1 , 2 , (λ ()) , (λ ()) , (λ ())

    ¬Bool-Has-Three : ¬ Has-Three Bool
    ¬Bool-Has-Three (false , false , _ , f , _ , _) = f refl
    ¬Bool-Has-Three (false , true , false , _ , g , _) = g refl
    ¬Bool-Has-Three (false , true , true , _ , _ , h) = h refl
    ¬Bool-Has-Three (true , false , false , _ , _ , h) = h refl
    ¬Bool-Has-Three (true , false , true , _ , g , _) = g refl
    ¬Bool-Has-Three (true , true , _ , f , _ , _) = f refl

id′ : ⊥ → ⊥
id′ x = x

id″ : ⊥ → ⊥
id″ ()

id′≡id″ : id′ ≡ id″
id′≡id″ = extensionality λ ()

assimilation : {A : Set i} → (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
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

open _≅_

+-dual-× : {A : Set i} → {B : Set j} → ¬ (A + B) ≅ (¬ A) × (¬ B)
+-dual-× = →-distrib-+

¬+¬-implies-¬× : {A : Set i} → {B : Set j} → (¬ A) + (¬ B) → ¬ (A × B)
¬+¬-implies-¬× (inj₁ f) (x , y) = f x
¬+¬-implies-¬× (inj₂ g) (x , y) = g y

no-contradiction : {A : Set i} → ¬ (A × ¬ A)
no-contradiction f = f .proj₂ (f .proj₁)

postulate
    em : {A : Set i} → A + ¬ A

em-irrefutable : {A : Set i} → ¬ ¬ (A + ¬ A)
em-irrefutable f = f (inj₂ λ x → f (inj₁ x))

module Classical where

    ExcludedMiddle : Set (lsuc i)
    ExcludedMiddle {i} = (A : Set i) → A + ¬ A

    DoubleNegationElimination : Set (lsuc i)
    DoubleNegationElimination {i} = (A : Set i) → ¬ ¬ A → A

    PeirceLaw : Set (lsuc (i ⊔ j))
    PeirceLaw {i} {j} = (A : Set i) → (B : Set j) → ((A → B) → A) → A

    ImplicationAsDisjunction : Set (lsuc (i ⊔ j))
    ImplicationAsDisjunction {i} {j} = (A : Set i) → (B : Set j) → (A → B) → B + ¬ A

    DeMorgan : Set (lsuc (i ⊔ j))
    DeMorgan {i} {j} = (A : Set i) → (B : Set j) → ¬ (¬ A × ¬ B) → A + B

    em-implies-dne : ({i : Level} → ExcludedMiddle {i}) → ({i : Level} → DoubleNegationElimination {i})
    em-implies-dne em A f with em A
    ... | inj₁ x = x
    ... | inj₂ g = ⊥-elim (f g)

    dne-implies-em : ({i : Level} → DoubleNegationElimination {i}) → ({i : Level} → ExcludedMiddle {i})
    dne-implies-em dne A = dne (A + ¬ A) em-irrefutable

    em-implies-peirce : ({i : Level} → ExcludedMiddle {i}) → ({i j : Level} → PeirceLaw {i} {j})
    em-implies-peirce em A B f with em A
    ... | inj₁ x = x
    ... | inj₂ g = f (λ x → ⊥-elim (g x))

    peirce-implies-em : ({i j : Level} → PeirceLaw {i} {j}) → ({k : Level} → ExcludedMiddle {i})
    peirce-implies-em peirce A = peirce (A + ¬ A) A λ f → inj₁ (peirce A ⊥ λ g → f (inj₂ g))

    em-implies-iad : ({i : Level} → ExcludedMiddle {i}) → ({i j : Level} → ImplicationAsDisjunction {i} {j})
    em-implies-iad em A B f with em A
    ... | inj₁ x = inj₁ (f x)
    ... | inj₂ g = inj₂ g

    iad-implies-em : ({i j : Level} → ImplicationAsDisjunction {i} {j}) → ({i : Level} → ExcludedMiddle {i})
    iad-implies-em iad A = iad A A id

    em-implies-dm : ({i : Level} → ExcludedMiddle {i}) → ({i j : Level} → DeMorgan {i} {j})
    em-implies-dm em A B f with em A
    ... | inj₁ x = inj₁ x
    ... | inj₂ g with em B
    ... | inj₁ y = inj₂ y
    ... | inj₂ h = ⊥-elim (f (g , h))

    dm-implies-em : ({i j : Level} → DeMorgan {i} {j}) → ({i : Level} → ExcludedMiddle {i})
    dm-implies-em dm A = dm A (¬ A) λ w → proj₂ w (proj₁ w)

    dne-implies-peirce : ({i : Level} → DoubleNegationElimination {i}) → ({i j : Level} → PeirceLaw {i} {j})
    dne-implies-peirce dne A B f = dne A λ g → g (f λ x → dne B λ _ → g x)

    peirce-implies-dne : ({i j : Level} → PeirceLaw {i} {j}) → ({i : Level} → DoubleNegationElimination {i})
    peirce-implies-dne peirce A f = peirce A ⊥ λ g → ⊥-elim (f g)
    -- peirce-implies-dne peirce A f = peirce A (¬ A) (λ g → ⊥-elim (f λ x → g x x))

    dne-implies-iad : ({i : Level} → DoubleNegationElimination {i}) → ({i j : Level} → ImplicationAsDisjunction {i} {j})
    dne-implies-iad dne A B f = dne (B + ¬ A) λ g → g (inj₁ (f (dne A λ h → g (inj₂ h))))

    iad-implies-dne : ({i j : Level} → ImplicationAsDisjunction {i} {j}) → ({i : Level} → DoubleNegationElimination {i})
    iad-implies-dne iad A f with iad A A id
    ... | inj₁ x = x
    ... | inj₂ g = ⊥-elim (f g)

    dne-implies-dm : ({i : Level} → DoubleNegationElimination {i}) → ({i j : Level} → DeMorgan {i} {j})
    dne-implies-dm dne A B f = dne (A + B) λ g → f ((λ x → g (inj₁ x)) , λ y → g (inj₂ y))

    dm-implies-dne : ({i j : Level} → DeMorgan {i} {j}) → ({i : Level} → DoubleNegationElimination {i})
    dm-implies-dne dm A f with dm A ⊥ (λ w → f (proj₁ w))
    ... | inj₁ x = x

    peirce-implies-iad : ({i j : Level} → PeirceLaw {i} {j}) → ({i j : Level} → ImplicationAsDisjunction {i} {j})
    peirce-implies-iad peirce A B f = peirce (B + ¬ A) ⊥ λ g → inj₂ λ x → g (inj₁ (f x))

    iad-implies-peirce : ({i j : Level} → ImplicationAsDisjunction {i} {j}) → ({i j : Level} → PeirceLaw {i} {j})
    iad-implies-peirce iad A B f with iad A A id
    ... | inj₁ x = x
    ... | inj₂ g = f (λ x → ⊥-elim (g x))

    peirce-implies-dm : ({i j : Level} → PeirceLaw {i} {j}) → ({i j : Level} → DeMorgan {i} {j})
    peirce-implies-dm peirce A B f = peirce (A + B) ⊥ λ g → ⊥-elim (f ((λ x → g (inj₁ x)) , (λ y → g (inj₂ y))))

    dm-implies-peirce : ({i j : Level} → DeMorgan {i} {j}) → ({i j : Level} → PeirceLaw {i} {j})
    dm-implies-peirce dm A B f with dm A ⊥ (λ w → proj₁ w (f λ x → ⊥-elim (proj₁ w x)))
    ... | inj₁ x = x

    iad-implies-dm : ({i j : Level} → ImplicationAsDisjunction {i} {j}) → ({i j : Level} → DeMorgan {i} {j})
    iad-implies-dm iad A B f with iad A A id
    ... | inj₁ x = inj₁ x
    ... | inj₂ g with iad B B id
    ... | inj₁ y = inj₂ y
    ... | inj₂ h = ⊥-elim (f (g , h))

    dm-implies-iad : ({i j : Level} → DeMorgan {i} {j}) → ({i j : Level} → ImplicationAsDisjunction {i} {j})
    dm-implies-iad dm A B f = dm B (¬ A) λ w → proj₂ w λ x → proj₁ w (f x)

    NotImplicationAsConjunction : Set (lsuc (i ⊔ j))
    NotImplicationAsConjunction {i} {j} = (A : Set i) → (B : Set j) → ¬ (A → B) → A × ¬ B

    niac-implies-em : ({i j : Level} → NotImplicationAsConjunction {i} {j}) → ({i : Level} → ExcludedMiddle {i})
    niac-implies-em niac A = proj₁ (niac (A + ¬ A) ⊥ λ f → f (inj₂ λ x → f (inj₁ x)))

    em-implies-niac : ({i : Level} → ExcludedMiddle {i}) → ({i j : Level} → NotImplicationAsConjunction {i} {j})
    em-implies-niac em A B f with em A
    ... | inj₁ x = x , λ y → f (λ _ → y)
    ... | inj₂ g = ⊥-elim (f (⊥-elim ∘ g))

    NotPiAsSigma : Set (lsuc (i ⊔ j))
    NotPiAsSigma {i} {j} = (A : Set i) → (B : A → Set j) → ¬ ((x : A) → B x) → Σ A (¬_ ∘ B)

    npas-implies-em : ({i j : Level} → NotPiAsSigma {i} {j}) → ({i : Level} → ExcludedMiddle {i})
    npas-implies-em npas A = proj₁ (npas (A + ¬ A) (λ _ → ⊥) λ f → f (inj₂ λ x → f (inj₁ x)))

    em-implies-npas : ({i : Level} → ExcludedMiddle {i}) → ({i j : Level} → NotPiAsSigma {i} {j})
    em-implies-npas em A B f with em (Σ A (¬_ ∘ B))
    ... | inj₁ w = w
    ... | inj₂ g = ⊥-elim (f λ x → helper x (em (B x))) where
        helper : (x : A) → (B x) + ¬ (B x) → B x
        helper x (inj₁ y) = y
        helper x (inj₂ h) = ⊥-elim (g (x , h))

    Decidable : Set i → Set i
    Decidable A = A + ¬ A

    Stable : Set i → Set i
    Stable A = ¬ ¬ A → A

    stable-¬ : {A : Set i} → Stable (¬ A)
    stable-¬ = ¬¬¬-elim

    stable-× : {A : Set i} → {B : Set j} → Stable A → Stable B → Stable (A × B)
    stable-× s t f = (s (λ g → f (λ w → g (proj₁ w))) , t (λ h → f (λ w → h (proj₂ w))))

    decidable-implies-stable : {A : Set i} → Decidable A → Stable A
    decidable-implies-stable dec f with dec
    ... | inj₁ x = x
    ... | inj₂ g = ⊥-elim (f g)

×-implies-¬→¬ : {A : Set i} → {B : Set j} → A × B → ¬ (A → ¬ B)
×-implies-¬→¬ w f = f (proj₁ w) (proj₂ w)

test : {A : Set i} → (f g : ⊥ → A) → f ≡ g
test f g = extensionality λ ()

¬⊥≅⊤ : ¬ ⊥ ≅ ⊤
¬⊥≅⊤ .to _ = tt
¬⊥≅⊤ .from _ = λ ()
¬⊥≅⊤ .from∘to _ = extensionality λ ()
¬⊥≅⊤ .to∘from _ = refl

¬⊤≅⊥ : ¬ ⊤ ≅ ⊥
¬⊤≅⊥ .to f = f tt
¬⊤≅⊥ .from = ⊥-elim
¬⊤≅⊥ .from∘to f = extensionality λ _ → ⊥-elim (f tt)
¬⊤≅⊥ .to∘from ()

empty-domain : {A : Set i} → (⊥ → A) ≅ ⊤ -- ⊥ is the initial object
empty-domain .to _ = tt
empty-domain .from _ = λ ()
empty-domain .from∘to _ = extensionality λ ()
empty-domain .to∘from _ = refl

unit-codomain : {A : Set i} → (A → ⊤) ≅ ⊤ -- ⊤ is the terminal object
unit-codomain .to _ = tt
unit-codomain .from _ _ = tt
unit-codomain .from∘to _ = extensionality λ _ → refl
unit-codomain .to∘from _ = refl

empty-function : {A : ⊥ → Set i} → ((x : ⊥) → A x) ≅ ⊤
empty-function .to _ = tt
empty-function .from _ = λ ()
empty-function .from∘to _ = Π-extensionality λ ()
empty-function .to∘from _ = refl

empty-pair : {A : ⊥ → Set i} → Σ ⊥ A ≅ ⊥
empty-pair .to ()
empty-pair .from ()
empty-pair .from∘to ()
empty-pair .to∘from ()
