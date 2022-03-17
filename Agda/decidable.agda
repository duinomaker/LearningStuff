import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
-- open import Data.Nat.Properties using (suc-injective)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Function using (_∘_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import isom using (_⇔_)

{-
contradiction : ∀ {P : Set} → P → ¬ P → Whatever
is the same as, because
¬¬-intro      : ∀ {P : Set} → P → ¬ ¬ P
...           : ∀ {P : Set} → P → ¬ P → ⊥
and ⊥ implies Whatever
-}

data Bool : Set where
  true : Bool
  false : Bool

_≤ᵇ_ : ∀ (m n : ℕ) → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

T : Bool → Set
T true = ⊤
T false = ⊥

T→≡ : ∀ {b : Bool} → T b → b ≡ true
T→≡ {true} tt = refl
T→≡ {false} ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ {zero} {n} tt = z≤n
≤ᵇ→≤ {suc m} {zero} ()
≤ᵇ→≤ {suc m} {suc n} b = s≤s (≤ᵇ→≤ {m} {n} b)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s H) = ≤→≤ᵇ H

{-
`Reflects`, `Dec` and `pattern ...` in the following context are based on
the latest standard library (v2.0 development version)
-}
data Reflects (P : Set) : Bool → Set where
  ofʸ :   P → Reflects P true
  ofⁿ : ¬ P → Reflects P false

record Dec (P : Set) : Set where
  constructor _because_
  field
    does  : Bool
    proof : Reflects P does

pattern yes p =  true because ofʸ  p
pattern no ¬p = false because ofⁿ ¬p

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no (λ ())
suc m ≤? suc n with m ≤? n
...               | yes m≤n = yes (s≤s m≤n)
...               | no ¬m≤n = no (λ { (s≤s m≤n) → ¬m≤n m≤n })

⇔ᵇ-dec : ∀ {P : Set} (b : Bool) → (P ⇔ (b ≡ true)) → Dec P
⇔ᵇ-dec true ft = yes (_⇔_.f ft refl)
⇔ᵇ-dec false ft = no ((λ ()) ∘ (_⇔_.t ft))

{-
Another formulation that makes use of previously proved lemmas
-}
_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n = ⇔ᵇ-dec (m ≤ᵇ n) record
    { t = T→≡ ∘ ≤→≤ᵇ
    ; f = ≤ᵇ→≤ ∘ ≡→T
    }

{-
Yet another version

By using `with` clause, Agda would know whether m ≤ᵇ n is
true or false, which in turn turns T (m ≤ᵇ n) into ⊤ or ⊥
-}
_≤″_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤″ n with m ≤ᵇ n | ≤ᵇ→≤ {m} {n} | ≤→≤ᵇ {m} {n}
...       | true   | p             | _             = yes (p tt)
...       | false  | _             | ¬p            = no ¬p

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
m <? zero = no (λ ())
zero <? suc n = yes (s≤s z≤n)
suc m <? suc n with m <? n
...               | yes m<n = yes (s≤s m<n)
...               | no ¬m<n = no (λ { (s≤s m<n) → ¬m<n m<n })

_≡ℕ_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ zero = yes refl
zero ≡ℕ suc n = no (λ ())
suc m ≡ℕ zero = no (λ ())
suc m ≡ℕ suc n with m ≡ℕ n
...               | yes refl = yes refl
...               | no ¬m≡n = no (λ { refl → ¬m≡n refl})

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no ¬x ⌋ = false

_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n = ⌊ m ≤? n ⌋

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt = x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _ = tt
fromWitness {A} {no ¬x} x = ¬x x

≤ᵇ′→≤′ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤′ {m} {n} Tb = toWitness {m ≤ n} {m ≤? n} Tb

≤′→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤′→≤ᵇ′ {m} {n} m≤n = fromWitness {m ≤ n} {m ≤? n} m≤n 

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
true  ∧ false = false
false ∧ _     = false

_∨_ : Bool → Bool → Bool
true  ∨ _     = true
false ∨ true  = true
false ∨ false = false

infixr 6 _∧_
infixr 5 _∨_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
yes x ×-dec no ¬y = no (λ { ⟨ _ , y ⟩ → ¬y y })
no ¬x ×-dec _     = no (λ { ⟨ x , _ ⟩ → ¬x x })

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
no ¬x ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no (case-⊎ ¬x ¬y)

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no ¬x) = yes ¬x

_⊃_ : Bool → Bool → Bool
true  ⊃ false = false
false ⊃ false = true
_     ⊃ true  = true

_→-dec_ : {A B : Set} → Dec A → Dec B → Dec (A → B)
(yes x) →-dec (no ¬y) = no (λ ¬imp → ¬y (¬imp x))
(no ¬x) →-dec (no ¬y) = yes (λ x → ⊥-elim (¬x x))
_       →-dec (yes y) = yes (λ _ → y)

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) →
  ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes x) (yes y) = refl
∧-× (yes x) (no ¬y) = refl
∧-× (no x)  _       = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) →
  ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes x) _       = refl
∨-⊎ (no ¬x) (yes y) = refl
∨-⊎ (no ¬x) (no ¬y) = refl

not-¬ : ∀ {A : Set} (x : Dec A) →
  not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes x) = refl
not-¬ (no ¬x) = refl

_iff_ : Bool → Bool → Bool
true  iff true  = true
true  iff false = false
false iff true  = false
false iff false = true

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes x ⇔-dec yes y = yes (record
  { t = λ _ → y
  ; f = λ _ → x })
yes x ⇔-dec no ¬y = no (λ tf → ¬y (_⇔_.t tf x))
no ¬x ⇔-dec yes y = no (λ tf → ¬x (_⇔_.f tf y))
no ¬x ⇔-dec no ¬y = yes (record
  { t = λ x → ⊥-elim (¬x x)
  ; f = λ y → ⊥-elim (¬y y) })

iff-⇔ : ∀ {A B : Set} → (x : Dec A) → (y : Dec B) →
  ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes x) (yes y) = refl
iff-⇔ (yes x) (no ¬y) = refl
iff-⇔ (no ¬x) (yes y) = refl
iff-⇔ (no ¬x) (no ¬y) = refl

minus : (m n : ℕ) → n ≤ m → ℕ
minus m zero z≤n = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m

_-_ : (m n : ℕ) {_ : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)
