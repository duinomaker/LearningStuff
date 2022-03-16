open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; _>_; s≤s)
open import Data.Nat.Properties using (<-asym)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import isom using (_≃_; extensionality; _⇔_)

¬_ : Set → Set
¬ A = A → ⊥
infix 3 ¬_

→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim f x = f x

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim {A} = →-elim {A} {⊥}

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x = λ ¬x → ¬x x

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f = λ ¬y → (λ x → ¬y (f x))

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

peano : ∀ {n : ℕ} → zero ≢ suc n
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality λ ()

{-
⊥ implies anything, including equalities.
-}
assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive {zero} ()
<-irreflexive {suc n} (s≤s h) = <-irreflexive {n} h

trichotomy : ∀ {m n : ℕ} →
  (m ≡ n → ¬ m < n × ¬ m > n) ×
  (m < n → ¬ m ≡ n × ¬ m > n) ×
  (m > n → ¬ m ≡ n × ¬ m < n)
trichotomy {m} {n} =
  ⟨ (λ { refl → ⟨ <-irreflexive , <-irreflexive ⟩ })
  , ⟨ helper₁ m n , helper₂ m n ⟩ ⟩ where
  helper₁ : ∀ (m n : ℕ) → m < n → ¬ m ≡ n × ¬ m > n
  helper₁ m n m<n =
    ⟨ (λ { refl → <-irreflexive m<n })
    , (λ m>n → <-asym m<n m>n) ⟩
  helper₂ : ∀ (m n : ℕ) → m > n → ¬ m ≡ n × ¬ m < n
  helper₂ m n m>n =
    ⟨ (λ { refl → <-irreflexive m>n })
    , (λ m<n → <-asym m<n m>n) ⟩

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = record
  { t   = λ { ¬A⊎B → ⟨ ¬A⊎B ∘ inj₁ , ¬A⊎B ∘ inj₂ ⟩ }
  ; f   = λ { ⟨ ¬x , ¬y ⟩ → case-⊎ ¬x ¬y }
  ; f∘t = λ { ¬A⊎B → extensionality λ A⊎B → ⊥-elim (¬A⊎B A⊎B) }
  ; t∘f = λ _ → refl
  }

-- (¬ A) ⊎ (¬ B) → ¬ (A × B)
-- won't know which of A and B is an empty type from ¬ (A × B)
try-×-dual-⊎ : ∀ {A B : Set} → (¬ (A × B)) ⇔ ((¬ A) ⊎ (¬ B))
try-×-dual-⊎ = record
  { t = λ ¬A×B → inj₁ {!!}
  ; f = λ { (inj₁ ¬x) ⟨ x , y ⟩ → ¬x x ; (inj₂ ¬y) ⟨ x , y ⟩ → ¬y y}
  }

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ nem → nem (inj₂ (λ x → nem (inj₁ x)))

em      = ∀ {A   : Set} → A ⊎ ¬ A
¬¬-elim = ∀ {A   : Set} → ¬ ¬ A → A
peirce  = ∀ {A B : Set} → ((A → B) → A) → A
iad     = ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
dm      = ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B

em→¬¬-elim : em → ¬¬-elim
em→¬¬-elim A⊎¬A ¬¬x with A⊎¬A
...                     | (inj₁  x) = x
...                     | (inj₂ ¬x) = ⊥-elim (¬¬x ¬x)

{-
This one is mostly completed just by pressing C-c C-a.
-}
¬¬-elim→peirce : ¬¬-elim → peirce
¬¬-elim→peirce ¬¬x→x f = ¬¬x→x (λ ¬x → ¬x (f (λ x → ⊥-elim (¬x x))))

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable ¬¬¬x = ¬¬¬-elim ¬¬¬x

×-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-stable SA SB ¬¬xy =
  ⟨ SA (λ ¬x → ¬¬xy λ { ⟨ x , y ⟩ → ¬x x })
  , SB (λ ¬y → ¬¬xy λ { ⟨ x , y ⟩ → ¬y y }) ⟩
