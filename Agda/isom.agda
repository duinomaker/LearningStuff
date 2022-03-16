import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; sym)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Function using (_∘_)

-- extensionality

postulate
  extensionality : ∀ {A B : Set} → {f g : A → B} →
    (∀ (x : A) → f x ≡ g x) → f ≡ g

-- _+′_

_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ (suc n) = suc (m +′ n)

-- same-app

same-app : ∀ (m n : ℕ) → m + n ≡ m +′ n
same-app m zero rewrite +-comm m zero = refl
same-app m (suc n) rewrite +-comm m (suc n) = begin
  suc (n +  m) ≡⟨ cong suc (+-comm n m) ⟩
  suc (m +  n) ≡⟨ cong suc (same-app m n) ⟩
  suc (m +′ n) ∎

-- same

same : _+_ ≡ _+′_
same = extensionality (λ x → extensionality (λ y → same-app x y))

-- ∀-extensionality

postulate
  ∀-extensionality : {A : Set} {B : A → Set} {f g : (x : A) → B x} →
    (∀ (x : A) → f x ≡ g x) → f ≡ g

-- _≃_

record _≃_ (A B : Set) : Set where
  field
    t : A → B
    f : B → A
    f∘t : ∀ (x : A) → f (t x) ≡ x
    t∘f : ∀ (y : B) → t (f y) ≡ y
infix 0 _≃_
open _≃_

-- ≃-refl

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl = record
  { t   = λ x → x
  ; f   = λ x → x
  ; f∘t = λ x → refl
  ; t∘f = λ x → refl
  }

-- ≃-sym

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B = record
  { t   = f   A≃B
  ; f   = t   A≃B
  ; f∘t = t∘f A≃B
  ; t∘f = f∘t A≃B
  }

-- ≃-trans

≃-trans : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C = record
  { t   = t B≃C ∘ t A≃B
  ; f   = f A≃B ∘ f B≃C
  ; f∘t = λ x → begin
        f A≃B (f B≃C (t B≃C (t A≃B x)))
      ≡⟨ cong (f A≃B) (f∘t B≃C (t A≃B x)) ⟩
        f A≃B (t A≃B x)
      ≡⟨ f∘t A≃B x ⟩
        x
      ∎
  ; t∘f = λ y → begin
        t B≃C (t A≃B (f A≃B (f B≃C y)))
      ≡⟨ cong (t B≃C) (t∘f A≃B (f B≃C y)) ⟩
        t B≃C (f B≃C y)
      ≡⟨ t∘f B≃C y ⟩
        y
      ∎
  }

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} → A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

record _≲_ (A B : Set) : Set where
  field
    t : A → B
    f : B → A
    f∘t : ∀ (x : A) → f (t x) ≡ x
open _≲_
infix 0 _≲_

-- ≲-antisym

≲-antisym : ∀ {A B : Set} → (A≲B : A ≲ B) → (B≲A : B ≲ A) →
  (t A≲B) ≡ (f B≲A) → (f A≲B) ≡ (t B≲A) → A ≃ B
≲-antisym A≲B B≲A eAB eBA = record
  { t   = t A≲B
  ; f   = f A≲B
  ; f∘t = f∘t A≲B
  ; t∘f = λ y → begin
        t A≲B (f A≲B y)
      ≡⟨ cong (t A≲B) (cong-app eBA y) ⟩
        t A≲B (t B≲A y)
      ≡⟨ cong-app eAB (t B≲A y) ⟩
        f B≲A (t B≲A y)
      ≡⟨ f∘t B≲A y ⟩
        y
      ∎
  }

record _⇔_ (A B : Set) : Set where
  field
    t : A → B
    f : B → A
open _⇔_

⇔-refl : {A : Set} → A ⇔ A
⇔-refl = record { t = λ x → x ; f = λ x → x }

⇔-sym : {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym A⇔B = record { t = f A⇔B ; f = t A⇔B }

⇔-trans : {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans A⇔B B⇔C = record
  { t = t B⇔C ∘ t A⇔B
  ; f = f A⇔B ∘ f B⇔C
  }
