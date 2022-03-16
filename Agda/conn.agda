import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_; id)
open import isom using (_≃_; _≲_; extensionality)
open isom.≃-Reasoning

data _×′_ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩′ : (x : A) → B x → A ×′ B
infixr 2 _×′_

proj′₁ : {A : Set} {B : A → Set} → A ×′ B → A
proj′₁ ⟨ x , y ⟩′ = x

proj′₂ : {A : Set} {B : A → Set} → (w : A ×′ B) → B (proj′₁ w)
proj′₂ ⟨ x , y ⟩′ = y

η-×′ : ∀ {A : Set} {B : A → Set} (w : A ×′ B) →
  ⟨ proj′₁ w , proj′₂ w ⟩′ ≡ w
η-×′ ⟨ x , y ⟩′ = refl

{-
This one defines non-dependent pair, where the equality between
⟨ proj₁ w , proj₂ w ⟩ and w holds by definition.
-}
record _×_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B
open _×_
infixr 2 _×_

×-comm : {A B : Set} → A × B ≃ B × A
×-comm = record
  { t   = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ }
  ; f   = λ { ⟨ y , x ⟩ → ⟨ x , y ⟩ }
  ; f∘t = λ { ⟨ x , y ⟩ → refl }
  ; t∘f = λ { ⟨ y , x ⟩ → refl }
  }

×-assoc : {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = record
  { t   = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
  ; f   = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
  ; f∘t = λ { _ → refl }
  ; t∘f = λ { _ → refl }
  }

record _⇔_ (A B : Set) : Set where
  field
    t : A → B
    f : B → A
open _⇔_

⇔≃× : {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record
  { t   = λ { A⇔B → ⟨ t A⇔B , f A⇔B ⟩ }
  ; f   = λ { ⟨ A→B , B→A ⟩ → record { t = A→B ; f = B→A } }
  ; f∘t = λ { _ → refl }
  ; t∘f = λ { _ → refl }
  }

data ⊤ : Set where
  tt : ⊤

record ⊤′ : Set where
  constructor tt′

data ⊥ : Set where

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

{-
Records stay unchanged after any (the only) re-construction.
-}
η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ = record
  { t   = λ { ⟨ tt , x ⟩ → x }
  ; f   = λ { x → ⟨ tt , x ⟩ }
  ; f∘t = λ { ⟨ tt , x ⟩ → refl }
  ; t∘f = λ { x → refl }
  }

⊤-identityʳ : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identityʳ {A} = ≃-begin
  (A × ⊤) ≃⟨ ×-comm ⟩
  (⊤ × A) ≃⟨ ⊤-identityˡ ⟩
  A       ≃-∎

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

{-
postulate
  the-axiom : ⊥

forty-two : ℕ
forty-two = ⊥-count the-axiom
-}

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
infixr 1 _⊎_

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B C : Set} → (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} → (h : A ⊎ B → C) →
  (w : A ⊎ B) → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

∀-uniq-⊎ : ∀ {A B C : Set} → (h : A ⊎ B → C) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) ≡ h
∀-uniq-⊎ h = extensionality (uniq-⊎ h)

∀-η-⊎ : ∀ {A B : Set} → case-⊎ {A} {B} {A ⊎ B} inj₁ inj₂ ≡ id
∀-η-⊎ = ∀-uniq-⊎ id

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { t   = λ { (inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y }
  ; f   = λ { (inj₁ y) → inj₂ y ; (inj₂ x) → inj₁ x }
  ; f∘t = λ { (inj₁ x) → refl   ; (inj₂ y) → refl   }
  ; t∘f = λ { (inj₁ y) → refl   ; (inj₂ x) → refl   }
  }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record
  { t   = λ
    { (inj₁ (inj₁ a)) → inj₁ a
    ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b)
    ; (inj₂ c)        → inj₂ (inj₂ c)
    }
  ; f   = λ
    { (inj₁ a)        → inj₁ (inj₁ a)
    ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b)
    ; (inj₂ (inj₂ c)) → inj₂ c
    }
  ; f∘t = λ
    { (inj₁ (inj₁ a)) → refl
    ; (inj₁ (inj₂ b)) → refl
    ; (inj₂ c)        → refl
    }
  ; t∘f = λ
    { (inj₁ a)        → refl
    ; (inj₂ (inj₁ b)) → refl
    ; (inj₂ (inj₂ c)) → refl
    }
  }

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ = record
  { t   = λ { (inj₂ x) → x }
  ; f   = λ { x → inj₂ x }
  ; f∘t = λ { (inj₂ x) → refl }
  ; t∘f = λ { x → refl }
  }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} = ≃-begin
  (A ⊎ ⊥) ≃⟨ ⊎-comm ⟩
  (⊥ ⊎ A) ≃⟨ ⊥-identityˡ ⟩
  A       ≃-∎

→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L H = L H

{-
My incorrect initial formulation.
η-→ : ∀ {A B : Set} → (x : A) (y : B) → →-elim (λ _ → y) x ≡ y
η-→ x y = refl
-}

{-
Seems in Agda the equality between (λ x → f x) and f holds by definition.
-}
η-→ : ∀ {A B : Set} (f : A → B) → (λ x → f x) ≡ f
η-→ f = refl

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...           | aa     | aa      = 1
...           | aa     | bb      = 2
...           | aa     | cc      = 3
...           | bb     | aa      = 4
...           | bb     | bb      = 5
...           | bb     | cc      = 6
...           | cc     | aa      = 7
...           | cc     | bb      = 8
...           | cc     | cc      = 9

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying = record
  { t   = λ { f ⟨ x , y ⟩ → f x y }
  ; f   = λ { g x y → g ⟨ x , y ⟩ }
  ; f∘t = λ { f → refl }
  ; t∘f = λ { g → refl }
  }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ (A → C) × (B → C)
→-distrib-⊎ = record
  { t   = λ { h → ⟨ h ∘ inj₁ , h ∘ inj₂ ⟩ }
  ; f   = λ { ⟨ f , g ⟩ → case-⊎ f g }
  ; f∘t = ∀-uniq-⊎
  ; t∘f = λ { w → refl }
  }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = record
  { t   = λ { h → ⟨ (λ x → proj₁ (h x)) , (λ x → proj₂ (h x)) ⟩ }
  ; f   = λ { ⟨ f , g ⟩ x → ⟨ f x , g x ⟩ } 
  ; f∘t = λ { h → refl }
  ; t∘f = λ { w → refl }
  }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ A × C ⊎ B × C
×-distrib-⊎ = record
  { t   = λ
    { ⟨ w , z ⟩ → case-⊎ (λ x → inj₁ ⟨ x , z ⟩)
                          (λ y → inj₂ ⟨ y , z ⟩)
                          w
    }
  ; f   = case-⊎ (λ { ⟨ x , z ⟩ → ⟨ inj₁ x , z ⟩ })
                 (λ { ⟨ y , z ⟩ → ⟨ inj₂ y , z ⟩ })
  ; f∘t = λ
    { ⟨ inj₁ x , z ⟩ → refl
    ; ⟨ inj₂ y , z ⟩ → refl
    }
  ; t∘f = λ
    { (inj₁ xz) → refl
    ; (inj₂ yz) → refl
    }
  }

{-
But (A ∧ B) ∨ C ⇔ (A ∨ B) ∧ (A ∨ C) in logic.
-}
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× = record
   { t   = λ
     { (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
     ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
     }
   ; f   = λ
     { ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
     ; ⟨ _      , inj₂ z ⟩ → inj₂ z
     ; ⟨ inj₂ z , _      ⟩ → inj₂ z
     }
   ; f∘t = λ
     { (inj₁ ⟨ x , y ⟩) → refl
     ; (inj₂ z)         → refl
     }
   }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× {A} {B} {C} w = helper (_≃_.t ×-distrib-⊎ w) where
  helper : (A × C) ⊎ (B × C) → A ⊎ (B × C)
  helper (inj₁ ⟨ x , _ ⟩) = inj₁ x
  helper (inj₂ ⟨ y , z ⟩) = inj₂ ⟨ y , z ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ z , w ⟩) = ⟨ inj₂ z , inj₂ w ⟩
