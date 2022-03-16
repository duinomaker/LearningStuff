import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎) renaming (step-≡ to _≡⟨_⟩_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-comm; +-suc; +-identityʳ)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import isom using (_≃_; extensionality; _⇔_)

∀-elim : ∀ {A : Set} {B : A → Set} → (∀ (x : A) → B x) → (x : A) → B x
∀-elim f x = f x

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record
  { t   = λ { f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
  ; f   = λ { ⟨ f , g ⟩ → (λ x → ⟨ f x , g x ⟩) }
  ; f∘t = λ { f → refl }
  ; t∘f = λ { ⟨ f , g ⟩ → refl }
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → (∀ (x : A) → B x ⊎ C x)
⊎∀-implies-∀⊎ = case-⊎ (λ f → inj₁ ∘ f) (λ g → inj₂ ∘ g)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} →
    {f g : (x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

∀-×-Tri : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-×-Tri = record
  { t   = λ { f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩ }
  ; f   = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → λ { aa → x ; bb → y ; cc → z }}
  ; f∘t = λ f → ∀-extensionality (λ
      { aa → refl
      ; bb → refl
      ; cc → refl
      })
  ; t∘f = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
  }

{-
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
-}
record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B proj₁

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- L for Lemma, wit for witness and H for Hypothesis
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set} →
  (∀ (x : A) → B x → C) → ∃[ x ] B x → C
∃-elim L ⟨ wit , H ⟩ = L wit H

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set} →
  (∀ (x : A) → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying = record
  { t   = ∃-elim
  ; f   = λ L wit H → L ⟨ wit , H ⟩
  ; f∘t = λ L → refl
  ; t∘f = λ f → extensionality (λ { ⟨ wit , H ⟩ → refl })
  }

∃-distrib-⊎ : {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record
  { t   = λ
      { ⟨ w , inj₁ H ⟩ → inj₁ ⟨ w , H ⟩
      ; ⟨ w , inj₂ H ⟩ → inj₂ ⟨ w , H ⟩
      }
  ; f   = case-⊎ (λ { ⟨ w , H ⟩ → ⟨ w , inj₁ H ⟩ })
                 (λ { ⟨ w , H ⟩ → ⟨ w , inj₂ H ⟩ })
  ; f∘t = λ { ⟨ w , inj₁ H ⟩ → refl ; ⟨ w , inj₂ H ⟩ → refl }
  ; t∘f = λ { (inj₁ y) → refl ; (inj₂ z) → refl }
  }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ = λ { ⟨ w , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ w , y ⟩ , ⟨ w , z ⟩ ⟩ }

{-
Seems Agda cannot automatically enumerate through all constructors of a
datatype or through all possible constructors of a sum type, so I have to
do all the enumeration manually in f∘t and t∘f.
-}
∃-⊎-Tri : ∀ {B : Tri → Set} {x : Tri} →
  ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎-Tri = record
  { t   = λ
      { ⟨ aa , H ⟩ → inj₁ H
      ; ⟨ bb , H ⟩ → inj₂ (inj₁ H)
      ; ⟨ cc , H ⟩ → inj₂ (inj₂ H)
      }
  ; f   = λ
      { (inj₁ H)        → ⟨ aa , H ⟩
      ; (inj₂ (inj₁ H)) → ⟨ bb , H ⟩
      ; (inj₂ (inj₂ H)) → ⟨ cc , H ⟩
      }
  ; f∘t = λ
      { ⟨ aa , H ⟩ → refl
      ; ⟨ bb , H ⟩ → refl
      ; ⟨ cc , H ⟩ → refl
      }
  ; t∘f = λ
      { (inj₁ H)        → refl
      ; (inj₂ (inj₁ H)) → refl
      ; (inj₂ (inj₂ H)) → refl
      }
  }

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ k ] (    2 * k ≡ n)
odd-∃  : ∀ {n : ℕ} → odd  n → ∃[ k ] (1 + 2 * k ≡ n)

even-∃ zero = ⟨ zero , refl ⟩
even-∃ (suc od) with odd-∃ od
...                | ⟨ n , refl ⟩ = ⟨ suc n , +-suc (suc n) (n + 0) ⟩
odd-∃  (suc ev) with even-∃ ev
...                | ⟨ n , refl ⟩ = ⟨ n , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ k ] (    2 * k ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ k ] (1 + 2 * k ≡ n) → odd  n

∃-even ⟨ zero  , refl ⟩ = zero
∃-even ⟨ suc k , refl ⟩ = suc (∃-odd  ⟨ k , sym (+-suc k (k + zero)) ⟩)
∃-odd  ⟨ k     , refl ⟩ = suc (∃-even ⟨ k , refl ⟩)

∃-|-≤ : ∀ {y z : ℕ} → ((∃[ x ] (x + y ≡ z)) ⇔ (y ≤ z))
∃-|-≤ = record
  { t = λ { ⟨ x , refl ⟩ → lemma₁ }
  ; f = lemma₂
  } where
  lemma₁ : ∀ {x y : ℕ} → y ≤ x + y
  lemma₁ {x} {zero} = z≤n
  lemma₁ {x} {suc y} rewrite +-suc x y = s≤s (lemma₁ {x} {y})
  lemma₂ : ∀ {x y : ℕ} → x ≤ y → ∃[ z ] (z + x ≡ y)
  lemma₂ {x} {y} z≤n = ⟨ y , +-identityʳ y ⟩
  lemma₂ {suc x} {suc y} (s≤s h) with lemma₂ {x} {y} h
  ...                               | ⟨ z , refl ⟩ = ⟨ z , +-suc z x ⟩

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set} →
  ¬ (∃[ x ] B x) ≃ (∀ (x : A) → ¬ B x)
¬∃≃∀¬ = record
  { t   = λ ¬∃ → λ { x H → ¬∃ ⟨ x , H ⟩ }
  ; f   = λ ∀¬ → λ { ⟨ x , H ⟩ → ∀¬ x H }
  ; f∘t = λ ¬∃ → refl
  ; t∘f = λ ∀¬ → refl
  }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set} →
  ∃[ x ] (¬ B x) → ¬ (∀ (x : A) → B x)
∃¬-implies-¬∀ ⟨ w , H ⟩ ¬∀ = H (¬∀ w)
