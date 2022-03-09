open import Data.Nat using (ℕ; _+_; _≤_; z≤n; s≤s; zero; suc)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

{-
a variety where _≡_ is indexed by two arguments
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
-}
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl e = e

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ {x : A} → f x ≡ g x
cong-app refl = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst _ refl h = h

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin h = h

  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  _ ≡⟨⟩ h = h

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ hxy ⟩ hyz = trans hxy hyz

  _∎ : ∀ (x : A) → x ≡ x
  _ ∎ = refl

open ≡-Reasoning public

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-identity n)
+-comm (suc m) n = begin
  suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
  suc (n + m) ≡⟨ sym (+-suc n m) ⟩
  n + suc m   ∎

module ≤-Reasoning-stupid where

  {-
  I realized its stupidity after postulating _≤⟨_,_,_,_,_,_,_⟩_
  which has the theorem ≤-mono embedded into it, which is redundant.
  
  Theorems should be provided inside the brackets, not within the
  reasoning tool itself.
  -}

  infix  1 begin-le_
  infixr 2 _≤⟨⟩_ _≤⟨_,_,_,_,_,_,_⟩_
  infix  3 _∎-le

  postulate
    ≤-mono : ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

  begin-le_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  begin-le h = h

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  _ ≤⟨⟩ h = h

  postulate
    _≤⟨_,_,_,_,_,_,_⟩_ : ∀ (x : ℕ) (m p n q : ℕ) (_ : x ≡ m + p) →
      m ≤ n → p ≤ q → {y : ℕ} → (_+_ n q) ≤ y → (_+_ m p) ≤ y

  _∎-le : ∀ (n : ℕ) → n ≤ n
  _ ∎-le = ≤-refl

  postulate
    test1 : 1 ≤ 2
    test2 : 3 ≤ 4

  test : 1 + 3 ≤ 2 + 4
  test = begin-le
    1 + 3 ≤⟨ 1 , 3 , 2 , 4 , refl , test1 , test2 ⟩
    2 + 4 ∎-le

module ≤-Reasoning where

  infix  1 begin-le_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≡′⟨_⟩_
  infix  3 _∎-le

  begin-le_ : ∀ {m n : ℕ} → m ≤ n → m ≤ n
  begin-le h = h

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  _ ≤⟨⟩ h = h

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  _ ≤⟨ hxy ⟩ hyz = ≤-trans hxy hyz

  _≡′⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≡ y → y ≤ z → x ≤ z
  _ ≡′⟨ refl ⟩ hyz = hyz

  _∎-le : ∀ (n : ℕ) → n ≤ n
  _ ∎-le = ≤-refl

  +-monoʳ-≤ : ∀ (m n p : ℕ) → m ≤ n → p + m ≤ p + n
  +-monoʳ-≤ m n zero h = h
  +-monoʳ-≤ m n (suc p) h = begin-le
    suc (p + m) ≤⟨ s≤s (+-monoʳ-≤ m n p h)  ⟩
    suc (p + n) ∎-le

  +-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
  +-monoˡ-≤ m n p h = begin-le
    m + p ≡′⟨ +-comm m p ⟩
    p + m ≤⟨ +-monoʳ-≤ m n p h ⟩
    p + n ≡′⟨ +-comm p n ⟩
    n + p ∎-le

module RewriteExpanded where

  postulate
    P : ℕ → Set

  stmt : Set
  stmt = ∀ (m n : ℕ) → P (m + n) → P (n + m)

  try-with : stmt
  try-with m n p with   m + n  | +-comm m n
  ...               | .(n + m) | refl = p

  try-subst : stmt
  try-subst m n = subst P (+-comm m n)

module Leibniz where

  _≐_ : ∀ {A : Set} (x y : A) → Set₁
  _≐_ {A} x y = ∀ (P : A → Set) → P x → P y

  ≐-refl : ∀ {A : Set} {x : A} → x ≐ x
  ≐-refl P Px = Px

  ≐-trans : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
  ≐-trans hxy hyz P Px = hyz P (hxy P Px)

  ≐-sym : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
  ≐-sym {A} {x} {y} hxy P = hxy (λ s → P s → P x) (hxy (λ _ → P x))

  ≡→≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
  ≡→≐ hxy P = subst P hxy

  ≐→≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
  ≐→≡ {A} {x} {y} leb = leb (λ s → x ≡ s) refl

module Universe where

  data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
    refl′ : x ≡′ x

  sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡′ y → y ≡′ x
  sym′ refl′ = refl′

  _≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
  _≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

  _∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} →
    (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)
