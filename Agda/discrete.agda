import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Product using (_×_; _,_)

data sigma : Set
data A : Set
data B : Set

data sigma where
  a : A → sigma
  b : B → sigma

data A where
  a₁ : A
  a₂ : sigma → A
  a₃ : A → A → A

data B where
  b₁ : B
  b₂ : sigma → B
  b₃ : B → B → B

0-suc : ℕ × ℕ → ℕ × ℕ
0-suc (m , n) = (suc m , n)

1-suc : ℕ × ℕ → ℕ × ℕ
1-suc (m , n) = (m , suc n)

_p+_ : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
(m₁ , m₂) p+ (n₁ , n₂) = (m₁ + n₁ , m₂ + n₂)

cnt-sigma : sigma → ℕ × ℕ
cnt-a : A → ℕ × ℕ
cnt-b : B → ℕ × ℕ

cnt-sigma (a x) = 1-suc (cnt-a x)
cnt-sigma (b x) = 0-suc (cnt-b x)
cnt-a a₁ = (1 , 0)
cnt-a (a₂ x) = 0-suc (cnt-sigma x)
cnt-a (a₃ x y) = 1-suc (cnt-a x) p+ (cnt-a y)
cnt-b b₁ = (0 , 1)
cnt-b (b₂ x) = 1-suc (cnt-sigma x)
cnt-b (b₃ x y) = 0-suc (cnt-b x) p+ (cnt-b y)

fst : {A : Set} → A × A → A
fst (m , _) = m

snd : {A : Set} → A × A → A
snd (_ , n) = n

eq : {A : Set} → A × A → Set
eq x = fst x ≡ snd x

lemma₁ : ∀ {x : ℕ × ℕ} → eq x → eq (0-suc (1-suc x))
lemma₁ = {!!}

lemma₂ : ∀ {x : ℕ × ℕ} → eq x → eq (1-suc (0-suc x))
lemma₂ = {!!}

lemma₃ : ∀ {x y : ℕ × ℕ} → eq x → eq y → eq (x p+ y)
lemma₃ = {!!}

lemma₄ : ∀ {x y : ℕ × ℕ} → 1-suc (x p+ y) ≡ x p+ (1-suc y)
lemma₄ = {!!}

lemmaA : ∀ {x : A} → eq (1-suc (cnt-a x))
lemmaA = {!!}

lemmaB : ∀ {x : B} → eq (0-suc (cnt-b x))
lemmaB = {!!}

thetheorem : ∀ (s : sigma) → eq (cnt-sigma s)
thetheorem (a a₁) = refl
thetheorem (a (a₂ x)) = lemma₂ (thetheorem x)
thetheorem (a (a₃ x y)) = {!!}
thetheorem (b b₁) = {!!}
thetheorem (b (b₂ x)) = {!!}
thetheorem (b (b₃ x y)) = {!!}
