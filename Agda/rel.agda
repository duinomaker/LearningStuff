{-# OPTIONS --guardedness #-}

open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
open import Data.Nat using (ℕ; _+_; _*_; zero; suc)
open import Data.Nat.Properties using (+-comm; *-comm)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
infix 4 _≤_

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

inv-≤ : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-≤ (s≤s h) = h

inv-z≤n : ∀ {n : ℕ} → n ≤ zero → n ≡ zero
inv-z≤n z≤n = refl

≤-trans : ∀ {m n o : ℕ} → m ≤ n → n ≤ o → m ≤ o
≤-trans {zero} _ _ = z≤n
≤-trans (s≤s hmn) (s≤s hno) = s≤s (≤-trans hmn hno)

≤-asym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-asym z≤n z≤n = refl
≤-asym (s≤s hmn) (s≤s hnm) = cong suc (≤-asym hmn hnm)

data Total {A : Set} (r : A → A → Set) (m n : A) : Set where
  fw : r m n → Total r m n
  bk : r n m → Total r m n

≤-total : ∀ {m n : ℕ} → Total _≤_ m n
≤-total {m = zero} = fw z≤n
≤-total {n = zero} = bk z≤n
≤-total {suc m} {suc n} with ≤-total {m} {n}
... | fw h = fw (s≤s h)
... | bk h = bk (s≤s h)
{-
which is equivalent to
≤-total {suc m} {suc n} = helper (≤-total {m} {n}) where
  helper : Total _≤_ m n → Total _≤_ (suc m) (suc n)
  helper (fw h) = fw (s≤s h)
  helper (bk h) = bk (s≤s h)
-}

+-monoʳ-≤ : ∀ {n p q : ℕ} → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ {zero} h = h
+-monoʳ-≤ {suc n} h = s≤s (+-monoʳ-≤ {n} h)

+-monoˡ-≤ : ∀ {n p q : ℕ} → p ≤ q → p + n ≤ q + n
+-monoˡ-≤ {n} {p} {q} h
  rewrite +-comm p n
        | +-comm q n = +-monoʳ-≤ {n} {p} {q} h

+-mono-≤ : ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ hmn hpq = ≤-trans (+-monoˡ-≤ hmn) (+-monoʳ-≤ hpq)

*-monoʳ-≤ : ∀ {n p q : ℕ} → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ {zero} _ = z≤n
*-monoʳ-≤ {suc n} {p} {q} h =
  +-mono-≤ {p} {q} {n * p} {n * q} h (*-monoʳ-≤ {n} h)

*-monoˡ-≤ : ∀ {n p q : ℕ} → p ≤ q → p * n ≤ q * n
*-monoˡ-≤ {n} {p} {q} h
  rewrite *-comm p n
        | *-comm q n = *-monoʳ-≤ {n} {p} {q} h

*-mono-≤ : ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ {_} {n} hmn hpq = ≤-trans (*-monoˡ-≤ hmn) (*-monoʳ-≤ {n} hpq)

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n} → zero < suc n
  s<s : ∀ {m n} → m < n → suc m < suc n
infix 4 _<_

<-trans : ∀ {m n o : ℕ} → m < n → n < o → m < o
<-trans {zero} {_} {suc o} _ _ = z<s
<-trans (s<s hmn) (s<s hno) = s<s (<-trans hmn hno)

record _↔_ (L R : Set) : Set where
  field
    l→r : L → R
    r→l : R → L
open _↔_ public

≤→< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤→< {zero} {suc n} _ = z<s
≤→< {suc m} {suc n} (s≤s h) = s<s (≤→< h)

<→≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<→≤ {zero} {suc n} _ = s≤s z≤n
<→≤ {suc m} {suc n} (s<s h) = s≤s (<→≤ h)

≤↔< : ∀ {m n : ℕ} → (suc m ≤ n) ↔ (m < n)
(l→r ≤↔<) = ≤→<
(r→l ≤↔<) = <→≤

<-trans-revisited : ∀ {m n o : ℕ} → m < n → n < o → m < o
<-trans-revisited hmn hno =
  ≤→< (≤-trans (<→≤ hmn) (helper (<→≤ hno))) where
    helper : {m n : ℕ} → suc m ≤ n → m ≤ n
    helper {zero} _ = z≤n
    helper {suc m} (s≤s h) = s≤s (helper h)

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : {n : ℕ} → odd n → even (suc n)

data odd where
  suc : {n : ℕ} → even n → odd (suc n)

{-
using a parlance that is tedius
e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
e+e≡e zero hn = hn
e+e≡e {suc (suc m)} (suc (suc hm)) hn = suc (suc (e+e≡e hm hn))
-}

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)
e+e≡e zero hn = hn
e+e≡e (suc hm) hn = suc (o+e≡o hm hn)
o+e≡o (suc hm) hn = suc (e+e≡e hm hn)

+-sucʳ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-sucʳ zero _ = refl
+-sucʳ (suc m) n = cong suc (+-sucʳ m n)

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e {suc m} {suc n} (suc hm) (suc hn)
  rewrite (cong (λ x → even (suc x)) (+-sucʳ m n)) =
    suc (suc (e+e≡e hm hn))
