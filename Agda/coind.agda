{-# OPTIONS --guardedness #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
open Stream using (hd; tl)

{-
Any natural number is in the stream of all natural numbers.
-}
natsfrom : ℕ → Stream ℕ
hd (natsfrom n) = n
tl (natsfrom n) = natsfrom (suc n)

allnats : Stream ℕ
allnats = natsfrom zero

data _∈_ {A} : A → Stream A → Set where
  here : ∀ {x xs} → x ≡ hd xs → x ∈ xs
  there : ∀ {x xs} → x ∈ tl xs → x ∈ xs
infix 4 _∈_

lemma₁ : ∀ {m : ℕ} (n : ℕ) → m ∈ natsfrom n → m ∈ allnats
lemma₁ zero h = h
lemma₁ (suc n) h = lemma₁ n (there h)

natinnats : ∀ (n : ℕ) → n ∈ allnats
natinnats n = lemma₁ n (here refl)

{-
Any stream keeps unchanged after being splitted and merged.
-}
even : ∀ {A} → Stream A → Stream A
hd (even xs) = hd xs
tl (even xs) = even (tl (tl xs))

odd : ∀ {A} → Stream A → Stream A
odd xs = even (tl xs)

split : ∀ {A} → Stream A → Stream A × Stream A
split xs = even xs , odd xs

merge : ∀ {A} → Stream A × Stream A → Stream A
hd (merge (l , r)) = hd l
tl (merge (l , r)) = merge (r , tl l)

record _≈_ {A} (m n : Stream A) : Set where
  coinductive
  field
    hd-≡ : hd m ≡ hd n
    tl-≈ : tl m ≈ tl n
open _≈_ using (hd-≡; tl-≈)
infix 4 _≈_

identity : ∀ {A} (xs : Stream A) → merge (split xs) ≈ xs
hd-≡ (identity xs) = refl
tl-≈ (identity xs) = identity (tl xs)
