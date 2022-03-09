import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)
{-# BUILTIN NATPLUS _+_ #-}

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)
{-# BUILTIN NATTIMES _*_ #-}

infixl 6 _+_
infixl 7 _*_

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = (inc n) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

_ : to 7 ≡ ⟨⟩ I I I
_ = refl

from : Bin → ℕ
from ⟨⟩ = 0
from (n O) = 2 * from n
from (n I) = suc (2 * from n)

_ : from (⟨⟩ I O I) ≡ 5
_ = refl
