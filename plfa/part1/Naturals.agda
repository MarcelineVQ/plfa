module plfa.part1.Naturals where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


-- skips
-- I want to describe a list indexed by Nat which only contains every nth element of another list

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_ _∸_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)
{-# BUILTIN NATPLUS _+_ #-}

_∸_ : ℕ → ℕ → ℕ
zero ∸ n = zero
m ∸ zero = m
suc m ∸ suc n = m ∸ n
{-# BUILTIN NATMINUS _∸_ #-}

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)
{-# BUILTIN NATTIMES _*_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin


inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ = refl

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl


to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * from b
from (b I) = 1 + (2 * from b)

_ : to (from (⟨⟩ O)) ≡ ⟨⟩ O
_ = refl

_ : to (from (⟨⟩ I)) ≡ ⟨⟩ I
_ = refl

_ : to (from (⟨⟩ I O)) ≡ ⟨⟩ I O
_ = refl

_ : to (from (⟨⟩ I I)) ≡ ⟨⟩ I I
_ = refl

_ : to (from (⟨⟩ I I O)) ≡ ⟨⟩ I I O
_ = refl

foo1 : ∀ (m n : ℕ) → (m + n) ≡ (n + m) 
foo1 = {!   !} -- import this from somewhere

foo2 : ∀ (m : ℕ) → m + zero ≡ m
foo2 = {!   !} -- import this from somewhere

inc_suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc ⟨⟩ suc = refl
inc b O suc = refl
inc b I suc rewrite inc_suc b
                  | foo1 (from b) (suc(from b + 0))
                  | foo2 (from b)
                  = refl

to_from : ∀ (b : Bin) → to (from b) ≡ b
to ⟨⟩ from = {!   !} -- can't prove ⟨⟩ O ≡ ⟨⟩
to b O from = {!   !}
to b I from = {!   !}

from_to : ∀ (n : ℕ) → from (to n) ≡ n
from zero to = refl
from suc n to rewrite inc_suc (to n) = cong suc (from_to n)


--