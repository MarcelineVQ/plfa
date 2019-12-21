module plfa.part1.Bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)

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
to zero = ⟨⟩
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * from b
from (b I) = 1 + (2 * from b)

_ : to (from (⟨⟩ O)) ≡ ⟨⟩
_ = refl

_ : to (from (⟨⟩ I)) ≡ ⟨⟩ I
_ = refl

_ : to (from (⟨⟩ I O)) ≡ ⟨⟩ I O
_ = refl

_ : to (from (⟨⟩ I I)) ≡ ⟨⟩ I I
_ = refl

_ : to (from (⟨⟩ I I O)) ≡ ⟨⟩ I I O
_ = refl

inc-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc-suc ⟨⟩ = refl
inc-suc (b O) = refl
inc-suc (b I) rewrite inc-suc b
                  | +-comm (from b) (suc (from b + 0))
                  | +-comm (from b) zero
                  = refl
{-
to_from : ∀ (b : Bin) → to (from b) ≡ b
to ⟨⟩ from = {!   !} -- can't prove ⟨⟩ O ≡ ⟨⟩
to b O from = {!   !}
to b I from = {!   !}
-}
from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n) rewrite inc-suc (to n) = cong suc (from-to n)
