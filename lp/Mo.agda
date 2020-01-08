module lp.Mo where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

data Unit : Set where
  tt : Unit

data CmpNat : ℕ → ℕ → Set where
     CmpLT : ∀ {x} y → CmpNat x (x + suc y)
     CmpEQ : ∀ {x} → CmpNat x x
     CmpGT : ∀ x {y} → CmpNat (y + suc x) y

cmp : (x y : ℕ) → CmpNat x y
cmp 0 0     = CmpEQ
cmp 0 (suc k) = CmpLT k
cmp (suc k) 0 = CmpGT k
cmp (suc x) (suc y) with (cmp x y)
cmp (suc x) (suc .(x + (suc k))) | CmpLT k = CmpLT k
cmp (suc x) (suc x)              | CmpEQ   = CmpEQ
cmp (suc .(y + (suc k))) (suc y) | CmpGT k = CmpGT k

-- why can't I case on c? Why is it not just CmpEQ?
prf : (x : ℕ) → Unit
prf k with cmp k k
prf zero | CmpEQ = tt            -- fine
prf (suc zero) | CmpEQ = tt      -- fine
prf (suc (suc k)) | c = {! c  !} -- how do I unify this?



