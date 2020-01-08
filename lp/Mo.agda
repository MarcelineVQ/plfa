module lp.Mo where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

data CmpNat : ℕ → ℕ → Set where
     CmpLT : ∀ {x} y → CmpNat x (x + suc y)
     CmpEQ : ∀ {x} → CmpNat x x
     CmpGT : ∀ x {y} → CmpNat (y + suc x) y


cmp : (x y : ℕ) → CmpNat x y
cmp zero zero = CmpEQ
cmp zero (suc y) = CmpLT y
cmp (suc x) zero = CmpGT x
cmp (suc x) (suc y) with cmp x y
cmp (suc x) (suc .(x + suc y)) | CmpLT y = CmpLT y
cmp (suc x) (suc .x) | CmpEQ = CmpEQ
cmp (suc .(y + suc x)) (suc y) | CmpGT x = CmpGT x


compareBranch : ∀ {b : Set} → ℕ → ℕ → b → b → b → b
compareBranch m n l e g with (cmp m n)
compareBranch m .(m + suc y) l e g | CmpLT y = l
compareBranch m m l e g | CmpEQ = e
compareBranch .(n + suc x) n l e g | CmpGT x = g


-- I don't understand what the errors below are telling me
-- when I case. Does this have something to do with both arguments
-- to CmpNat being indexes instead of parameters? They have to be
-- indexes for this don't they?

-- why can't I case on p? Why is it not just CmpEQ?
prf : ∀ {A} {l e g : A} → (x : ℕ) → CmpNat x x → compareBranch x x l e g ≡ e
prf k p = {! p  !}
{-
I'm not sure if there should be a case for the constructor CmpLT,
because I get stuck when trying to solve the following unification
problems (inferred index ≟ expected index):
  x ≟ k₁
  x + suc y ≟ k₁
Possible reason why unification failed:
  Cannot solve variable x of type ℕ with solution x + suc y because
  the variable occurs in the solution, or in the type of one of the
  variables in the solution.
when checking that the expression ? has type
compareBranch k k l e g ≡ e
-}

-- why can't I case on c? Why is it not just CmpEQ?
prf' : ∀ {A} {l e g : A} → (x : ℕ) → compareBranch x x l e g ≡ e
prf' k with cmp k k
prf' zero | CmpEQ = refl
prf' (suc k) | c = {!   !}
{-
I'm not sure if there should be a case for the constructor CmpLT,
because I get stuck when trying to solve the following unification
problems (inferred index ≟ expected index):
  x ≟ k₁
  x + suc y ≟ k₁
Possible reason why unification failed:
  Cannot solve variable x of type ℕ with solution x + suc y because
  the variable occurs in the solution, or in the type of one of the
  variables in the solution.
when checking that the expression ? has type
(compareBranch k k l e g | c) ≡ e
-}


