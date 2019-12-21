module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-aassoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-aassoc zero n p = refl
+-aassoc (suc m) n p = cong suc (+-aassoc m n p)

+-aassoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-aassoc' zero n p = refl
+-aassoc' (suc m) n p rewrite +-aassoc' m n p = refl

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm m zero = +-identityʳ m
+-comm m (suc n) = trans (+-suc m n) (cong suc (+-comm m n))

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
   (m + (n + p)) + q
  ∎

+-rearrange' : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange' m n p q
  rewrite +-assoc m n (p + q)
        | cong (m +_) (sym (+-assoc n p q))
        | sym (+-assoc m (n + p) q)
        = refl

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p)
                   | +-comm m n
                   | +-assoc n m p = refl

*-zeroʳ : ∀ (n : ℕ) → n * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc n) = *-zeroʳ n

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p
        | sym (+-assoc p (m * p) (n * p)) = refl

*-assoc : ∀ (n m p : ℕ) → (n * m) * p ≡ n * (m * p)
*-assoc zero m p = refl
*-assoc (suc n) m p rewrite *-distrib-+ m (n * m) p
                          | sym (*-assoc n m p) = refl

-- surely this is longer than it needs to be 
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-zeroʳ m = refl
*-comm zero (suc n) rewrite *-zeroʳ n = refl
*-comm (suc m) (suc n) rewrite *-comm m (suc n)
                             | *-comm n (suc m)
                             | *-comm m n
                             | sym (+-assoc n m (n * m))
                             | sym (+-assoc m n (n * m))
                             | +-comm n m
                               = refl

∸-identityˡ : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-identityˡ zero = refl
∸-identityˡ (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite ∸-identityˡ n
                         | ∸-identityˡ p
                         | ∸-identityˡ (n + p) = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

*-identityʳ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityʳ zero = refl
*-identityʳ (suc n) = cong suc (*-identityʳ n)

+-suc-right-suc : ∀ (n m : ℕ) → n + suc m ≡ suc (n + m)
+-suc-right-suc zero m = refl
+-suc-right-suc (suc n) m = cong suc (+-suc-right-suc n m)

^+-distrib-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^+-distrib-* m zero zero = refl
^+-distrib-* m zero (suc p) rewrite +-identityʳ (m * (m ^ p)) = refl
^+-distrib-* m (suc n) zero rewrite +-identityʳ n
                                  | *-identityʳ (m * (m ^ n)) = refl
^+-distrib-* m (suc n) (suc p)
  rewrite *-assoc m (m ^ n) (m * (m ^ p))
        | *-comm m (m ^ p)
        | sym (*-assoc (m ^ n) (m ^ p) m)
        | sym (^+-distrib-* m n p)
        | +-suc-right-suc n p
        | sym (*-comm m (m ^ (n + p)))
        = refl

^*-distrib-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^*-distrib-* m n zero = refl
^*-distrib-* m n (suc p) rewrite sym (*-assoc (m * (m ^ p)) n (n ^ p))
                               | *-comm (m * (m ^ p)) n
                               | sym (*-assoc n m (m ^ p))
                               | *-comm n m 
                               | ^*-distrib-* m n p
                               | sym (*-assoc (m * n) (m ^ p) (n ^ p))
                               = refl

^-one : ∀ (n : ℕ) → 1 ≡ 1 ^ n
^-one zero = refl
^-one (suc n) rewrite sym (^-one n) = refl

^*-distrib-^ : ∀ (m n p : ℕ) → m ^ (n * p) ≡ (m ^ n) ^ p
^*-distrib-^ m zero p = ^-one p
^*-distrib-^ m (suc n) p rewrite ^*-distrib-* m (m ^ n) p
                               | sym (^*-distrib-^ m n p )
                               | sym (^+-distrib-* m p ((n * p)))
                               = refl


