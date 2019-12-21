module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)
open import plfa.part1.Bin

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m) (s≤s n) = s≤s (≤-trans m n)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m) (s≤s n) = cong suc (≤-antisym m n)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)


+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q =
  let g = +-monoˡ-≤ p q (n * p) p≤q
      h = +-monoʳ-≤ q (n * p) (n * q) (*-monoʳ-≤ n p q p≤q)
  in ≤-trans g h

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤  m n p p≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n p≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-trans : ∀ {m p q : ℕ} → m < p → p < q → m < q
<-trans z<s (s<s p<q) = z<s
<-trans (s<s m<p) (s<s p<q) = s<s (<-trans m<p p<q)

data Trichotomy (m n : ℕ) : Set where
  m<n : m < n → Trichotomy m n
  m≡n : m ≡ n → Trichotomy m n
  m>n : n < m → Trichotomy m n

trichotomy : (m n : ℕ) → Trichotomy m n
trichotomy zero zero = m≡n refl
trichotomy zero (suc n) = m<n z<s
trichotomy (suc m) zero = m>n z<s
trichotomy (suc m) (suc n) with trichotomy m n
...                           | m<n a = m<n (s<s a)
...                           | m≡n refl = m≡n (cong suc refl)
...                           | m>n c = m>n (s<s c)

≤-iff-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-iff-< (s≤s z≤n) = z<s
≤-iff-< (s≤s (s≤s mn)) = s<s (≤-iff-< (s≤s mn))

<-iff-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-iff-≤ z<s = s≤s z≤n
<-iff-≤ (s<s mn) = s≤s (<-iff-≤ mn)

foo : ∀ {p q : ℕ} → suc p ≤ q -> p ≤ q
foo (s≤s z≤n) = z≤n
foo (s≤s (s≤s pq)) = s≤s (foo (s≤s pq))

<-trans-revisited : ∀ {m n p q : ℕ} → m < p → p < q → m < q
<-trans-revisited mp pq = ≤-iff-< (≤-trans (<-iff-≤ mp) (foo (<-iff-≤ pq)))

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n -> odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc x) n = suc (e+e≡e x n)

-- :/
o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (n + m)
o+o≡e (suc zero) (suc zero) = suc (suc zero)
o+o≡e (suc zero) (suc (suc x)) = suc (suc (o+o≡e (suc zero) x))
o+o≡e (suc (suc x)) (suc zero) = suc (suc (suc x))
o+o≡e (suc (suc x)) (suc (suc x₁)) = suc (suc (o+o≡e (suc (suc x)) x₁))

data One : Bin → Set where
  one : One (⟨⟩ I)
  suc : ∀ {b : Bin} → One b → One (inc b)

data Can : Bin → Set where
  ℂ⟨⟩ : Can ⟨⟩ 
  ℂI : ∀ {b : Bin} → One b → Can b

inc-canonical : ∀ {b : Bin} → Can b → Can (inc b)
inc-canonical ℂ⟨⟩ = ℂI one
inc-canonical (ℂI one) = ℂI (suc one)
inc-canonical (ℂI (suc x)) = ℂI (suc (suc x))

nat-canonical : ∀ (n : ℕ) → Can (to n)
nat-canonical zero = ℂ⟨⟩
nat-canonical (suc n) = inc-canonical (nat-canonical n)

one-ident : ∀ {b : Bin} → One b → to (from b) ≡ b
one-ident one = refl
one-ident (suc {b} c) rewrite inc-suc b = cong inc (one-ident c)

canonical-ident : ∀ {b : Bin} → Can b → to (from b) ≡ b
canonical-ident ℂ⟨⟩ = refl
canonical-ident (ℂI x) = one-ident x




