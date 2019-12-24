module plfa.part1.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl;cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using () renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Relations using (_<_;_≤_; z<s; s<s)
open plfa.part1.Relations._≤_
open import plfa.part1.Isomorphism using (_⇔_)

_↯_ : {A B : Set} → A → ¬ A → B
_↯_ = ¬¬-intro

data Bool : Set where
  true : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n

T : Bool → Set
T true = ⊤
T false = ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt = refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

-- ≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
-- ≤ᵇ→≤ zero    n       tt  =  z≤n
-- ≤ᵇ→≤ (suc m) zero    ()
-- ≤ᵇ→≤ (suc m) (suc n) t   =  s≤s (≤ᵇ→≤ m n t)

-- Seems like we don't have to show the () cases
≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n tt = z≤n
≤ᵇ→≤ (suc m) (suc n) p = s≤s (≤ᵇ→≤ m n p)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? n                  = yes z≤n
suc m ≤? zero               = no ¬s≤z -- no (λ ())
suc m ≤? suc n with m ≤? n
...               | yes m≤n = yes (s≤s m≤n)
...               | no ¬m≤n = no (¬s≤s ¬m≤n)

{- NB The test says this:
(A subtlety: if we do not define ¬s≤z and ¬s≤s as top-level functions, but instead use inline anonymous functions then Agda may have trouble normalising evidence of negation.)
-}

¬z<z : ¬ (zero < zero)
¬z<z ()

¬s<z : ∀ {m : ℕ} → ¬ (suc m < zero)
¬s<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero  <? zero               = no (¬z<z)
zero  <? suc n              = yes z<s
suc m <? zero               = no ¬s<z
suc m <? suc n with m <? n
...               | yes m<n = yes (s<s m<n)
...               | no ¬m<n = no (¬s<s ¬m<n)

-- ^ Seems like evidence like = no (λ()) reduce just fine but you
-- see λ() instead of ¬s<z or ¬z<z which are much more
-- informative than λ()

¬z≡s : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
¬z≡s ()

¬s≡z : ∀ {m : ℕ} → ¬ (suc m ≡ zero)
¬s≡z ()

¬s≡s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬s≡s ¬m≡n refl = ¬m≡n refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero  ≡ℕ? zero               = yes refl
zero  ≡ℕ? suc n              = no ¬z≡s
suc m ≡ℕ? zero               = no ¬s≡z
suc m ≡ℕ? suc n with m ≡ℕ? n
...                | yes m≡n = yes (cong suc m≡n)
...                | no ¬m≡n = no (¬s≡s ¬m≡n)

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = {!   !}
...        | false  | _        | ¬p           = {!   !}

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no x ⌋ = false

_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋

-- We can omit the () case, if we have a T ⌊ D ⌋ it is tt and yes
toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt = x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {_} {yes x} _ = tt
fromWitness {_} {no ¬x} x = ¬x x

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x)  =  no (¬¬-intro x)
¬? (no ¬x)  =  yes ¬x

-- Not sure why this behaves how it does. I guess a form of
-- "Ex falso quodlibet" False implies anything, true doesn't
-- imply false.
_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes x) (yes y) = refl
∧-× (yes x) (no ¬y) = refl
∧-× (no ¬x) y = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes x) y = refl
∨-⊎ (no ¬x) (yes y) = refl
∨-⊎ (no ¬x) (no ¬y) = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes x) = refl
not-¬ (no ¬x) = refl

module iff-erasure where
  open _⇔_
  
  -- I don't understand how to phrase this, I don't know logic.
  -- So I copied this from a truth table.
  -- Why is implication `false => anything = true` but iff is
  -- `false <=> false = true`?
  _iff_ : Bool → Bool → Bool
  true  iff true  = true
  true  iff false = false
  false iff true  = false
  false iff false = true -- why is this true?

  _⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
  yes a ⇔-dec yes b = yes record { to = λ _ → b
                                 ; from = λ _ → a }
  yes a ⇔-dec no ¬b = no (λ a⇔b → ¬b (to a⇔b a))
  no ¬a ⇔-dec yes b = no (λ a⇔b → ¬a (from a⇔b b))
  no ¬a ⇔-dec no ¬b = yes record { to = λ a → a ↯ ¬a
                                 ; from = λ b → b ↯ ¬b }
  
  iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
  iff-⇔ (yes x) (yes y) = refl
  iff-⇔ (yes x) (no ¬y) = refl
  iff-⇔ (no ¬x) (yes y) = refl
  iff-⇔ (no ¬x) (no ¬y) = refl




