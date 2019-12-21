module plfa.part1.Negation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl;cong;cong₂)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_;_,_)
open import plfa.part1.Isomorphism using (_≃_; extensionality; _≲_)
open import plfa.part1.Relations using (_<_;z<s;s<s)
open import plfa.part1.Connectives using (→-elim;η-→)

¬_ : Set → Set
¬_ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x = λ ¬x → ¬x x

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ x → ⊥-elim (¬x x)

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero = λ ()
<-irreflexive (suc n) (s<s a) = <-irreflexive n a

_≮_ : ∀ (n m : ℕ) → Set
n ≮ m = ¬ (n < m)

_↯_ : ∀ {A B : Set} → A → ¬ A → B
p ↯ ¬p = ⊥-elim (¬p p)

-- good luck reading this
trichotomy : ∀ (m n : ℕ)
           → m < n × m ≢ n × n ≮ m
           ⊎ m ≮ n × m ≡ n × n ≮ m
           ⊎ m ≮ n × m ≢ n × n < m
trichotomy zero zero = inj₂ (inj₁ ((λ ()) , refl , λ ()))
trichotomy zero (suc n) = inj₁ (z<s , (λ ()) , (λ ()))
trichotomy (suc m) zero = inj₂ (inj₂ ((λ ()) , (λ ()) , z<s))
trichotomy (suc m) (suc n) with trichotomy m n
trichotomy (suc m) (suc n) | inj₁ (m<n , m≢n , n≮m) =
  inj₁ ( s<s m<n
       , (λ { refl → m<n ↯ n≮m })
       , λ { (s<s n<m) → n<m ↯ n≮m })
trichotomy (suc m) (suc n) | inj₂ (inj₁ (m≮n , m≡n , n≮m)) =
  inj₂ (inj₁ ( (λ { (s<s m<n) → m<n ↯ m≮n })
             , cong suc m≡n
             , λ { (s<s n<m) → n<m ↯ n≮m }))
trichotomy (suc m) (suc n) | inj₂ (inj₂ (m≮n , m≢n , n<m)) =
  inj₂ (inj₂ ( (λ { (s<s m<n) → m<n ↯ m≮n })
             , (λ{ refl → refl ↯ m≢n })
             , s<s n<m))

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
    { to = λ ¬[a⊎b] → (λ a → inj₁ a ↯ ¬[a⊎b])
                    , (λ b → inj₂ b ↯ ¬[a⊎b])
    ; from = λ { (¬a , ¬b) (inj₁ a) → ¬a a
               ; (¬a , ¬b) (inj₂ b) → ¬b b
               }
    ; from∘to = λ ¬[a⊍b] → assimilation _ ¬[a⊍b]
    -- ; from∘to = λ ¬[a⊍b] → extensionality
                -- λ { a@(inj₁ _) → a ↯ ¬[a⊍b]
                  -- ; b@(inj₂ _) → b ↯ ¬[a⊍b]} 
    ; to∘from = λ { (¬a , ¬b) →
      cong₂ _,_ (assimilation _ ¬a) (assimilation _ ¬b)}
    }

-- I don't think so, we can't construct A × B from A.
-- ¬ (A × B) is a proof that (A × B) doesn't hold, not a proof
-- that ¬A × ¬B holds.
×-dual-⊎ : ∀ {A B : Set} → ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
×-dual-⊎ =
  record
    { to      = λ {¬a×b → inj₁ (contraposition {!   !} ¬a×b)}
    ; from    = λ { (inj₁ ¬a) → {!   !} ; (inj₂ y) → {!   !}}
    ; from∘to = λ {w →  {!   !}}
    ; to∘from = λ {w →  {!   !}}
    }


-- ^ Q. If so, prove; if not, can you give a relation weaker than isomorphism that relates the two sides?
-- I don't know any other relations. ≲ still has 'to' and 'from'
-- which I couldn't prove above, so no I guess?

×-partial-dual-⊎ : ∀ {A B : Set} → ¬ (A × B) ≲ (¬ A) ⊎ (¬ B)
×-partial-dual-⊎ =
  record
    { to      = λ {w →  {!   !} }
    ; from    = λ {w →  {!   !} }
    ; from∘to = λ {w →  {!   !}}
    }





