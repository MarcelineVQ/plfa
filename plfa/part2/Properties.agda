module plfa.part2.Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plfa.part1.Isomorphism
open import plfa.part2.Lambda

V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ        ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N

infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ


-- casing cv or v will skip creating impossible/empty cases
-- casing both cv and v at once will retain them.
canonical : ∀ {V A} → ∅ ⊢ V ⦂ A → Value V → Canonical V ⦂ A
canonical cv v = {!   !}

-- cased cv
canonical' : ∀ {V A} → ∅ ⊢ V ⦂ A → Value V → Canonical V ⦂ A
canonical' (⊢ƛ cv) v = {!   !}
canonical' ⊢zero v = {!   !}
canonical' (⊢suc cv) v = {!   !}

-- cased v
canonical'' : ∀ {V A} → ∅ ⊢ V ⦂ A → Value V → Canonical V ⦂ A
canonical'' cv V-ƛ = {!   !}
canonical'' cv V-zero = {!   !}
canonical'' cv (V-suc v) = {!   !}

--cased both at once
canonical''' : ∀ {V A} → ∅ ⊢ V ⦂ A → Value V → Canonical V ⦂ A
canonical''' (⊢` x) ()
canonical''' (⊢ƛ cv) V-ƛ = {!   !}
canonical''' (cv · cv₁) ()
canonical''' ⊢zero V-zero = {!   !}
canonical''' (⊢suc cv) (V-suc v) = {!   !}
canonical''' (⊢case cv cv₁ cv₂) ()
canonical''' (⊢μ cv) ()



