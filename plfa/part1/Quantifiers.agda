module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;refl;cong;cong₂;trans;cong-app;sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm;*-comm;+-suc)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁;proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import plfa.part1.Isomorphism using (_≃_; ∀-extensionality; extensionality;_⇔_)
open import Function using (_∘_)
open import plfa.part1.Relations using (even;odd;_≤_;≤-refl;s≤s;z≤n;≤-trans)

-- I don't like that the last two are just refl porbbaly due to
-- my 'to' but w/e, it's not really a bad thing.
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ x→Bx×Cx → ⟨ proj₁ ∘ x→Bx×Cx , proj₂ ∘ x→Bx×Cx ⟩
    ; from = λ { ⟨ x→Bx , x→Cx ⟩ x → ⟨ (x→Bx x) , (x→Cx x) ⟩}
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ a→bx) a = inj₁ (a→bx a)
⊎∀-implies-∀⊎ (inj₂ a→cx) a = inj₂ (a→cx a)

-- Q. Does the converse hold?
∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x ⊎ C x) → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
∀⊎-implies-⊎∀ x = {!   !}
-- I don't see how it can  x : (x₁ : A) → B x₁ ⊎ C x₁  which means
-- that we don't know whether we have a B or C untill we apply it
-- to an A, and we don't have an A until we are locked in to
-- choosing B or C.

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

-- B : Tri → Set

∀-x : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x ) ≃ (B aa × B bb × B cc)
∀-x =
  record
    { to = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
    ; from = λ { ⟨ a , ⟨ b , c ⟩ ⟩ → λ { aa → a ; bb → b ; cc → c}}
    ; from∘to = λ f → ∀-extensionality λ { aa → refl ; bb → refl ; cc → refl}
    ; to∘from = λ y → refl
    }


data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B


Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
       → (∀ x → B x → C)
       → ∃[ x ] B x
       → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = λ { ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩
             ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩}
    ; from = λ { (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩
               ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , inj₂ Cx ⟩}
    ; from∘to = λ { ⟨ x , inj₁ x₁ ⟩ → refl
                  ; ⟨ x , inj₂ y ⟩ → refl}
    ; to∘from = λ { (inj₁ ⟨ x , y ⟩) → refl
                  ; (inj₂ ⟨ x , y ⟩) → refl}
    }


∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ Bx , Cx ⟩ ⟩ = ⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩

-- This doesn't seem to hold, is this because ∃ [ x ] aren't equivalent? While there exists some x thus y, it's not the same x?
×∃-implies-∃× : ∀ {A : Set} {B C : A → Set} →
  (∃[ x ] B x) × (∃[ x ] C x) → ∃[ x ] (B x × C x)
×∃-implies-∃× ⟨ b , c  ⟩ = {!   !}
-- These 'show this is impossible' questions are extremely difficult because I don't know anything. How do I prove what I don't know?
-- That is to say, that I can't prove it doesn't mean it can't be proven!

∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ = 
  record
    { to = λ { ⟨ aa , Baa ⟩ → inj₁ Baa
             ; ⟨ bb , Bbb ⟩ → inj₂ (inj₁ Bbb)
             ; ⟨ cc , Bcc ⟩ → inj₂ (inj₂ Bcc) }
    ; from = λ { (inj₁ Baa) → ⟨ aa , Baa ⟩
               ; (inj₂ (inj₁ Bbb)) → ⟨ bb , Bbb ⟩
               ; (inj₂ (inj₂ Bcc)) → ⟨ cc , Bcc ⟩ }
    ; from∘to = λ { ⟨ aa , _ ⟩ → refl
                  ; ⟨ bb , _ ⟩ → refl
                  ; ⟨ cc , _ ⟩ → refl }
    ; to∘from = λ { (inj₁ x) → refl
                  ; (inj₂ (inj₁ x)) → refl
                  ; (inj₂ (inj₂ y)) → refl }
    }

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (     m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] ( 1 + m * 2 ≡ n)

even-∃ even.zero = ⟨ zero , refl ⟩
even-∃ (even.suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd.suc e) with even-∃ e
...                  | ⟨ m , refl ⟩ = ⟨ m , refl ⟩


∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even.zero
∃-even ⟨ suc m , refl ⟩  =  even.suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd.suc (∃-even ⟨ m , refl ⟩)

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n

feb : ∀ (m : ℕ) →  m * 2 ≡ m + m
feb m rewrite *-comm m 2 | +-comm m zero = refl

∃-even′ ⟨ zero , refl ⟩ = even.zero
∃-even′ ⟨ suc m , refl ⟩ rewrite +-comm m zero | +-comm m (suc m) = even.suc (∃-odd ⟨ m , cong suc (feb m) ⟩)

∃-odd′ ⟨ m , refl ⟩ rewrite +-comm m zero | +-comm (m + m) 1 = odd.suc (∃-even ⟨ m , feb m ⟩)

feh : ∀ {x y : ℕ} → y ≤ x + y
feh {_} {zero} = z≤n
feh {x} {suc y} rewrite +-suc x y = s≤s feh

∃-+-≤ : ∀ {x y z : ℕ} → ((y ≤ z) ⇔ (∃[ x ] (x + y ≡ z)))
∃-+-≤ {x} {y} {z} =
  record
    { from = λ { ⟨ n , refl ⟩ → feh
               }
    ; to = λ { z≤n  → ⟨ z , +-comm z zero ⟩
             ; (s≤s {m} {n} s) → 
             let c = to (∃-+-≤ {zero} {m} {n}) s
                 ⟨ j , k ⟩ = c
             in ⟨ {!   !} , {!   !} ⟩
             }
    }
  where open _⇔_
{-
Above says:

Expected record pattern
when checking the let binding ⟨ j , k ⟩ = c

If I replace our definition of Σ at line #55 with an
import of Σ from Data.Product there is no error.
I understand that Data.Product.Σ is a record but
why does it need a 'record pattern' in the first place?
What is a record pattern?
Is ⟨ , ⟩ not a constructor, why isn't that a valid pattern?

-}
