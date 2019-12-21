module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality;_⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

infixr 2 _×_
data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : (x : A) → (y : B) → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = record
  { to      = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ }
  ; from    = λ { ⟨ y , x ⟩ → ⟨ x , y ⟩ }
  ; from∘to = λ { ⟨ x , y ⟩ → refl }
  ; to∘from = λ { ⟨ x , y ⟩ → refl}
  }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = 
  record
    { to      = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩}
    ; from    = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩}
    ; from∘to = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → refl}
    ; to∘from = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → refl}
    }

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ ((A → B) × (B → A))
⇔≃× = 
  record
    { to      = λ {x → ⟨ _⇔_.to x , _⇔_.from x ⟩}
    ; from    = λ { ⟨ x , y ⟩ → _⇔_.iff x y}
    ; from∘to = λ {x → refl}
    ; to∘from = λ { ⟨ x , y ⟩ → refl}
    }

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

infix 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} → (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B)
       → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to      = λ { (inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y}
    ; from    = λ { (inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y}
    ; from∘to = λ { (inj₁ x) → refl ; (inj₂ y) → refl}
    ; to∘from = λ { (inj₁ x) → refl ; (inj₂ y) → refl}
    }

--hideous
⊎-assoc : ∀ {A B C : Set} → A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
⊎-assoc =
  record
    { to      = λ { (inj₁ x) → inj₁ (inj₁ x)
                  ; (inj₂ (inj₁ x)) → inj₁ (inj₂ x)
                  ; (inj₂ (inj₂ y)) → inj₂ y}
    ; from    = λ { (inj₁ (inj₁ x)) → inj₁ x
                  ; (inj₁ (inj₂ y)) → inj₂ (inj₁ y)
                  ; (inj₂ y) → inj₂ (inj₂ y)}
    ; from∘to = λ { (inj₁ x) → refl
                  ; (inj₂ (inj₁ x)) → refl
                  ; (inj₂ (inj₂ y)) → refl}
    ; to∘from = λ { (inj₁ (inj₁ x)) → refl
                  ; (inj₁ (inj₂ y)) → refl
                  ; (inj₂ y) → refl}
    }

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ { C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-identityˡ : ∀ {B : Set} → (⊥ ⊎ B) ≃ B
⊥-identityˡ =
  record
    { to      = λ { (inj₂ y) → y }
    ; from    = λ { w → inj₂ w }
    ; from∘to = λ { (inj₂ y) → refl }
    ; to∘from = λ { w → refl }
    }

⊥-identityʳ : ∀ {B : Set} → (B ⊎ ⊥) ≃ B
⊥-identityʳ {B} =
  ≃-begin
    (B ⊎ ⊥)
  ≃⟨ ⊎-comm {B} {⊥} ⟩
    (⊥ ⊎ B)
  ≃⟨ ⊥-identityˡ {B} ⟩
    B
  ≃-∎

→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      = λ{ f → λ { ⟨ x , y ⟩ → f x y}}
    ; from    = λ{ g → λ x y → g ⟨ x , y ⟩ }
    ; from∘to = λ{ f → refl}
    ; to∘from = λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl}}
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ a → ⟨ g a , h a ⟩} }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } } 
    ; to∘from = λ{ ⟨ x , y ⟩ → refl }
    }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , y ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ y₁ , y ⟩ = inj₂ ⟨ y₁ , y ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ x , y ⟩) = ⟨ inj₂ x , inj₂ y ⟩

-- No, this can't hold. We might have A × D, which can't
-- construct (A × B) or (C × D)
postulate
  ×⊎-implies-⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)



