module plfa.part1.Equality where

data _≡_ {A : Set} (x : A) : (y : A) -> Set where
  refl : x ≡ x
infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} { x y z : A} → x ≡ y → y ≡ z → x ≡ z 
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
      → u ≡ x
      → v ≡ y
      → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B}
         → f ≡ g
         → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
      → x ≡ y
      → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where
  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
         → x ≡ y
         → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
        → x ≡ y
        → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
         → x ≡ y
         → y ≡ z
         → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

trans' : ∀ {A : Set} {x y z : A}
       → x ≡ y
       → y ≡ z
       → x ≡ z
trans' {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎
  where open ≡-Reasoning

module NatStuff where
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero    + n  =  n
  (suc m) + n  =  suc (m + n)

  postulate
    +-identity : ∀ (m : ℕ) → m + zero ≡ m
    +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm m zero =
    begin
      m + zero
    ≡⟨ +-identity m ⟩
      m
    ≡⟨⟩
      zero + m
    ∎
    where open ≡-Reasoning
  +-comm m (suc n) =
    begin
      m + suc n
    ≡⟨ +-suc m n ⟩
      suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
      suc (n + m)
    ≡⟨⟩
      suc n + m
    ∎
    where open ≡-Reasoning
    
  data even : ℕ → Set
  data odd : ℕ → Set

  data even where
    even-zero : even zero
    even-suc : ∀ {n : ℕ} → odd n → even (suc n)
  
  data odd where
    odd-suc : ∀ {n : ℕ} → even n → odd (suc n)


module ≤-Reasoning where
  open import plfa.part1.Relations using (_≤_;≤-trans;s≤s;z≤n;≤-refl)
  open import Data.Nat hiding (_≤_)
  open import Data.Nat.Properties using (+-comm;+-suc)
  
  infix  1 begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : ℕ}
         → x ≤ y
         → x ≤ y
  begin x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
        → x ≤ y
        → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
         → x ≤ y
         → y ≤ z
         → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _∎ : ∀ (x : ℕ) → x ≤ x
  x ∎ = ≤-refl

  -- (c)lean
  +-monoʳ-≤c : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
  +-monoʳ-≤c zero p q p≤q = p≤q
  +-monoʳ-≤c (suc n) p q p≤q = s≤s (+-monoʳ-≤c n p q p≤q)
  
  -- What are these nats even conveying to the reader?
  +-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
  +-monoʳ-≤ zero p q p≤q = p≤q
  +-monoʳ-≤ (suc n) p q p≤q =
    begin
      suc n + p -- ???
    ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
      suc (n + q) -- ???
    ∎
  -- (c)lean
  +-monoˡ-≤c : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
  +-monoˡ-≤c m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy -- x≐y (_≡_ x) refl
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x



{-

4666b7ba-1ea4-11ea-9f0e-0242ac1c0002
cf7486c2-1ea4-11ea-9f0e-0242ac1c0002
320a182e-1ea5-11ea-9f0e-0242ac1c0002
a30adfae-1ea5-11ea-9f0e-0242ac1c0002
ef01288c-1ea5-11ea-9f0e-0242ac1c0002
aacc60b8-1ea6-11ea-9f0e-0242ac1c0002
f62c8cae-1ea6-11ea-9f0e-0242ac1c0002

bf48f5f0-1ea7-11ea-9f0e-0242ac1c0002

f51986bc-1f57-11ea-ac0b-0242ac1c0002

6345ce46-1f5a-11ea-ae9d-0242ac1c0002

28a41aa8-1f5b-11ea-a335-0242ac1c0002

58f9e976-1f5b-11ea-a335-0242ac1c0002

e40502ca-1f9d-11ea-ad9d-0242ac1c0002

10.3 / 24 trailer | 0.429 kw/h

14.7 / 26.2 building | 0.561 kw/h

0.99 kw/h

712kwh per 30 days


f9524548-1f89-11ea-aa90-0242ac1c0002


-}
  
  



