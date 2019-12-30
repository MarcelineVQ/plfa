module plfa.part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong;cong₂;cong-app)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_;extensionality;∀-extensionality)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

-- rly?
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

length-++′ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++′ [] ys = refl
length-++′ (x ∷ xs) ys = cong suc (length-++′ xs ys)

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

-- cong (_++ [ x ]) was a little tricky but neat
reverse-++-distrib : ∀ {A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) = refl
reverse-++-distrib (x ∷ xs) ys rewrite sym (++-assoc (reverse ys) (reverse xs) [ x ]) = cong (_++ [ x ]) (reverse-++-distrib xs ys)

-- we need to use reverse-++-distrib to put the [ x ] in the lead
-- this lets the reduction of reverse force it to the very front
-- so we can simply cong
reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) rewrite reverse-++-distrib (reverse xs) [ x ] = cong (x ∷_) (reverse-involutive xs)

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

_ : shunt [ 1 , 2 , 3 ] [] ≡ [ 3 , 2 , 1 ]
_ = begin
      shunt [ 1 , 2 , 3 ] []
    ≡⟨⟩
      shunt [ 2 , 3 ] [ 1 ]
    ≡⟨⟩
      shunt [ 3 ] [ 2 , 1 ]
    ≡⟨⟩
      shunt [] [ 3 , 2 , 1 ]
    ≡⟨⟩
      [ 3 , 2 , 1 ]
    ∎

-- NB ! rewrite shunt-reverse xs (x ∷ ys) is valid in Agda
-- because as the text says "the second argument actually becomes
-- larger, but this is not a problem because the argument on
-- which we induct becomes smaller."
shunt-reverse : ∀ {A : Set} (xs ys : List A)
             → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys rewrite shunt-reverse xs (x ∷ ys) | ++-assoc (reverse xs) [ x ] ys = refl

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

-- remember to use C-u C-u C-c C-t to see that reverse′ is shunt
reverses : ∀ {A : Set} (xs : List A) → reverse′ xs ≡ reverse xs
reverses [] = refl
reverses (x ∷ xs) rewrite shunt-reverse xs [ x ] = refl

_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎


map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- I had to make a explicit helper to keep the types lining up.
map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C) → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality (map-compose′ f g)
  where
    map-compose′ : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    map-compose′ f g [] = refl
    map-compose′ f g (x ∷ xs) = cong (g (f x) ∷_) (map-compose′ f g xs)


map-++-distribute : ∀ {A B : Set} {f : A → B} (xs ys : List A)
                  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute [] ys = refl
map-++-distribute {f = f} (x ∷ xs) ys = cong (f x ∷_) (map-++-distribute xs ys)


data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node l x r) = node (map-Tree f g l) (g x) (map-Tree f g r)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : ∀ (xs : List ℕ) → ℕ
product [] = 1
product (x ∷ xs) = x * product xs

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A)
         → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys = cong (x ⊗_) (foldr-++ _⊗_ e xs ys)

foldr-∷ : {A : Set} (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) = cong (_∷_ x) (foldr-∷ xs)

foldr-append-∷ : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
foldr-append-∷ [] ys = refl
foldr-append-∷ (x ∷ xs) ys = cong (_∷_ x) (foldr-append-∷ xs ys)

-- it wants us to prove using foldr-++
foldr-append-∷′ : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
foldr-append-∷′ xs ys rewrite sym (foldr-∷ ys) | sym (foldr-++ _∷_ [] xs ys) | foldr-∷ ys | foldr-∷ (xs ++ ys) = refl

map-is-foldr : ∀ {A B : Set} (f : A → B) → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality help
  where
   help : ∀ {A B : Set} {f : A → B} (xs : List A) → map f xs ≡ foldr (λ x → _∷_ (f x)) [] xs
   help [] = refl
   help {f = f} (x ∷ xs) = cong (_∷_ (f x)) (help xs)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node l x r) = g (fold-Tree f g l) x (fold-Tree f g r)


-- practise for map-Tree-is-fold-Tree
-- Used to discover what map-Tree via fold-Tree looks like.
fold-Tree-g : ∀ {A B : Set} → (t : Tree A B) → fold-Tree leaf node t ≡ t
fold-Tree-g (leaf x) = refl
fold-Tree-g (node l x r) rewrite fold-Tree-g l | fold-Tree-g r = refl

-- practise for map-Tree-is-fold-Tree
-- Used to discover the type signature to write for map-Tree-is-fold-Tree
fold-Tree-map : ∀ {A B C D : Set} → (f : A → C) → (g : B → D)
              → (t : Tree A B) → Tree C D
fold-Tree-map f g t =
  fold-Tree (λ x → leaf (f x)) (λ l x r → node l (g x) r) t


map-Tree-is-fold-Tree : ∀ {A B C D : Set} (f : A → C) (g : B → D) → map-Tree f g ≡ fold-Tree (λ x → leaf (f x)) (λ l x r → node l (g x) r)
map-Tree-is-fold-Tree f g = extensionality λ t → help f g t
  where
    help : ∀ {A B C D : Set} (f : A → C) (g : B → D) (t : Tree A B) → map-Tree f g t ≡ fold-Tree (λ x → leaf (f x)) (λ l x r → node l (g x) r) t
    help f g (leaf x) = refl
    help f g (node l x r) rewrite sym (help f g l) | sym (help f g r) = refl

module DownFrom where
  open import Data.Nat
  open import Data.Nat.Properties
  downFrom : ℕ → List ℕ
  downFrom zero     =  []
  downFrom (suc n)  =  n ∷ downFrom n

  _ : downFrom 3 ≡ [ 2 , 1 , 0 ]
  _ = refl

  geh : ∀ (n : ℕ) → n + n ≡ n * 2
  geh zero = refl
  geh (suc n) rewrite *-comm n 2 | +-identityʳ n = let c = geh n in cong suc (+-suc n n)


  -- kill me
  -- just end my life
  -- what even is this
  -- don't know what to name this (dwtnt)
  dwtnt : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
  dwtnt zero = refl
  dwtnt (suc n) rewrite *-comm (n + foldr _+_ 0 (downFrom n)) 2 | +-identityʳ (n + foldr _+_ 0 (downFrom n)) | +-assoc n (foldr _+_ 0 (downFrom n)) (n + foldr _+_ 0 (downFrom n)) | sym (+-assoc (foldr _+_ 0 (downFrom n)) n (foldr _+_ 0 (downFrom n))) | +-comm (foldr _+_ 0 (downFrom n)) n | +-assoc n (foldr _+_ 0 (downFrom n)) (foldr _+_ 0 (downFrom n)) | sym (+-assoc n n (foldr _+_ 0 (downFrom n) + foldr _+_ 0 (downFrom n))) | geh (foldr _+_ 0 (downFrom n)) | dwtnt n  = {!   !}
    where
    c : ∀ (n : ℕ) → ℕ
    c n = foldr _+_ 0 (downFrom n)
  -- everything I do results in an insane rewrite mess
  -- what even is the right approach
  -- how do I, or should I, remove the ∸
  -- surely this was not the intended exercise

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldl : ∀ {A B : Set} → (B → A → B) → B → (xs : List A) → B
foldl f e [] = e
foldl f e (x ∷ xs) = foldl f (f e x) xs

beb : ∀ {A B : Set} {_⊗_ : B → A → B} {e : B} {x y z : A} → foldl _⊗_ e [ x , y , z ] ≡ ((e ⊗ x) ⊗ y) ⊗ z
beb = refl

foldl-monoid : ∀ {A : Set} {_⊗_ : A → A → A} {e : A} → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs 
foldl-monoid pf [] y = sym (identityʳ pf y)
foldl-monoid {_⊗_ = _⊗_} {e = e} pf (x ∷ xs) y rewrite identityˡ pf x | foldl-monoid pf xs x | foldl-monoid pf xs (y ⊗ x) | assoc pf y x (foldl _⊗_ e xs) = refl

foldr-monoid-foldl : ∀ {A : Set} {_⊗_} {e : A} (xs : List A) → IsMonoid _⊗_ e → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl [] pf = refl
foldr-monoid-foldl (x ∷ xs) pf rewrite foldr-monoid-foldl xs pf | identityˡ pf x | foldl-monoid pf xs x =  refl


data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

feh : ∀ {A : Set} (x : A) (xs ys : List A) → (x ∷ xs) ++ ys ≡ x ∷ (xs ++ ys)
feh x xs ys = refl

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys = record { to = to xs ys; from = from xs ys }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    -- is the with neccesary? I think so because we need to
    -- know whether 'to' resulted in L or R
    to [] ys x = inj₂ x
    to (_ ∷ xs) ys (here x) = inj₁ (here x)
    to (_ ∷ xs) ys (there pf) with to xs ys pf
    ...                          | inj₁ x = inj₁ (there x)
    ...                          | inj₂ y = inj₂ y

    -- can be shortened?
    from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
      Any P xs ⊎ Any P ys → Any P (xs ++ ys)
    from [] ys (inj₂ v) = v
    from (x ∷ xs) ys (inj₁ (here v)) = here v
    from (x ∷ xs) ys (inj₁ (there v)) = there (from xs ys (inj₁ v))
    from (x ∷ xs) ys (inj₂ (here v)) = there (from xs ys (inj₂ (here v)))
    from (x ∷ xs) ys (inj₂ (there v)) = there (from xs ys (inj₂ (there v)))


-- "As a consequence [of Any-++-⇔], demonstrate an equivalence relating _∈_ and _++_."
postulate
  foo : ∀ {A : Set} {x : A} {xs ys} → x ∈ (xs ++ ys) ≃ (x ∈ xs ⊎ x ∈ ys)
  -- but isn't this just Any-++-⇔ again, just with P as x≡ ?
  -- What does it want me to write for this exercise?
  -- What does it mean by equivalence? _≃_ ? _⇔_ ?
  
  -- later exercises suggest that equivalence means _⇔_
  -- and isomorphism means _≃_
  
-- is this really the intent?
∈-++-⇔ : ∀ {A : Set} (x : A) (xs ys : List A) → (x ∈ (xs ++ ys)) ⇔ ((x ∈ xs) ⊎ (x ∈ ys))
∈-++-⇔ x xs ys =
  record
    { to = to (Any-++-⇔ xs ys)
    ; from = from (Any-++-⇔ xs ys)
    }
  where
    open _⇔_

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys =
  record
  { to = to (All-++-⇔ xs ys)
  ; from = from (All-++-⇔ xs ys)
  ; to∘from = to∘from
  ; from∘to = from∘to
  }
  where
    open _⇔_

    to∘from : ∀ {P} → (y : All P xs × All P ys) →
      to (All-++-⇔ xs ys)
      (from (All-++-⇔ xs ys) y)
      ≡ y
    to∘from ⟨ [] , snd ⟩ = refl
    to∘from ⟨ x ∷ fst , snd ⟩ =
      cong₂ ⟨_,_⟩ (cong (x ∷_) {!   !}) {!   !}
    -- ^ how do?
    
    from∘to : ∀ {P} → (y : All P (xs ++ ys))
      → from (All-++-⇔ xs ys) (to (All-++-⇔ xs ys) y) ≡ y
    from∘to y = {!   !}
    -- ^ why can't I case y, why can't I case xs?

    -- Why do I have to write ∀ {P} but not ∀ {P xs ys} ?

