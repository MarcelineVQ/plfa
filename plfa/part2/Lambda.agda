module plfa.part2.Lambda where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl;cong)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
open import plfa.part1.Isomorphism
open import Data.Product using (_×_; ∃; ∃-syntax;proj₁;proj₂) renaming (_,_ to ⟨_,_⟩)

Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_



data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

-- "the number n is represented by a function that accepts two arguments and applies the first n times to the second"
-- for plusᶜ what is happening is s is applied to z 'n' times, s is applied to n s z m times.
plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
        ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

-- how do I check if my mul is correct?
mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ `zero
           |suc "m" ⇒ plus · ` "n" · (` "*" · `"m" · `"n") ]

-- confirmed this in ghci since we've not got a method to confirm
-- it in agda at this point in the text
-- (\m n s z -> (n (m s)) z)     -- m * n: m suc's done n times
-- (\s z -> s (s (s z)))         -- 3
-- (\s z -> s (s (s (s (s z))))) -- 5
-- (+1) 0                        -- `suc and `zero
-- 15
mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
       ` "n" · (` "m"  · ` "s") · ` "z"


-- gross, making the meta languaged untyped as well
ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
ƛ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
μ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
         case′ m
           [zero⇒ `zero
           |suc m ⇒ plus′ · n · (* · m · n) ]
  where
  * = ` "*"
  m = ` "m"
  n = ` "n"

data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _          =  V
... | no  _          =  ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  ƛ x ⇒ N
... | no  _          =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]   =  L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]   =  `zero
(`suc M) [ y := V ]  =  `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  μ x ⇒ N
... | no  _          =  μ x ⇒ N [ y := V ]

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

-- I prefer mutual to forward declaration, hopefully it doesn't
-- have any issues.
mutual
  infix 9 _[_:=_]′

  _[_:=_]′ : Term → Id → Term → Term
  (` x) [ y := V ]′ with x ≟ y
  ... | yes _          =  V
  ... | no  _          =  ` x
  (L · M) [ y := V ]′   =  L [ y := V ]′ · M [ y := V ]′
  (`zero) [ y := V ]′   =  `zero
  (`suc M) [ y := V ]′  =  `suc M [ y := V ]′
  (ƛ x ⇒ N) [ y := V ]′ = bound-subst x N ƛ_⇒_ y V
  (case L [zero⇒ M |suc x ⇒ N ]) [ y := V ]′ = bound-subst x N (case_[zero⇒_|suc_⇒_] (L [ y := V ]′) (M [ y := V ]′)) y V
  (μ x ⇒ N) [ y := V ]′ = bound-subst x N μ_⇒_ y V

  bound-subst : Id → Term → (Id → Term → Term) → Id → Term → Term
  bound-subst x N cons y V with x ≟ y
  ... | yes p = cons x N
  ... | no ¬p = cons x (N [ y := V ]′ )

-- _[_:=_]′ tests
_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]′ ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ]′ ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ]′ ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ]′ ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ]′ ≡ ƛ "y" ⇒ ` "y"
_ = refl

infix 4 _—→_

data _—→_ : Term → Term → Set where
  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
    → L · M —→ L′ · M
  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
    → V · M —→ V · M′
  β-ƛ : ∀ {x N V}
    → Value V
    → (ƛ x ⇒ N) · V —→ N [ x := V ]
  ξ-suc : ∀ {M M′}
    → M —→ M′
    → `suc M —→ `suc M′
  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]
  β-zero : ∀ {x M N}
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M
  β-suc : ∀ {x V M N}
    → Value V
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]
  β-μ : ∀ {x M}
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

infix 2 _—↠_
infix 1 begin_
infixr 2 _—→⟨_⟩_
infix 3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
    → M —↠ M

  _—→⟨_⟩_ : ∀ {M N} L
    → L —→ M
    → M —↠ N
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
  → M —↠ N
begin M—↠N = M—↠N

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

—↠≲—↠′ : ∀ {L M} → L —↠ M ≲ L —↠′ M
—↠≲—↠′ {L} {M} =
  record
    { to = to
    ; from = from
    ; from∘to = from∘to
    }
  where

    to : ∀ {L M} → L —↠ M → L —↠′ M
    to (M ∎) = refl′
    to (L —→⟨ L—→M1 ⟩ M1—↠M2) = trans′ (step′ L—→M1) (to M1—↠M2)

    -- how did Zambonifofex determine he needed 3 types here :(
    -- it's obvious once you start pattern matching and have
    -- holes but you need types written before that
    -- further, why is this N —↠′ L → N —↠ M and not N —↠′ L → N —↠ L
    traverse : ∀ {L M N} → L —↠ M → N —↠′ L → N —↠ M
    traverse acc (step′ x) = _ —→⟨ x ⟩ acc
    traverse acc refl′ = acc
    traverse acc (trans′ x y) = traverse (traverse acc y) x

    from : ∀ {L M} → L —↠′ M → L —↠ M
    from {L} {M} t = traverse (M ∎) t

    from∘to : ∀ {L M} → (x : L —↠ M) → from (to x) ≡ x
    from∘to (M ∎) = refl
    from∘to (L —→⟨ x ⟩ t) = cong (L —→⟨ x ⟩_) (from∘to t)

---------

{-

-- The book doesn't ask us to implement these but I thought I'd try
-- but, uh, I don't see how there's any P that satisfies
-- arbitrary M and N to specific P.

confluence : ∀ {L M N} → ∃[ P ]
  ( ((L —↠ M) × (L —↠ N))
    --------------------
  → ((M —↠ P) × (N —↠ P)) )
confluence {L} {M} {N} = record { fst = N ; snd = snd' }
  where
    snd' : (L —↠ M) × (L —↠ N) → (M —↠ N) × (N —↠ N)
    snd' ⟨ L ∎ , .L ∎ ⟩ = {!   !}
    snd' ⟨ L ∎ , .L —→⟨ x ⟩ snd ⟩ = {!   !}
    snd' ⟨ L —→⟨ x ⟩ fst , .L ∎ ⟩ = {! -d -t 5  !}
    snd' ⟨ L —→⟨ x ⟩ fst , .L —→⟨ x₁ ⟩ snd ⟩ = {!   !}

diamond : ∀ {L M N} → ∃[ P ]
  ( ((L —→ M) × (L —→ N))
    --------------------
  → ((M —↠ P) × (N —↠ P)) )
proj₁ diamond = `zero
proj₂ diamond ⟨ fst , snd ⟩ = ⟨ {!   !} , {!   !} ⟩

-- are these provable in agda?
deterministic : ∀ {L M N}
  → L —→ M
  → L —→ N
    ------
  → M ≡ N
deterministic x y = {!   !}

-}

{-
"It is easy to show that every deterministic relation satisfies the diamond property, and that every relation that satisfies the diamond property is confluent. Hence, all the reduction systems studied in this text are trivially confluent."
-}
-- Whoever wrote this book has a far far different idea of what
-- the word easy means. I don't even see how to show these
-- properties exist for our Term type in the first place.


-- This is the example given for 2 + 2 = 4
-- There is no way I'm writing 1 + 1 = 2 by hand
-- Just look at these fucking moonrunes.
_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
      case two [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
         · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
      case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case `suc `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc `suc (plus · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎



infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

module Context-≃ where
  open _≃_
  
  Context-≃ : Context ≃ List (Id × Type)
  to Context-≃ ∅ = []
  to Context-≃ (c , id ⦂ ty) = ⟨ id , ty ⟩ ∷ to Context-≃ c
  from Context-≃ [] = ∅
  from Context-≃ (⟨ id , ty ⟩ ∷ c) = from Context-≃ c , id ⦂ ty
  from∘to Context-≃ ∅ = refl
  from∘to Context-≃ (c , id ⦂ ty) = cong (_, id ⦂ ty) (from∘to Context-≃ c)
  to∘from Context-≃ [] = refl
  to∘from Context-≃ (⟨ id , ty ⟩ ∷ c) = cong (⟨ id , ty ⟩ ∷_)   (to∘from Context-≃ c)


infix  4  _∋_⦂_

-- context lookup
data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A
-- I don't understand the purpose of the x ≢ y
-- The text says "If two variables in a context have the same
-- name, then lookup should return the most recently bound
-- variable, which shadows the other variables. "
-- So why are we preventing shadowing with the S constructor?

-- Additionaly the text says
-- "Constructor S takes an additional parameter, which ensures
-- that when we look up a variable that it is not shadowed by
-- another variable with the same name to its left in the list."
-- But isn't it the right that 'shadows'? As a snoclist the right
-- is the newest addition and thus the 'most recently bound',
-- isn't it?
-- why does it matter that a variable "is not shadowed by
-- another variable with the same name to its left"

infix  4  _⊢_⦂_

-- Type Derivation
data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I 
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A

-- Text says "The entire process can be automated using Agsy, invoked with C-c C-a."
-- Which can often work but seems to be untrue for this case, agda reports:
-- Not implemented: The Agda synthesizer (Agsy) does not support literals yet
-- What literal is it referring to?
⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

-- lookup is injective, as a consequence of our x ≢ y for ∋
-- why is this important if we're supposed to have a context
-- which allows shadowing?
∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z        Z          =  refl
∋-injective Z        (S x≢ _)   =  ⊥-elim (x≢ refl)
∋-injective (S x≢ _) Z          =  ⊥-elim (x≢ refl)
∋-injective (S _ ∋x) (S _ ∋x′)  =  ∋-injective ∋x ∋x′

-- How did they write this? How do I write this myself?
nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)

-- ^ you can write
-- nope₁ x = {! !}          -- then case on x
-- nope₁ (c · c₁) = {!   !} -- then case on c
-- nope₁ (() · c₁)

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′))  =  contradiction (∋-injective ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()

nope₂' : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂' (⊢ƛ (⊢` Z · ⊢` (S _ ())))

-- Task: For each of the following, give a type A for which it is
-- derivable, or explain why there is no such A.
-- What does derivable mean?
-- To create a type derivation?
-- This is quite hard, up until now we've just been writing pieces
-- now we have to understand how the connect.

-- It couldn't be clearer that A is `ℕ here, how can I show
-- this to agda. It should be mechanical.
-- ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ A
-- added parens because this is very hard to parse mentally
--                Context                 Term          Type
der₁ : (∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ) ⊢ (` "y" · ` "x") ⦂ (`ℕ)
der₁ = ⊢` (S (λ ()) Z {- 1 -}) ·  ⊢` Z {- 2 -}
-- {- 1 -} oddly, agda could not fill in this Z with C-c C-r
-- probably due to the right side of · not being filled in.
-- {- 2 -} this also was not able to be filled in with C-c C-r
-- since it had a choice of S or Z, despite Z being the clear fit.


-- Pretty clearly not derivable based on the types.
-- ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A
der₂ : ∀ {A} → ¬ (∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A)
der₂ (⊢` (S _ (S _ ())) · _)

-- ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ A
der₃ : ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ `ℕ ⇒ `ℕ
der₃ = ⊢ƛ ((⊢` (S (λ ()) Z)) · ⊢` Z)

-- ^ These are very good exercises for understanding the material.


-- Task: For each of the following, give types A, B, and C for
-- which it is derivable, or explain why there are no such types.

-- Cannot, there's no way to ` "x" · ` "x" with any single type.
-- You would need ` "x" of some polymorphic type so that the
-- first occurence of ` "x" was A ⇒ A, and the second could be
-- (A ⇒ A) ⇒ (A ⇒ A)
-- ∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B
-- der₄ : ∀ {A} → ∅ , "x" ⦂ (A ⇒ A) ⊢ ` "x" · ` "x" ⦂ (A ⇒ A)
-- der₄ = {! !}

-- A : `ℕ ⇒ `ℕ
-- B : `ℕ ⇒ `ℕ
-- C : `ℕ ⇒ `ℕ
-- ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ C
der₅ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ `ℕ ⇒ `ℕ
der₅ = ⊢ƛ (⊢` (S (λ ()) (S ((λ ())) Z))
        · ((⊢` (S ((λ ())) Z)) · ⊢` Z))


-- uh, wow, don't want to do too many of these by hand
-- used `ℕ just to keep sig simple
⊢mul₁ : ∅ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul₁ = ⊢μ (⊢ƛ (⊢ƛ (
  ⊢case
    (⊢` (S (λ ()) Z))
    ⊢zero
    (((⊢μ (⊢ƛ (⊢ƛ (⊢case
                    (⊢` (S (λ ()) Z))
                    (⊢` Z)
                    (⊢suc ((⊢` (S (λ ()) (S (λ ()) (S (λ ()) Z))))
                      · (⊢` Z)
                      · (⊢` (S (λ ()) Z))))))))
      · ⊢` (S (λ ()) Z))
      · ((⊢` (S (λ ()) (S (λ ()) (S (λ ()) Z))))
         · ⊢` Z
         · ⊢` (S (λ ()) Z))))))

⊢mulᶜ : ∅ ⊢ mulᶜ ⦂ ((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ)) ⇒ ((`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
⊢mulᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (((⊢` (S (λ ()) (S (λ ()) Z)))
                          · (⊢` (S (λ ()) (S (λ ()) (S (λ ()) Z)))
                              · ⊢` (S (λ ()) Z)))
                     · ⊢` Z))))
-- generalized sig
⊢mulᶜᵍ : ∀ {A B C D E F} → ∅ ⊢ mulᶜ ⦂ ((A ⇒ B) ⇒ (C ⇒ D)) ⇒ ((C ⇒ D) ⇒ E ⇒ F) ⇒ (A ⇒ B) ⇒ E ⇒ F
⊢mulᶜᵍ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (((⊢` (S (λ ()) (S (λ ()) Z)))
                          · (⊢` (S (λ ()) (S (λ ()) (S (λ ()) Z)))
                              · ⊢` (S (λ ()) Z)))
                     · ⊢` Z))))




