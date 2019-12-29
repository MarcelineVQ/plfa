module plfa.part2.Lambda where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl;cong)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
open import plfa.part1.Isomorphism

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







