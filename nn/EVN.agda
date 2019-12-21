module nn.EVN where

open import Data.Nat

-- data Vector (A : Set) : Set where
--   [] : Vector a
--   ,_ : (a : A) -> Vector a
--   _,_ : (a : A) → Vector a → Vector a



-- evolvable nerual unit
record ENU : Set where
  field
    inputChannels : ℕ
    ouputChannels : ℕ
    -- resetGate : tt

