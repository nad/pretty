------------------------------------------------------------------------
-- Bits
------------------------------------------------------------------------

module Examples.Bit where

open import Coinduction
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Grammar.Infinite
open import Pretty
open import Renderer

data Bit : Set where
  [0] [1] : Bit

bit : Grammar Bit
bit = [0] <$ symbol′ "0"
    ∣ [1] <$ symbol′ "1"

bit-printer : Pretty-printer bit
bit-printer [0] = ∣-left-doc  (<$-doc symbol-doc)
bit-printer [1] = ∣-right-doc (<$-doc symbol-doc)

test₁ : render 4 (bit-printer [0]) ≡ "0"
test₁ = refl

test₂ : render 0 (bit-printer [1]) ≡ "1"
test₂ = refl
