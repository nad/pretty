------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

module Examples.Bool where

open import Codata.Musical.Notation
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Grammar.Infinite using (Grammar)
import Pretty
open import Renderer

module _ where

  open Grammar.Infinite

  bool : Grammar Bool
  bool = true  <$ string′ "true"
       ∣ false <$ string′ "false"

open Pretty

bool-printer : Pretty-printer bool
bool-printer true  = left  (<$ text)
bool-printer false = right (<$ text)

test₁ : render 4 (bool-printer true) ≡ "true"
test₁ = refl

test₂ : render 0 (bool-printer false) ≡ "false"
test₂ = refl
