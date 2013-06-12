------------------------------------------------------------------------
-- Identifiers
------------------------------------------------------------------------

module Examples.Identifier where

open import Coinduction
open import Data.Bool
open import Data.Char
open import Data.List.NonEmpty
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Grammar.Infinite as Grammar using (Grammar)
open import Pretty using (Pretty-printer)
open import Renderer
open import Utilities

-- Lower-case (ASCII) characters.

is-lower : Char → Bool
is-lower t = ('a' ≤?C t) ∧ (t ≤?C 'z')

-- Identifiers.

Identifier : Set
Identifier = List⁺ (∃ λ t → T (is-lower t))

identifier : Grammar Identifier
identifier = sat is-lower +
  where open Grammar

identifier-printer : Pretty-printer identifier
identifier-printer = map+ (λ _ → sat is-lower)
  where open Pretty

-- Identifiers possibly followed by whitespace.

identifier-w : Grammar Identifier
identifier-w = identifier <⊛ whitespace ⋆
  where open Grammar

identifier-w-printer : Pretty-printer identifier-w
identifier-w-printer n = identifier-printer n <⊛ nil-⋆
  where open Pretty

test : render 80 (identifier-w-printer (str⁺ "aaa")) ≡ "aaa"
test = refl
