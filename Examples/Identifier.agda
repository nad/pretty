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
open import Relation.Nullary

open import Grammar.Infinite as Grammar using (Grammar)
open import Pretty using (Doc; Pretty-printer)
open import Renderer
open import Utilities

-- Lower-case (ASCII) characters.

is-lower : Char → Bool
is-lower t = ('a' ≤?C t) ∧ (t ≤?C 'z')

-- A problematic attempt to define a grammar and a corresponding
-- pretty-printer for identifiers.

module Problematic where

  -- The grammar can be defined.

  identifier : Grammar (List⁺ Char)
  identifier = (proj₁ <$> sat is-lower) +
    where open Grammar

  -- However, it is impossible to define a corresponding
  -- pretty-printer.

  no-printer : ¬ Pretty-printer identifier
  no-printer identifier-printer = no-doc (identifier-printer [ 'A' ])
    where
    open Grammar

    lemma : ∀ {p : Char → Bool} {t s s′} →
            t ∷ s ∈ (proj₁ <$> sat p) + · s′ → T (p t)
    lemma (⊛-sem (<$>-sem (<$>-sem {x = _ , ok} _)) _) = ok

    no-doc : ¬ Doc identifier [ 'A' ]
    no-doc d = lemma (proj₂ (Renderer.string-exists d))

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
