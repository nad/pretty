------------------------------------------------------------------------
-- Lists of identifiers
------------------------------------------------------------------------

-- This example is based on one in Swierstra and Chitil's "Linear,
-- bounded, functional pretty-printing".

{-# OPTIONS --guardedness #-}

module Examples.Identifier-list where

open import Codata.Musical.Notation
open import Data.List
import Data.List.NonEmpty as List⁺
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Examples.Identifier
open import Grammar.Infinite as Grammar
  using (Grammar) hiding (module Grammar)
open import Pretty using (Pretty-printer)
open import Renderer
open import Utilities

identifier-list-body : Grammar (List Identifier)
identifier-list-body =
    return []
  ∣ List⁺.toList <$> (identifier-w sep-by symbol′ ",")
  where open Grammar

identifier-list : Grammar (List Identifier)
identifier-list = symbol′ "[" ⊛> identifier-list-body <⊛ symbol′ "]"
  where open Grammar

open Pretty

identifier-list-printer : Pretty-printer identifier-list
identifier-list-printer ns = symbol ⊛> body ns <⊛ symbol
  where
  body : Pretty-printer identifier-list-body
  body []       = left nil
  body (n ∷ ns) =
    right (<$> (<$> identifier-w-printer n
                  ⊛
                map⋆ (λ n → group symbol-line ⊛>
                            identifier-w-printer n)
                     ns))

identifiers : List Identifier
identifiers = str⁺ "aaa" ∷ str⁺ "bbbbb" ∷ str⁺ "ccc" ∷
              str⁺ "dd" ∷ str⁺ "eee" ∷ []

test₁ : render 80 (identifier-list-printer identifiers) ≡
        "[aaa, bbbbb, ccc, dd, eee]"
test₁ = refl

test₂ : render 11 (identifier-list-printer identifiers) ≡
        "[aaa,\nbbbbb, ccc,\ndd, eee]"
test₂ = refl

test₃ : render 8 (identifier-list-printer identifiers) ≡
        "[aaa,\nbbbbb,\nccc, dd,\neee]"
test₃ = refl
