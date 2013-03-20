------------------------------------------------------------------------
-- Lists of names
------------------------------------------------------------------------

-- This example is based on one in Swierstra and Chitil's "Linear,
-- bounded, functional pretty-printing".

module Examples.Name-list where

open import Coinduction
open import Data.List
import Data.List.NonEmpty as List⁺
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Examples.Name
open import Grammar.Infinite as Grammar using (Grammar)
open import Pretty using (Pretty-printer)
open import Renderer
open import Utilities

name-list-body : Grammar (List Name)
name-list-body =
    return []
  ∣ List⁺.toList <$> (name-w sep-by symbol′ ",")
  where open Grammar

name-list : Grammar (List Name)
name-list = symbol′ "[" ⊛> name-list-body <⊛ symbol′ "]"
  where open Grammar

open Pretty

name-list-printer : Pretty-printer name-list
name-list-printer ns = symbol ⊛> body ns <⊛ symbol
  where
  body : Pretty-printer name-list-body
  body []       = left nil
  body (n ∷ ns) =
    right (<$> (<$> name-w-printer n
                  ⊛
                map⋆ (λ n → group symbol-line ⊛> name-w-printer n) ns))

names : List Name
names = str "aaa" ∷ str "bbbbb" ∷ str "ccc" ∷
        str "dd" ∷ str "eee" ∷ []

test₁ : render 80 (name-list-printer names) ≡
        "[aaa, bbbbb, ccc, dd, eee]"
test₁ = refl

test₂ : render 11 (name-list-printer names) ≡
        "[aaa,\nbbbbb, ccc,\ndd, eee]"
test₂ = refl

test₃ : render 8 (name-list-printer names) ≡
        "[aaa,\nbbbbb,\nccc, dd,\neee]"
test₃ = refl
