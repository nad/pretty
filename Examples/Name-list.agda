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
open import Grammar.Infinite
open import Pretty
open import Renderer
open import Utilities

name-list-body : Grammar (List Name)
name-list-body =
    return []
  ∣ List⁺.toList <$> (name-w sep-by symbol′ ",")

name-list : Grammar (List Name)
name-list = symbol′ "[" ⊛> name-list-body <⊛ symbol′ "]"

name-list-printer : Pretty-printer name-list
name-list-printer ns = symbol-doc ⊛>-doc body ns <⊛-doc symbol-doc
  where
  body : Pretty-printer name-list-body
  body []       = ∣-left-doc nil
  body (n ∷ ns) =
    ∣-right-doc
      (<$>-doc
         (<$>-doc (name-w-printer n)
            ⊛-doc
          map⋆-doc (λ n → group symbol-line-doc
                            ⊛>-doc
                          name-w-printer n)
                   ns))

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
