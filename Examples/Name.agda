------------------------------------------------------------------------
-- "Names"
------------------------------------------------------------------------

module Examples.Name where

open import Coinduction
open import Data.Bool
open import Data.Char
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Grammar.Infinite as Grammar using (Grammar)
open import Pretty using (Pretty-printer)
open import Renderer
open import Utilities

-- "Name characters".

is-name-char : Char → Bool
is-name-char t =
  ('A' ≤?C t) ∧ (t ≤?C 'Z')
    ∨
  ('a' ≤?C t) ∧ (t ≤?C 'z')
    ∨
  ('0' ≤?C t) ∧ (t ≤?C '9')
    ∨
  (t == ':')
    ∨
  (t == '.')
    ∨
  (t == '/')

Name-char : Set
Name-char = ∃ λ (t : Char) → T (is-name-char t)

name-char : Grammar Name-char
name-char = sat _
  where open Grammar

name-char-printer : Pretty-printer name-char
name-char-printer _ = sat
  where open Pretty

-- Note that if we had defined Name-char = Char, then it
-- wouldn't have been possible to define name-char-printer.

-- Names. Note that names are allowed to be empty.

Name : Set
Name = List Name-char

name : Grammar Name
name = name-char ⋆
  where open Grammar

name-printer : Pretty-printer name
name-printer = map⋆ name-char-printer
  where open Pretty

-- Names possibly followed by whitespace.

name-w : Grammar Name
name-w = name <⊛ whitespace ⋆
  where open Grammar

name-w-printer : Pretty-printer name-w
name-w-printer n = name-printer n <⊛ nil-⋆
  where open Pretty

test : render 80 (name-w-printer (str "aaa")) ≡ "aaa"
test = refl
