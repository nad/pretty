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

open import Grammar.Infinite
open import Pretty
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
  (t ≟C ':')
    ∨
  (t ≟C '.')
    ∨
  (t ≟C '/')

Name-char : Set
Name-char = ∃ λ (t : Char) → T (is-name-char t)

name-char : Grammar Name-char
name-char = sat _

name-char-printer : Pretty-printer name-char
name-char-printer _ = sat-doc

-- Note that if we had defined Name-char = Char, then it
-- wouldn't have been possible to define name-char-printer.

-- Names. Note that names are allowed to be empty.

Name : Set
Name = List Name-char

name : Grammar Name
name = name-char ⋆

name-printer : Pretty-printer name
name-printer = map⋆-doc name-char-printer

-- Names possibly followed by whitespace.

name-w : Grammar Name
name-w = name <⊛ whitespace ⋆

name-w-printer : Pretty-printer name-w
name-w-printer n = name-printer n <⊛-doc []-doc

test : render 80 (name-w-printer (str "aaa")) ≡ "aaa"
test = refl
