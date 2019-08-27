------------------------------------------------------------------------
-- Various utility functions
------------------------------------------------------------------------

module Utilities where

open import Data.Bool
open import Data.Bool.Properties using (T-∧)
open import Data.Char
import Data.Char.Properties as Char
open import Data.List
open import Data.List.NonEmpty as List⁺
open import Data.Nat
import Data.Nat.Properties as NP
open import Data.Product
open import Data.String as String using (String)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using () renaming (module Equivalence to Eq)
open import Relation.Binary
import Relation.Binary.Properties.StrictTotalOrder as STO
open import Relation.Nullary.Decidable

------------------------------------------------------------------------
-- Some comparison operators

-- Is one number strictly smaller than another?

_<?ℕ_ : ℕ → ℕ → Bool
n₁ <?ℕ n₂ = ⌊ n₁ NP.<? n₂ ⌋

-- Is one character smaller than or equal to another?

_≤?C_ : Char → Char → Bool
c₁ ≤?C c₂ = ⌊ DecTotalOrder._≤?_
                (STO.decTotalOrder Char.<-strictTotalOrder-≈)
                c₁ c₂ ⌋

------------------------------------------------------------------------
-- Conversion of strings satisfying given predicates to annotated
-- lists

private
  mutual

    str′ : {p : Char → Bool}
           (s : List Char) → T (all p s) → List (∃ (T ∘ p))
    str′ []       _  = []
    str′ (t ∷ ts) ok = List⁺.toList (str⁺′ (t ∷ ts) ok)

    str⁺′ : {p : Char → Bool}
            (s : List⁺ Char) → T (all p (List⁺.toList s)) →
            List⁺ (∃ (T ∘ p))
    str⁺′ (t ∷ ts) ok =
      let (ok₁ , ok₂) = Eq.to T-∧ ⟨$⟩ ok in
      (t , ok₁) ∷ str′ ts ok₂

str : {p : Char → Bool}
      (s : String)
      {ok : T (all p $ String.toList s)} →
      List (∃ (T ∘ p))
str s {ok} = str′ (String.toList s) ok

str⁺ : {p : Char → Bool}
       (s : String)
       {ok₁ : T (all p $ String.toList s)}
       {ok₂ : T (not $ null $ String.toList s)} →
       List⁺ (∃ (T ∘ p))
str⁺ s {ok₂ = _} with String.toList s
str⁺ s {ok₂ = ()} | []
str⁺ s {ok₁ = ok} | c ∷ cs = str⁺′ (c ∷ cs) ok
