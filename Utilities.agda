------------------------------------------------------------------------
-- Various utility functions
------------------------------------------------------------------------

module Utilities where

open import Data.Bool
open import Data.Bool.Properties using (T-∧)
open import Data.Char as Char
open import Data.Empty
open import Data.List
open import Data.Nat as Nat
open import Data.Product
open import Data.String as String using (String)
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using () renaming (module Equivalence to Eq)
open import Relation.Binary
import Relation.Binary.Props.DecTotalOrder as DTO
import Relation.Binary.Props.StrictTotalOrder as STO
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary
open import Relation.Nullary.Decidable

------------------------------------------------------------------------
-- Some boolean-valued operators (equality, less than, …)

-- Is one number strictly smaller than another?

_<?ℕ_ : ℕ → ℕ → Bool
n₁ <?ℕ n₂ = ⌊ StrictTotalOrder._<?_
                (DTO.strictTotalOrder Nat.decTotalOrder)
                n₁ n₂ ⌋

-- Is one character smaller than or equal to another?

_≤?C_ : Char → Char → Bool
c₁ ≤?C c₂ = ⌊ DecTotalOrder._≤?_
                (STO.decTotalOrder Char.strictTotalOrder)
                c₁ c₂ ⌋

-- Is one character equal to another?

_≟C_ : Char → Char → Bool
c₁ ≟C c₂ = ⌊ c₁ Char.≟ c₂ ⌋

-- Some lemmas related to _≟C_.

≟C-refl : ∀ {c} → T (c ≟C c)
≟C-refl {c} with c Char.≟ c
... | yes refl = tt
... | no  c≢c  = ⊥-elim (c≢c refl)

≟C⇒≡ : ∀ {c c′} → T (c ≟C c′) → c ≡ c′
≟C⇒≡ = toWitness

------------------------------------------------------------------------
-- Converts strings satisfying a given predicate to annotated lists

str : {p : Char → Bool}
      (s : String)
      {ok : T (all p $ String.toList s)} →
      List (∃ (T ∘ p))
str {p} s {ok} = str′ (String.toList s) {ok}
  where
  str′ : (s : List Char) {ok : T (all p s)} → List (∃ (T ∘ p))
  str′ []            = []
  str′ (t ∷ ts) {ok} =
    let (ok₁ , ok₂) = Eq.to T-∧ ⟨$⟩ ok in
    (t , ok₁) ∷ str′ ts {ok₂}
