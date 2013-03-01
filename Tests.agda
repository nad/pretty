------------------------------------------------------------------------
-- Some boolean-valued operators (equality, less than, …)
------------------------------------------------------------------------

module Tests where

open import Data.Bool
open import Data.Char as Char
open import Data.Empty
open import Data.Nat as Nat
open import Data.Unit
open import Relation.Binary
import Relation.Binary.Props.DecTotalOrder as DTO
import Relation.Binary.Props.StrictTotalOrder as STO
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary
open import Relation.Nullary.Decidable

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
