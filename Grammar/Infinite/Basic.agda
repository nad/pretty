------------------------------------------------------------------------
-- "Basic" infinite grammars
------------------------------------------------------------------------

-- For a larger and more convenient, but equivalent, grammar
-- interface, see Grammar.Infinite.

module Grammar.Infinite.Basic where

open import Algebra
open import Coinduction
open import Data.Bool
open import Data.Char
open import Data.Empty
open import Data.List as List
open import Data.Product as Prod
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary

private module LM {A : Set} = Monoid (List.monoid A)

open import Utilities

------------------------------------------------------------------------
-- Simple, potentially infinite grammars

-- These grammars are very general. Every language that can be
-- recursively enumerated using an Agda function s : ℕ → List Char can
-- be expressed using one of these grammars:
-- ♯ ⟦ string (s 0) ⟧ ∣ ♯ (♯ ⟦ string (s 1) ⟧ ∣ …). (The string
-- combinator and ⟦_⟧ are defined in Grammar.Infinite. The empty
-- language can also be handled, see below.)
--
-- In practice one may want to restrict attention to, say, recursive
-- languages. I use general grammars to illustrate that this approach
-- to pretty-printing is not restricted to a small class of languages.

infixl 15 _>>=_
infixl 10 _∣_

data Grammar : Set → Set₁ where

  -- The empty string.

  return : ∀ {A} → A → Grammar A

  -- A single, arbitrary token.

  token  : Grammar Char

  -- Monadic sequencing.

  _>>=_  : ∀ {A B} → ∞ (Grammar A) → (A → ∞ (Grammar B)) → Grammar B

  -- Symmetric choice.

  _∣_    : ∀ {A} → ∞ (Grammar A) → ∞ (Grammar A) → Grammar A

-- Semantics of grammars (parse trees). Here x ∈ g ∙ s means that x
-- is one of the possible results of parsing the string s using the
-- grammar g.

infix 4 _∈_∙_

data _∈_∙_ : ∀ {A} → A → Grammar A → List Char → Set₁ where
  return-sem  : ∀ {A} {x : A} → x ∈ return x ∙ []
  token-sem   : ∀ {t} → t ∈ token ∙ [ t ]
  >>=-sem     : ∀ {A B x y s₁ s₂} {g₁ : ∞ (Grammar A)}
                  {g₂ : A → ∞ (Grammar B)} →
                x ∈ ♭ g₁ ∙ s₁ → y ∈ ♭ (g₂ x) ∙ s₂ →
                y ∈ g₁ >>= g₂ ∙ s₁ ++ s₂
  ∣-left-sem  : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
                x ∈ ♭ g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  ∣-right-sem : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
                x ∈ ♭ g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s

----------------------------------------------------------------------
-- Some grammar and semantics combinators

-- Cast lemma.

cast : ∀ {A} {g : Grammar A} {x s₁ s₂} →
       s₁ ≡ s₂ → x ∈ g ∙ s₁ → x ∈ g ∙ s₂
cast refl = id

-- Failure.

fail : ∀ {A} → Grammar A
fail = ♯ fail ∣ ♯ fail

fail-sem⁻¹ : ∀ {A} {x : A} {s} → ¬ (x ∈ fail {A = A} ∙ s)
fail-sem⁻¹ (∣-left-sem  ∈fail) = fail-sem⁻¹ ∈fail
fail-sem⁻¹ (∣-right-sem ∈fail) = fail-sem⁻¹ ∈fail

-- Map.

infixl 20 _<$>_

_<$>_ : ∀ {A B} → (A → B) → Grammar A → Grammar B
f <$> g = ♯ g >>= λ x → ♯ return (f x)

<$>-sem : ∀ {A B} {f : A → B} {g : Grammar A} {x s} →
          x ∈ g ∙ s → f x ∈ f <$> g ∙ s
<$>-sem x∈ =
  cast (proj₂ LM.identity _)
       (>>=-sem x∈ return-sem)

-- The empty string if the argument is true, otherwise failure.

if-true : Bool → Grammar ⊤
if-true true  = return tt
if-true false = fail

if-true-sem : tt ∈ if-true true ∙ []
if-true-sem = return-sem

if-true-sem⁻¹ : ∀ {b s} → tt ∈ if-true b ∙ s → T b × s ≡ []
if-true-sem⁻¹ {true}  return-sem = _ , refl
if-true-sem⁻¹ {false} ∈fail      = ⊥-elim (fail-sem⁻¹ ∈fail)

-- A token satisfying a given predicate.

sat : (p : Char → Bool) → Grammar Char
sat p = ♯ token >>= λ t → ♯ (const t <$> if-true (p t))

sat-sem : ∀ {p : Char → Bool} {t} → T (p t) →
          t ∈ sat p ∙ [ t ]
sat-sem {p} {t} pt = >>=-sem token-sem (<$>-sem lemma)
  where
  lemma : tt ∈ if-true (p t) ∙ []
  lemma with p t | pt
  lemma | true  | _  = if-true-sem
  lemma | false | ()

-- A specific token.

tok : Char → Grammar Char
tok t = sat (λ t′ → t ≟C t′)

tok-sem : ∀ {t} → t ∈ tok t ∙ [ t ]
tok-sem = sat-sem ≟C-refl

tok-sem⁻¹ : ∀ {t t′ s} → t′ ∈ tok t ∙ s → t ≡ t′ × s ≡ [ t ]
tok-sem⁻¹ (>>=-sem token-sem (>>=-sem t∈ return-sem)) =
  helper (Prod.map ≟C⇒≡ id (if-true-sem⁻¹ t∈))
  where
  helper : ∀ {t t′ s} →
           t ≡ t′ × s ≡ [] → t ≡ t′ × t′ ∷ s ++ [] ≡ [ t ]
  helper (refl , refl) = (refl , refl)
