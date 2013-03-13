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
open import Data.Product
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
import Function.Related as Related
import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
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

fail-sem⁻¹ : ∀ {A} {x : A} {s} → ¬ (x ∈ fail ∙ s)
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

if-true-sem : ∀ {b s} → tt ∈ if-true b ∙ s ↔ (T b × s ≡ [])
if-true-sem = record
  { to         = P.→-to-⟶ (to _)
  ; from       = P.→-to-⟶ (from _)
  ; inverse-of = record
    { left-inverse-of  = from∘to _
    ; right-inverse-of = to∘from _
    }
  }
  where
  to : ∀ b {s} → tt ∈ if-true b ∙ s → T b × s ≡ []
  to true  return-sem = _ , refl
  to false ∈fail      = ⊥-elim $ fail-sem⁻¹ ∈fail

  from : ∀ b {s} → T b × s ≡ [] → tt ∈ if-true b ∙ s
  from true  (_  , refl) = return-sem
  from false (() , refl)

  from∘to : ∀ b {s} (tt∈ : tt ∈ if-true b ∙ s) → from b (to b tt∈) ≡ tt∈
  from∘to true  return-sem = refl
  from∘to false ∈fail      = ⊥-elim $ fail-sem⁻¹ ∈fail

  to∘from : ∀ b {s} (eqs : T b × s ≡ []) → to b (from b eqs) ≡ eqs
  to∘from true  (_  , refl) = refl
  to∘from false (() , refl)

-- A token satisfying a given predicate.

sat : (p : Char → Bool) → Grammar Char
sat p = ♯ token >>= λ t → ♯ (const t <$> if-true (p t))

sat-sem : ∀ {p : Char → Bool} {t s} →
          t ∈ sat p ∙ s ↔ (T (p t) × s ≡ [ t ])
sat-sem {p} {t} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
  to : ∀ {s} → t ∈ sat p ∙ s → T (p t) × s ≡ [ t ]
  to (>>=-sem token-sem (>>=-sem tt∈ return-sem)) =
    proj₁ lemma , P.cong (λ s → t ∷ s ++ []) (proj₂ lemma)
    where lemma = Inverse.to if-true-sem ⟨$⟩ tt∈

  from : ∀ {s} → T (p t) × s ≡ [ t ] → t ∈ sat p ∙ s
  from (pt , refl) =
    >>=-sem token-sem
            (>>=-sem (Inverse.from if-true-sem ⟨$⟩ (pt , refl))
                     return-sem)

  from∘to : ∀ {s} (t∈ : t ∈ sat p ∙ s) → from (to t∈) ≡ t∈
  from∘to (>>=-sem token-sem (>>=-sem {s₂ = []} tt∈ return-sem))
    with Inverse.to if-true-sem ⟨$⟩ tt∈
       | Inverse.left-inverse-of if-true-sem tt∈
  from∘to (>>=-sem token-sem
             (>>=-sem {x = tt} {s₂ = []}
                      .(Inverse.from if-true-sem ⟨$⟩ (pt , refl))
                      return-sem))
    | (pt , refl) | refl = refl

  to∘from : ∀ {s} (eqs : T (p t) × s ≡ [ t ]) → to (from eqs) ≡ eqs
  to∘from (pt , refl)
    rewrite Inverse.right-inverse-of if-true-sem (pt , refl)
    = refl

-- A specific token.

tok : Char → Grammar Char
tok t = sat (λ t′ → t ≟C t′)

tok-sem : ∀ {t′ t s} → t′ ∈ tok t ∙ s ↔ (t ≡ t′ × s ≡ [ t ])
tok-sem {t′} {t} {s} =
  t′ ∈ tok t ∙ s              ↔⟨ sat-sem ⟩
  (T (t ≟C t′) × s ≡ [ t′ ])  ↔⟨ Inv.sym $
                                   Σ.cong (Inv.sym ≟C↔≡) (λ {t≡t′} →
                                     P.subst (λ t′ → s ≡ [ t ] ↔ s ≡ [ t′ ]) t≡t′ Inv.id) ⟩
  (t ≡ t′ × s ≡ [ t ])        ∎
  where open Related.EquationalReasoning
