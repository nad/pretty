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
open import Data.Sum as Sum
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
import Function.Related as Related
import Function.Related.TypeIsomorphisms as Iso
open import Relation.Binary.Product.Pointwise using (_×-cong_)
import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Nullary

private module LM {A : Set} = Monoid (List.monoid A)
open Related.EquationalReasoning

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

return-sem′ : ∀ {A} {x y : A} {s} → x ∈ return y ∙ s ↔ (x ≡ y × s ≡ [])
return-sem′ {A} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
  to : ∀ {x y : A} {s} → x ∈ return y ∙ s → x ≡ y × s ≡ []
  to return-sem = (refl , refl)

  from : ∀ {x y : A} {s} → x ≡ y × s ≡ [] → x ∈ return y ∙ s
  from (refl , refl) = return-sem

  from∘to : ∀ {x y : A} {s} (x∈ : x ∈ return y ∙ s) → from (to x∈) ≡ x∈
  from∘to return-sem = refl

  to∘from : ∀ {x y : A} {s} (eqs : x ≡ y × s ≡ []) → to (from eqs) ≡ eqs
  to∘from (refl , refl) = refl

token-sem′ : ∀ {t s} → t ∈ token ∙ s ↔ s ≡ [ t ]
token-sem′ = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
  to : ∀ {t s} → t ∈ token ∙ s → s ≡ [ t ]
  to token-sem = refl

  from : ∀ {t s} → s ≡ [ t ] → t ∈ token ∙ s
  from refl = token-sem

  from∘to : ∀ {t s} (x∈ : t ∈ token ∙ s) → from (to x∈) ≡ x∈
  from∘to token-sem = refl

  to∘from : ∀ {t s} (eq : s ≡ [ t ]) → to (from eq) ≡ eq
  to∘from refl = refl

>>=-sem′ : ∀ {A B y s} {g₁ : ∞ (Grammar A)} {g₂ : A → ∞ (Grammar B)} →
           y ∈ g₁ >>= g₂ ∙ s ↔
           ∃₂ λ s₁ s₂ → ∃ λ x →
              s ≡ s₁ ++ s₂ × x ∈ ♭ g₁ ∙ s₁ × y ∈ ♭ (g₂ x) ∙ s₂
>>=-sem′ {B = B} {g₁ = g₁} {g₂} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
  RHS : B → List Char → Set₁
  RHS y s = ∃₂ λ s₁ s₂ → ∃ λ x →
               s ≡ s₁ ++ s₂ × x ∈ ♭ g₁ ∙ s₁ × y ∈ ♭ (g₂ x) ∙ s₂

  to : ∀ {y s} → y ∈ g₁ >>= g₂ ∙ s → RHS y s
  to (>>=-sem x∈ y∈) = _ , _ , _ , refl , x∈ , y∈

  from : ∀ {y s} → RHS y s → y ∈ g₁ >>= g₂ ∙ s
  from (_ , _ , _ , refl , x∈ , y∈) = >>=-sem x∈ y∈

  from∘to : ∀ {y s} (x∈ : y ∈ g₁ >>= g₂ ∙ s) → from (to x∈) ≡ x∈
  from∘to (>>=-sem x∈ y∈) = refl

  to∘from : ∀ {y s} (rhs : RHS y s) → to (from rhs) ≡ rhs
  to∘from (_ , _ , _ , refl , x∈ , y∈) = refl

∣-sem′ : ∀ {A x s} {g₁ g₂ : ∞ (Grammar A)} →
         x ∈ g₁ ∣ g₂ ∙ s ↔ (x ∈ ♭ g₁ ∙ s ⊎ x ∈ ♭ g₂ ∙ s)
∣-sem′ {g₁ = g₁} {g₂} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
  to : ∀ {x s} → x ∈ g₁ ∣ g₂ ∙ s → x ∈ ♭ g₁ ∙ s ⊎ x ∈ ♭ g₂ ∙ s
  to (∣-left-sem  x∈) = inj₁ x∈
  to (∣-right-sem x∈) = inj₂ x∈

  from : ∀ {x s} → x ∈ ♭ g₁ ∙ s ⊎ x ∈ ♭ g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  from = Sum.[ ∣-left-sem , ∣-right-sem ]

  from∘to : ∀ {x s} (x∈ : x ∈ g₁ ∣ g₂ ∙ s) → from (to x∈) ≡ x∈
  from∘to (∣-left-sem  x∈) = refl
  from∘to (∣-right-sem x∈) = refl

  to∘from : ∀ {x s} (x∈ : x ∈ ♭ g₁ ∙ s ⊎ x ∈ ♭ g₂ ∙ s) →
            to (from x∈) ≡ x∈
  to∘from = Sum.[ (λ _ → refl) , (λ _ → refl) ]

----------------------------------------------------------------------
-- Some grammar and semantics combinators

-- Cast lemma.

cast : ∀ {A} {g : Grammar A} {x s₁ s₂} →
       s₁ ≡ s₂ → x ∈ g ∙ s₁ → x ∈ g ∙ s₂
cast refl = id

-- Failure.

fail : ∀ {A} → Grammar A
fail = ♯ fail ∣ ♯ fail

fail-sem : ∀ {A} {x : A} {s} → x ∈ fail ∙ s ↔ ⊥
fail-sem {x = x} {s} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ (λ ())
  ; inverse-of = record
    { left-inverse-of  = ⊥-elim ∘ to
    ; right-inverse-of = λ ()
    }
  }
  where
  to : x ∈ fail ∙ s → ⊥
  to (∣-left-sem  ∈fail) = to ∈fail
  to (∣-right-sem ∈fail) = to ∈fail

-- Map.

infixl 20 _<$>_

_<$>_ : ∀ {A B} → (A → B) → Grammar A → Grammar B
f <$> g = ♯ g >>= λ x → ♯ return (f x)

<$>-sem : ∀ {A B} {f : A → B} {g : Grammar A} {y s} →
          y ∈ f <$> g ∙ s ↔ ∃ λ x → x ∈ g ∙ s × y ≡ f x
<$>-sem {f = f} {g} {y} {s} =
  y ∈ f <$> g ∙ s                                         ↔⟨ >>=-sem′ ⟩
  (∃₂ λ s₁ s₂ → ∃ λ x →
      s ≡ s₁ ++ s₂ × x ∈ g ∙ s₁ × y ∈ return (f x) ∙ s₂)  ↔⟨ Σ.cong Inv.id (Σ.cong Inv.id (Σ.cong Inv.id
                                                               (Inv.id ×-cong (Inv.id ×-cong return-sem′)))) ⟩
  (∃₂ λ s₁ s₂ → ∃ λ x →
      s ≡ s₁ ++ s₂ × x ∈ g ∙ s₁ × y ≡ f x × s₂ ≡ [])      ↔⟨ {!!} ⟩
  (∃ λ x → x ∈ g ∙ s × y ≡ f x)                           ∎

-- The empty string if the argument is true, otherwise failure.

if-true : Bool → Grammar ⊤
if-true true  = return tt
if-true false = fail

if-true-sem : ∀ {b s} → tt ∈ if-true b ∙ s ↔ (T b × s ≡ [])
if-true-sem {true}  {s} = tt ∈ return tt ∙ s  ↔⟨ return-sem′ ⟩
                          (tt ≡ tt × s ≡ [])  ↔⟨ Inv.sym (Iso.True↔ (yes (refl {x = tt})) P.proof-irrelevance) ×-cong Inv.id ⟩
                          (⊤ × s ≡ [])        ∎
if-true-sem {false} {s} = tt ∈ fail ∙ s  ↔⟨ fail-sem ⟩
                          ⊥              ↔⟨ {!!} ⟩
                          (⊥ × s ≡ [])   ∎

-- A token satisfying a given predicate.

sat : (p : Char → Bool) → Grammar Char
sat p = ♯ token >>= λ t → ♯ (const t <$> if-true (p t))

sat-sem : ∀ {p : Char → Bool} {t s} →
          t ∈ sat p ∙ s ↔ (T (p t) × s ≡ [ t ])
sat-sem {p} {t} {s} =
  t ∈ sat p ∙ s                                                ↔⟨ >>=-sem′ ⟩
  (∃₂ λ s₁ s₂ → ∃ λ t′ → s ≡ s₁ ++ s₂ ×
      t′ ∈ token ∙ s₁ × t ∈ const t′ <$> if-true (p t′) ∙ s₂)  ↔⟨ Σ.cong Inv.id (Σ.cong Inv.id (Σ.cong Inv.id
                                                                    (Inv.id ×-cong (token-sem′ ×-cong <$>-sem)))) ⟩
  (∃₂ λ s₁ s₂ → ∃ λ t′ → s ≡ s₁ ++ s₂ ×
      s₁ ≡ [ t′ ] × ∃ λ x → x ∈ if-true (p t′) ∙ s₂ × t ≡ t′)  ↔⟨ Σ.cong Inv.id (Σ.cong Inv.id (Σ.cong Inv.id
                                                                    (Inv.id ×-cong (Inv.id ×-cong Σ.cong Inv.id (if-true-sem ×-cong Inv.id))))) ⟩
  (∃₂ λ s₁ s₂ → ∃ λ t′ → s ≡ s₁ ++ s₂ ×
      s₁ ≡ [ t′ ] × ⊤ × (T (p t′) × s₂ ≡ []) × t ≡ t′)         ↔⟨ {!!} ⟩
  (T (p t) × s ≡ [ t ])                                        ∎

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
