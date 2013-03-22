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
open import Function.Related.TypeIsomorphisms
open import Relation.Binary.Product.Pointwise
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
  return-sem : ∀ {A} {x : A} → x ∈ return x ∙ []
  token-sem  : ∀ {t} → t ∈ token ∙ [ t ]
  >>=-sem    : ∀ {A B x y s₁ s₂} {g₁ : ∞ (Grammar A)}
                 {g₂ : A → ∞ (Grammar B)} →
               x ∈ ♭ g₁ ∙ s₁ → y ∈ ♭ (g₂ x) ∙ s₂ →
               y ∈ g₁ >>= g₂ ∙ s₁ ++ s₂
  left-sem   : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
               x ∈ ♭ g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  right-sem  : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
               x ∈ ♭ g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s

----------------------------------------------------------------------
-- Some grammar combinators

-- Failure.

fail : ∀ {A} → Grammar A
fail = ♯ fail ∣ ♯ fail

-- Map.

infixl 20 _<$>_ _<$_

private

  -- A workaround for what I think is an Agda bug.

  _<$>′_ : ∀ {A B} → (A → B) → ∞ (Grammar A) → Grammar B
  f <$>′ g = g >>= λ x → ♯ return (f x)

  delay : ∀ {A} → Grammar A → ∞ (Grammar A)
  delay = ♯_

_<$>_ : ∀ {A B} → (A → B) → Grammar A → Grammar B
f <$> g = f <$>′ delay g

_<$_ : ∀ {A B} → A → Grammar B → Grammar A
x <$ g = const x <$> g

-- The empty string if the argument is true, otherwise failure.

if-true : (b : Bool) → Grammar (T b)
if-true true  = return tt
if-true false = fail

-- A token satisfying a given predicate.

sat : (p : Char → Bool) → Grammar (∃ λ t → T (p t))
sat p = ♯ token >>= λ t → ♯ (_,_ t <$> if-true (p t))

-- A specific token.

tok : Char → Grammar Char
tok t = t <$ sat (λ t′ → t ≟C t′)

------------------------------------------------------------------------
-- Some semantics combinators

-- Cast lemma.

cast : ∀ {A} {g : Grammar A} {x s₁ s₂} →
       s₁ ≡ s₂ → x ∈ g ∙ s₁ → x ∈ g ∙ s₂
cast refl = id

fail-sem⁻¹ : ∀ {A} {x : A} {s} → ¬ (x ∈ fail ∙ s)
fail-sem⁻¹ (left-sem  ∈fail) = fail-sem⁻¹ ∈fail
fail-sem⁻¹ (right-sem ∈fail) = fail-sem⁻¹ ∈fail

<$>-sem : ∀ {A B} {f : A → B} {g : Grammar A} {y s} →
          y ∈ f <$> g ∙ s ↔ ∃ λ x → x ∈ g ∙ s × y ≡ f x
<$>-sem {A} {B} {f} {g} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ (from (delay g))
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from (delay g)
    }
  }
  where
  lemma : ∀ s → s ++ [] ≡ s
  lemma s = proj₂ LM.identity s

  to : ∀ {s g y} → y ∈ f <$>′ g ∙ s → ∃ λ x → x ∈ ♭ g ∙ s × y ≡ f x
  to (>>=-sem x∈ return-sem) =
    _ , cast (P.sym $ lemma _) x∈ , refl

  from : ∀ {s y} g → (∃ λ x → x ∈ ♭ g ∙ s × y ≡ f x) → y ∈ f <$>′ g ∙ s
  from _ (x , x∈ , refl) = cast (lemma _) (>>=-sem x∈ return-sem)

  >>=-cast : ∀ {x y s₁ s₂ s}
               {g₁ : ∞ (Grammar A)} {g₂ : A → ∞ (Grammar B)}
             (eq : s₁ ≡ s₂)
             (x∈ : x ∈ ♭ g₁ ∙ s₁) (y∈ : y ∈ ♭ (g₂ x) ∙ s) →
             >>=-sem {g₁ = g₁} {g₂ = g₂} (cast eq x∈) y∈ ≡
             cast (P.cong (λ s′ → s′ ++ s) eq) (>>=-sem x∈ y∈)
  >>=-cast refl _ _ = refl

  cast-cast : ∀ {A g s₁ s₂} {z : A} {z∈ : z ∈ g ∙ s₂}
              (eq₁ : s₁ ≡ s₂) (eq₂ : s₂ ≡ s₁) →
              cast eq₁ (cast eq₂ z∈) ≡ z∈
  cast-cast refl refl = refl

  from∘to : ∀ {s g y} (y∈ : y ∈ f <$>′ g ∙ s) → from _ (to y∈) ≡ y∈
  from∘to (>>=-sem {s₁ = s} x∈ return-sem) = begin
    cast (lemma (s ++ []))
         (>>=-sem (cast (P.sym $ lemma s) x∈) return-sem)  ≡⟨ P.cong (cast (lemma (s ++ []))) $
                                                                     >>=-cast (P.sym (lemma s)) x∈ return-sem ⟩
    cast (lemma (s ++ []))
         (cast (P.cong (λ s → s ++ []) (P.sym $ lemma s))
               (>>=-sem x∈ return-sem))                    ≡⟨ cast-cast (lemma (s ++ []))
                                                                        (P.cong (λ s → s ++ []) (P.sym $ lemma s)) ⟩
    >>=-sem x∈ return-sem                                  ∎
    where open P.≡-Reasoning

  to-cast : ∀ {s₁ s₂ y} g (eq : s₁ ≡ s₂) (y∈ : y ∈ f <$>′ g ∙ s₁) →
            to (cast eq y∈) ≡
            P.subst (λ s → ∃ λ x → x ∈ ♭ g ∙ s × y ≡ f x) eq (to y∈)
  to-cast _ refl y∈ = refl

  to∘from : ∀ {s y} g
            (x∈ : ∃ λ x → x ∈ ♭ g ∙ s × y ≡ f x) → to (from g x∈) ≡ x∈
  to∘from {s} g (x , x∈ , refl)
    rewrite to-cast g (lemma s) (>>=-sem x∈ return-sem)
          | lemma s
    = refl

if-true-sem : ∀ {b} x {s} → x ∈ if-true b ∙ s ↔ s ≡ []
if-true-sem x = record
  { to         = P.→-to-⟶ (to _)
  ; from       = P.→-to-⟶ (from _ _)
  ; inverse-of = record
    { left-inverse-of  = from∘to _
    ; right-inverse-of = to∘from _ x
    }
  }
  where
  to : ∀ b {x s} → x ∈ if-true b ∙ s → s ≡ []
  to true  return-sem = refl
  to false ∈fail      = ⊥-elim $ fail-sem⁻¹ ∈fail

  from : ∀ b x {s} → s ≡ [] → x ∈ if-true b ∙ s
  from true  _  refl = return-sem
  from false () refl

  from∘to : ∀ b {x s} (x∈ : x ∈ if-true b ∙ s) → from b x (to b x∈) ≡ x∈
  from∘to true  return-sem = refl
  from∘to false ∈fail      = ⊥-elim $ fail-sem⁻¹ ∈fail

  to∘from : ∀ b x {s} (eq : s ≡ []) → to b (from b x eq) ≡ eq
  to∘from true  _  refl = refl
  to∘from false () refl

sat-sem : ∀ {p : Char → Bool} {t pt s} →
          (t , pt) ∈ sat p ∙ s ↔ s ≡ [ t ]
sat-sem {p} {t} {pt} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
  to : ∀ {s} → (t , pt) ∈ sat p ∙ s → s ≡ [ t ]
  to (>>=-sem token-sem (>>=-sem tt∈ return-sem)) =
    P.cong (λ s → t ∷ s ++ []) (Inverse.to (if-true-sem pt) ⟨$⟩ tt∈)

  from : ∀ {s} → s ≡ [ t ] → (t , pt) ∈ sat p ∙ s
  from refl =
    >>=-sem token-sem
            (>>=-sem (Inverse.from (if-true-sem pt) ⟨$⟩ refl)
                     return-sem)

  from∘to : ∀ {s} (t∈ : (t , pt) ∈ sat p ∙ s) → from (to t∈) ≡ t∈
  from∘to (>>=-sem token-sem (>>=-sem tt∈ return-sem))
    with Inverse.to (if-true-sem pt) ⟨$⟩ tt∈
       | Inverse.left-inverse-of (if-true-sem pt) tt∈
  from∘to (>>=-sem token-sem
             (>>=-sem .(Inverse.from (if-true-sem pt) ⟨$⟩ refl)
                      return-sem))
    | refl | refl = refl

  to∘from : ∀ {s} (eq : s ≡ [ t ]) → to (from eq) ≡ eq
  to∘from refl
    rewrite Inverse.right-inverse-of (if-true-sem pt) refl
    = refl

abstract

  -- Grammar.Infinite requires a lot more memory to type-check if this
  -- definition is made concrete (at the time of writing).

  tok-sem : ∀ {t′ t s} → t′ ∈ tok t ∙ s ↔ (t ≡ t′ × s ≡ [ t ])
  tok-sem {t′} {t} {s} =
    t′ ∈ tok t ∙ s                                   ↔⟨ <$>-sem ⟩
    (∃ λ p → p ∈ sat (λ t′ → t ≟C t′) ∙ s × t′ ≡ t)  ↔⟨ Σ.cong Inv.id (sat-sem ×-cong Inv.id) ⟩
    (∃ λ p → s ≡ [ proj₁ p ] × t′ ≡ t)               ↔⟨ Σ-assoc ⟩
    (∃ λ t″ → T (t ≟C t″) × s ≡ [ t″ ] × t′ ≡ t)     ↔⟨ Σ.cong Inv.id (≟C↔≡ ×-cong Inv.id) ⟩
    (∃ λ t″ → t ≡ t″ × s ≡ [ t″ ] × t′ ≡ t)          ↔⟨ lemma ⟩
    (t ≡ t′ × s ≡ [ t ])                             ∎
    where
    open Related.EquationalReasoning

    lemma : (∃ λ t″ → t ≡ t″ × s ≡ [ t″ ] × t′ ≡ t) ↔
            (t ≡ t′ × s ≡ [ t ])
    lemma = record
      { to         = P.→-to-⟶ to
      ; from       = P.→-to-⟶ from
      ; inverse-of = record
        { left-inverse-of  = from∘to
        ; right-inverse-of = to∘from
        }
      }
      where
      to : ∀ {t′ t : Char} {s} →
           (∃ λ t″ → t ≡ t″ × s ≡ [ t″ ] × t′ ≡ t) → t ≡ t′ × s ≡ [ t ]
      to (._ , refl , refl , refl) = (refl , refl)

      from : ∀ {t′ t : Char} {s} →
             t ≡ t′ × s ≡ [ t ] → ∃ λ t″ → t ≡ t″ × s ≡ [ t″ ] × t′ ≡ t
      from (refl , refl) = (_ , refl , refl , refl)

      from∘to : ∀ {t′ t : Char} {s}
                (eqs : ∃ λ t″ → t ≡ t″ × s ≡ [ t″ ] × t′ ≡ t) →
                from (to eqs) ≡ eqs
      from∘to (._ , refl , refl , refl) = refl

      to∘from : ∀ {t′ t : Char} {s} (eqs : t ≡ t′ × s ≡ [ t ]) →
                to (from eqs) ≡ eqs
      to∘from (refl , refl) = refl
