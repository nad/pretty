------------------------------------------------------------------------
-- Infinite grammars
------------------------------------------------------------------------

module Grammar.Infinite where

open import Algebra
open import Coinduction
open import Data.Bool
open import Data.Char
open import Data.List as List
open import Data.List.Properties using (module List-solver)
open import Data.Product
open import Data.String using () renaming (toList to str)
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

private module LM {A : Set} = Monoid (List.monoid A)

open import Tests

------------------------------------------------------------------------
-- Grammars

-- Simple, potentially infinite grammars.
--
-- These grammars are very general. Every language that can be
-- recursively enumerated (using an Agda function s : ℕ → List Char)
-- can be expressed using one of these grammars:
-- ♯ s 0 ∣ ♯ (♯ s 1 ∣ …).
--
-- In practice one may want to restrict attention to, say, recursive
-- languages. I use general grammars to illustrate that this approach
-- to pretty-printing is not restricted to a small class of languages.

infixl 15 _>>=_
infixl 10 _∣_

data Grammar : Set → Set₁ where
  fail   : ∀ {A} → Grammar A
  return : ∀ {A} → A → Grammar A
  token  : Grammar Char
  _>>=_  : ∀ {A B} → ∞ (Grammar A) → (A → ∞ (Grammar B)) → Grammar B
  _∣_    : ∀ {A} → ∞ (Grammar A) → ∞ (Grammar A) → Grammar A

------------------------------------------------------------------------
-- Grammar combinators

-- Various sequencing operators.

infixr 20 _<$_
infixl 15 _≫=_ _>>_

_≫=_ : ∀ {A B} → Grammar A → (A → Grammar B) → Grammar B
g₁ ≫= g₂ = ♯ g₁ >>= λ x → ♯ g₂ x

_>>_ : ∀ {A B} → Grammar A → Grammar B → Grammar B
g₁ >> g₂ = g₁ ≫= λ _ → g₂

_<$_ : ∀ {A B} → A → Grammar B → Grammar A
x <$ g = g >> return x

-- Kleene star and plus.

mutual

  infix 30 _⋆ _+

  _⋆ : ∀ {A} → Grammar A → Grammar (List A)
  g ⋆ = ♯ return [] ∣ ♯ (g +)

  _+ : ∀ {A} → Grammar A → Grammar (List A)
  g + = ♯ g                >>= λ x  → ♯ (
        ♯ (g ⋆)            >>= λ xs →
        ♯ return (x ∷ xs)  )

-- Elements separated by something.

infixl 18 _sep-by_

_sep-by_ : ∀ {A B} → Grammar A → Grammar B → Grammar (List A)
g sep-by sep =
  ♯ g                >>= λ x  → ♯ (
  ♯ ((sep >> g) ⋆)   >>= λ xs →
  ♯ return (x ∷ xs)  )

-- A grammar for tokens satisfying a given predicate.

if-true : (b : Bool) → Grammar (T b)
if-true true  = return tt
if-true false = fail

sat : (p : Char → Bool) → Grammar (∃ λ t → T (p t))
sat p = ♯ token            >>= λ t  → ♯ (
        ♯ if-true (p t)    >>= λ pt →
        ♯ return (t , pt)  )

-- A grammar for a given token.

tok : Char → Grammar Char
tok t = ♯ sat (λ t′ → t ≟C t′)  >>= λ { (t , _) →
        ♯ return t              }

-- A grammar for whitespace.

whitespace : Grammar Char
whitespace = ♯ tok ' ' ∣ ♯ tok '\n'

-- A grammar for the given string.

string : List Char → Grammar (List Char)
string []      = return []
string (t ∷ s) = ♯ tok t           >>= λ t → ♯ (
                 ♯ string s        >>= λ s →
                 ♯ return (t ∷ s)  )

-- A grammar for the given string, possibly followed by some
-- whitespace.

symbol : List Char → Grammar (List Char)
symbol s = ♯ string s             >>= λ s →
           ♯ (s <$ whitespace ⋆)

------------------------------------------------------------------------
-- Semantics

-- Semantics of grammars (parse trees). Here x ∈ g ∙ s means that x is
-- one of the possible results of parsing the string s using the
-- grammar g.

infix 4 _∈_∙_

data _∈_∙_ : ∀ {A} → A → Grammar A → List Char → Set₁ where
  return-sem  : ∀ {A} {x : A} → x ∈ return x ∙ []
  token-sem   : ∀ {t} → t ∈ token ∙ [ t ]
  >>=-sem     : ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂ : A → ∞ (Grammar B)}
                  {x y s₁ s₂} →
                x ∈ ♭ g₁ ∙ s₁ → y ∈ ♭ (g₂ x) ∙ s₂ →
                y ∈ g₁ >>= g₂ ∙ s₁ ++ s₂
  ∣-left-sem  : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
                x ∈ ♭ g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  ∣-right-sem : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
                x ∈ ♭ g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s

-- Cast lemma.

cast : ∀ {A} {g : Grammar A} {x s₁ s₂} →
       s₁ ≡ s₂ → x ∈ g ∙ s₁ → x ∈ g ∙ s₂
cast refl = id

------------------------------------------------------------------------
-- Semantics combinators

<$-sem : ∀ {A B} {x : A} {y : B} {g s} →
         y ∈ g ∙ s → x ∈ x <$ g ∙ s
<$-sem y∈ = cast (proj₂ LM.identity _) (>>=-sem y∈ return-sem)

⋆-[]-sem : ∀ {A} {g : Grammar A} → [] ∈ g ⋆ ∙ []
⋆-[]-sem = ∣-left-sem return-sem

+-sem : ∀ {A} {g : Grammar A} {x xs s₁ s₂} →
        x ∈ g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g + ∙ s₁ ++ s₂
+-sem {s₁ = s₁} x∈ xs∈ =
  cast (P.cong (_++_ s₁) (proj₂ LM.identity _))
       (>>=-sem x∈ (>>=-sem xs∈ return-sem))

⋆-∷-sem : ∀ {A} {g : Grammar A} {x xs s₁ s₂} →
          x ∈ g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g ⋆ ∙ s₁ ++ s₂
⋆-∷-sem x∈ xs∈ = ∣-right-sem (+-sem x∈ xs∈)

sep-by-sem-singleton :
  ∀ {A B} {g : Grammar A} {sep : Grammar B} {x s} →
  x ∈ g ∙ s → [ x ] ∈ g sep-by sep ∙ s
sep-by-sem-singleton x∈ =
  cast (proj₂ LM.identity _)
       (>>=-sem x∈ (>>=-sem ⋆-[]-sem return-sem))

sep-by-sem-∷ :
  ∀ {A B} {g : Grammar A} {sep : Grammar B} {x y xs s₁ s₂ s₃} →
  x ∈ g ∙ s₁ → y ∈ sep ∙ s₂ → xs ∈ g sep-by sep ∙ s₃ →
  x ∷ xs ∈ g sep-by sep ∙ s₁ ++ s₂ ++ s₃
sep-by-sem-∷ {s₂ = s₂} x∈ y∈ (>>=-sem x′∈ (>>=-sem xs∈ return-sem)) =
  >>=-sem x∈ (cast lemma
                   (>>=-sem (⋆-∷-sem (>>=-sem y∈ x′∈) xs∈) return-sem))
  where
  open List-solver

  lemma = solve 4 (λ a b c d → ((a ⊕ b) ⊕ c) ⊕ d ⊜ a ⊕ b ⊕ c ⊕ d)
                  refl s₂ _ _ _

if-true-sem : ∀ {b} (t : T b) → t ∈ if-true b ∙ []
if-true-sem {b = true}  _  = return-sem
if-true-sem {b = false} ()

sat-sem : ∀ {p : Char → Bool} {t} (pt : T (p t)) →
          (t , pt) ∈ sat p ∙ [ t ]
sat-sem pt = >>=-sem token-sem (>>=-sem (if-true-sem pt) return-sem)

sat-sem⁻¹ : ∀ {p : Char → Bool} {t pt s} →
            (t , pt) ∈ sat p ∙ s → s ≡ [ t ]
sat-sem⁻¹ {p = p}
          (>>=-sem {x = t} token-sem (>>=-sem pt∈        return-sem)) with p t
sat-sem⁻¹ (>>=-sem {x = t} token-sem (>>=-sem return-sem return-sem)) | true  = refl
sat-sem⁻¹ (>>=-sem {x = t} token-sem (>>=-sem ()         return-sem)) | false

tok-sem : ∀ {t} → t ∈ tok t ∙ [ t ]
tok-sem = >>=-sem (sat-sem ≟C-refl) return-sem

tok-sem⁻¹ : ∀ {t t′ s} → t ∈ tok t′ ∙ s → t ≡ t′ × s ≡ [ t ]
tok-sem⁻¹ (>>=-sem {x = _ , t′≡t} tp∈ return-sem) =
  P.sym (≟C⇒≡ t′≡t) , P.cong (λ s → s ++ []) (sat-sem⁻¹ tp∈)

single-space-sem : str " " ∈ whitespace + ∙ str " "
single-space-sem = +-sem (∣-left-sem tok-sem) ⋆-[]-sem

string-sem : ∀ s → s ∈ string s ∙ s
string-sem []      = return-sem
string-sem (t ∷ s) =
  cast (P.cong (_∷_ t) $ proj₂ LM.identity s)
       (>>=-sem tok-sem (>>=-sem (string-sem s) return-sem))
