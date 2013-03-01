------------------------------------------------------------------------
-- Grammars
------------------------------------------------------------------------

module Grammar where

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

infix  30 _⋆ _+
infixr 20 _<$_
infixl 18 _sep-by_
infixl 15 _>>=_ _≫=_ _>>_
infixl 10 _∣_

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

data G : Set → Set₁ where
  fail   : ∀ {A} → G A
  return : ∀ {A} → A → G A
  token  : G Char
  _>>=_  : ∀ {A B} → ∞ (G A) → (A → ∞ (G B)) → G B
  _∣_    : ∀ {A} → ∞ (G A) → ∞ (G A) → G A

-- Semantics of grammars (parse trees). Here x ∈ g ∙ s means that x is
-- one of the possible results of parsing the string s using the
-- grammar g.

infix 4 _∈_∙_

data _∈_∙_ : ∀ {A} → A → G A → List Char → Set₁ where
  return  : ∀ {A} {x : A} → x ∈ return x ∙ []
  token   : ∀ {t} → t ∈ token ∙ t ∷ []
  _>>=_   : ∀ {A B} {g₁ : ∞ (G A)} {g₂ : A → ∞ (G B)} {x y s₁ s₂} →
            x ∈ ♭ g₁ ∙ s₁ → y ∈ ♭ (g₂ x) ∙ s₂ → y ∈ g₁ >>= g₂ ∙ s₁ ++ s₂
  ∣-left  : ∀ {A} {g₁ g₂ : ∞ (G A)} {x s} →
            x ∈ ♭ g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  ∣-right : ∀ {A} {g₁ g₂ : ∞ (G A)} {x s} →
            x ∈ ♭ g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s

-- Cast lemma.

cast : ∀ {A} {g : G A} {x s₁ s₂} →
       s₁ ≡ s₂ → x ∈ g ∙ s₁ → x ∈ g ∙ s₂
cast refl = id

-- Some derived grammar combinators.

_≫=_ : ∀ {A B} → G A → (A → G B) → G B
g₁ ≫= g₂ = ♯ g₁ >>= λ x → ♯ g₂ x

_>>_ : ∀ {A B} → G A → G B → G B
g₁ >> g₂ = g₁ ≫= λ _ → g₂

_<$_ : ∀ {A B} → A → G B → G A
x <$ g = g >> return x

<$-sem : ∀ {A B} {x : A} {y : B} {g s} →
         y ∈ g ∙ s → x ∈ x <$ g ∙ s
<$-sem y∈ = cast (proj₂ LM.identity _) (y∈ >>= return)

mutual

  _⋆ : ∀ {A} → G A → G (List A)
  g ⋆ = ♯ return [] ∣ ♯ (g +)

  _+ : ∀ {A} → G A → G (List A)
  g + = ♯ g                >>= λ x  → ♯ (
        ♯ (g ⋆)            >>= λ xs →
        ♯ return (x ∷ xs)  )

[]-sem : ∀ {A} {g : G A} → [] ∈ g ⋆ ∙ []
[]-sem = ∣-left return

∷-sem+ : ∀ {A} {g : G A} {x xs s₁ s₂} →
         x ∈ g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g + ∙ s₁ ++ s₂
∷-sem+ {s₁ = s₁} x∈ xs∈ =
  cast (P.cong (_++_ s₁) (proj₂ LM.identity _))
       (x∈ >>= (xs∈ >>= return))

∷-sem⋆ : ∀ {A} {g : G A} {x xs s₁ s₂} →
         x ∈ g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g ⋆ ∙ s₁ ++ s₂
∷-sem⋆ x∈ xs∈ = ∣-right (∷-sem+ x∈ xs∈)

_sep-by_ : ∀ {A B} → G A → G B → G (List A)
g sep-by sep =
  ♯ g                >>= λ x  → ♯ (
  ♯ ((sep >> g) ⋆)   >>= λ xs →
  ♯ return (x ∷ xs)  )

sep-by-sem-singleton :
  ∀ {A B} {g : G A} {sep : G B} {x s} →
  x ∈ g ∙ s → x ∷ [] ∈ g sep-by sep ∙ s
sep-by-sem-singleton x∈ =
  cast (proj₂ LM.identity _)
       (x∈ >>= ([]-sem >>= return))

sep-by-sem-cons :
  ∀ {A B} {g : G A} {sep : G B} {x y xs s₁ s₂ s₃} →
  x ∈ g ∙ s₁ → y ∈ sep ∙ s₂ → xs ∈ g sep-by sep ∙ s₃ →
  x ∷ xs ∈ g sep-by sep ∙ s₁ ++ s₂ ++ s₃
sep-by-sem-cons {s₂ = s₂} x∈ y∈ (x′∈ >>= (xs∈ >>= return)) =
  x∈ >>= cast lemma (∷-sem⋆ (y∈ >>= x′∈) xs∈ >>= return)
  where
  open List-solver

  lemma = solve 4 (λ a b c d → ((a ⊕ b) ⊕ c) ⊕ d ⊜ a ⊕ b ⊕ c ⊕ d)
                  refl s₂ _ _ _

if-true : (b : Bool) → G (T b)
if-true true  = return tt
if-true false = fail

if-true-sem : ∀ {b} (t : T b) → t ∈ if-true b ∙ []
if-true-sem {b = true}  _  = return
if-true-sem {b = false} ()

sat : (p : Char → Bool) → G (∃ λ t → T (p t))
sat p = ♯ token            >>= λ t  → ♯ (
        ♯ if-true (p t)    >>= λ pt →
        ♯ return (t , pt)  )

sat-sem : ∀ {p : Char → Bool} {t} (pt : T (p t)) →
          (t , pt) ∈ sat p ∙ t ∷ []
sat-sem pt = token >>= (if-true-sem pt >>= return)

sat-sem⁻¹ : ∀ {p : Char → Bool} {t pt s} →
            (t , pt) ∈ sat p ∙ s → s ≡ t ∷ []
sat-sem⁻¹ {p = p}
          (_>>=_ {x = t} token (pt∈    >>= return)) with p t
sat-sem⁻¹ (_>>=_ {x = t} token (return >>= return)) | true  = refl
sat-sem⁻¹ (_>>=_ {x = t} token (()     >>= return)) | false

tok : Char → G Char
tok t = ♯ sat (λ t′ → t ≟C t′)  >>= λ { (t , _) →
        ♯ return t              }

tok-sem : ∀ {t} → t ∈ tok t ∙ t ∷ []
tok-sem = sat-sem ≟C-refl >>= return

tok-sem⁻¹ : ∀ {t t′ s} → t ∈ tok t′ ∙ s → t ≡ t′ × s ≡ t ∷ []
tok-sem⁻¹ (_>>=_ {x = _ , t′≡t} tp∈ return) =
  P.sym (≟C⇒≡ t′≡t) , P.cong (λ s → s ++ []) (sat-sem⁻¹ tp∈)

whitespace : G Char
whitespace = ♯ tok ' ' ∣ ♯ tok '\n'

single-space-sem : str " " ∈ whitespace + ∙ str " "
single-space-sem = ∷-sem+ (∣-left tok-sem) []-sem

-- A grammar for the given string.

string : List Char → G (List Char)
string []      = return []
string (t ∷ s) = ♯ tok t           >>= λ t → ♯ (
                 ♯ string s        >>= λ s →
                 ♯ return (t ∷ s)  )

string-sem : ∀ s → s ∈ string s ∙ s
string-sem []      = return
string-sem (t ∷ s) =
  cast (P.cong (_∷_ t) $ proj₂ LM.identity s)
       (tok-sem >>= (string-sem s >>= return))

-- A grammar for the given string, possibly followed by some
-- whitespace.

symbol : List Char → G (List Char)
symbol s = ♯ string s             >>= λ s →
           ♯ (s <$ whitespace ⋆)
