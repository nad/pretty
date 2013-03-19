------------------------------------------------------------------------
-- Abstract grammars
------------------------------------------------------------------------

module Grammar.Abstract where

open import Data.Bool
open import Data.Char
open import Data.Empty
open import Data.List
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Grammars

-- I use an abstract and general definition of grammars: a grammar is
-- a predicate that relates strings with parse results.

Grammar : Set → Set₁
Grammar A = A → List Char → Set

------------------------------------------------------------------------
-- Grammar combinators

-- A grammar for no strings.

fail : ∀ {A} → Grammar A
fail = λ _ _ → ⊥

-- Symmetric choice.

infixl 10 _∣_

_∣_ : ∀ {A} → Grammar A → Grammar A → Grammar A
g₁ ∣ g₂ = λ x s → g₁ x s ⊎ g₂ x s

-- Grammars for the empty string.

return : ∀ {A} → A → Grammar A
return x = λ y s → y ≡ x × s ≡ []

-- Map.

infixl 20 _<$>_ _<$_

_<$>_ : ∀ {A B} → (A → B) → Grammar A → Grammar B
f <$> g = λ x s → ∃ λ y → g y s × x ≡ f y

_<$_ : ∀ {A B} → A → Grammar B → Grammar A
x <$ g = const x <$> g

-- A sequencing combinator for partially applied grammars.

seq : (List Char → Set) → (List Char → Set) → (List Char → Set)
seq p₁ p₂ = λ s → ∃₂ λ s₁ s₂ → p₁ s₁ × p₂ s₂ × s ≡ s₁ ++ s₂

-- Monadic bind.

infixl 15 _>>=_ _>>_

_>>=_ : ∀ {A B} → Grammar A → (A → Grammar B) → Grammar B
g₁ >>= g₂ = λ y s → ∃ λ x → seq (g₁ x) (g₂ x y) s

_>>_ : ∀ {A B} → Grammar A → Grammar B → Grammar B
g₁ >> g₂ = g₁ >>= λ _ → g₂

-- "Applicative" sequencing.

infixl 20 _⊛_ _<⊛_ _⊛>_

_⊛_ : ∀ {A B} → Grammar (A → B) → Grammar A → Grammar B
g₁ ⊛ g₂ = g₁ >>= λ f → f <$> g₂

_<⊛_ : ∀ {A B} → Grammar A → Grammar B → Grammar A
g₁ <⊛ g₂ = λ x s → ∃ λ y → seq (g₁ x) (g₂ y) s

_⊛>_ : ∀ {A B} → Grammar A → Grammar B → Grammar B
_⊛>_ = _>>_

-- Kleene star.

infix 30 _⋆ _+

_⋆ : ∀ {A} → Grammar A → Grammar (List A)
(g ⋆) []       s = s ≡ []
(g ⋆) (x ∷ xs) s = seq (g x) ((g ⋆) xs) s

_+ : ∀ {A} → Grammar A → Grammar (List A)
(g +) []       s = ⊥
(g +) (x ∷ xs) s = (g ⋆) (x ∷ xs) s

-- Elements separated by something.

infixl 18 _sep-by_

_sep-by_ : ∀ {A B} → Grammar A → Grammar B → Grammar (List A)
g sep-by sep = _∷_ <$> g ⊛ (sep >> g) ⋆

-- A grammar for an arbitrary token.

token : Grammar Char
token = λ c s → s ≡ [ c ]

-- A grammar for a given token.

tok : Char → Grammar Char
tok c = λ c′ s → c′ ≡ c × token c′ s

-- A grammar for tokens satisfying a given predicate.

sat : (p : Char → Bool) → Grammar (∃ λ t → T (p t))
sat _ = λ { (c , _) s → token c s }

-- A grammar for whitespace.

whitespace : Grammar Char
whitespace = tok ' ' ∣ tok '\n'

-- A grammar for a given string.

string : List Char → Grammar (List Char)
string s = λ s′ s″ → s′ ≡ s × s″ ≡ s

-- A grammar for the given string, possibly followed by some
-- whitespace.

symbol : List Char → Grammar (List Char)
symbol s = string s <⊛ whitespace ⋆
