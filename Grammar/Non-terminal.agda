------------------------------------------------------------------------
-- Grammars defined as functions from non-terminals to productions
------------------------------------------------------------------------

module Grammar.Non-terminal where

open import Algebra
open import Data.Bool
open import Data.Char
open import Data.List as List
open import Data.List.Properties using (module List-solver)
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)

private module LM {A : Set} = Monoid (List.monoid A)

open import Tests

------------------------------------------------------------------------
-- Grammars

-- Productions. (Note that productions can contain choices.)

infix  30 _⋆
infixl 15 _>>=_
infixl 10 _∣_

data Prod (NT : Set → Set₁) : Set → Set₁ where
  !      : ∀ {A} → NT A → Prod NT A
  fail   : ∀ {A} → Prod NT A
  return : ∀ {A} → A → Prod NT A
  token  : Prod NT Char
  _>>=_  : ∀ {A B} → Prod NT A → (A → Prod NT B) → Prod NT B
  _∣_    : ∀ {A} → Prod NT A → Prod NT A → Prod NT A
  _⋆     : ∀ {A} → Prod NT A → Prod NT (List A)

-- Grammars.

Grammar : (Set → Set₁) → Set₁
Grammar NT = ∀ A → NT A → Prod NT A

------------------------------------------------------------------------
-- Production combinators

-- A "non-dependent" variant of bind.

infixl 15 _>>_

_>>_ : ∀ {NT A B} → Prod NT A → Prod NT B → Prod NT B
p₁ >> p₂ = p₁ >>= λ _ → p₂

-- Map.

infixl 20 _<$>_
infixr 20 _<$_

_<$>_ : ∀ {NT A B} → (A → B) → Prod NT A → Prod NT B
f <$> p = p >>= (return ∘ f)

_<$_ : ∀ {NT A B} → A → Prod NT B → Prod NT A
x <$ p = const x <$> p

-- "Applicative" sequencing.

infixl 20 _⊛_ _<⊛_ _⊛>_

_⊛_ : ∀ {NT A B} → Prod NT (A → B) → Prod NT A → Prod NT B
p₁ ⊛ p₂ = p₁ >>= λ f → f <$> p₂

_<⊛_ : ∀ {NT A B} → Prod NT A → Prod NT B → Prod NT A
p₁ <⊛ p₂ = p₁ >>= λ x → x <$ p₂

_⊛>_ : ∀ {NT A B} → Prod NT A → Prod NT B → Prod NT B
_⊛>_ = _>>_

-- Kleene plus.

infix 30 _+

_+ : ∀ {NT A} → Prod NT A → Prod NT (List A)
p + = _∷_ <$> p ⊛ p ⋆

-- Elements separated by something.

infixl 18 _sep-by_

_sep-by_ : ∀ {NT A B} → Prod NT A → Prod NT B → Prod NT (List A)
g sep-by sep = _∷_ <$> g ⊛ (sep >> g) ⋆

-- A grammar for tokens satisfying a given predicate.

if-true : ∀ {NT} (b : Bool) → Prod NT (T b)
if-true true  = return tt
if-true false = fail

sat : ∀ {NT} (p : Char → Bool) → Prod NT (∃ λ t → T (p t))
sat p = token >>= λ t → _,_ t <$> if-true (p t)

-- A grammar for a given token.

tok : ∀ {NT} → Char → Prod NT Char
tok t = proj₁ <$> sat (λ t′ → t ≟C t′)

-- A grammar for whitespace.

whitespace : ∀ {NT} → Prod NT Char
whitespace = tok ' ' ∣ tok '\n'

-- A grammar for a given string.

string : ∀ {NT} → List Char → Prod NT (List Char)
string []      = return []
string (t ∷ s) = _∷_ <$> tok t ⊛ string s

-- A grammar for the given string, possibly followed by some
-- whitespace.

symbol : ∀ {NT} → List Char → Prod NT (List Char)
symbol s = string s <⊛ whitespace ⋆

------------------------------------------------------------------------
-- Semantics

infix 4 [_]_∈_∙_

data [_]_∈_∙_ {NT : Set → Set₁} (g : Grammar NT) :
              ∀ {A} → A → Prod NT A → List Char → Set₁ where
  !-sem       : ∀ {A} {nt : NT A} {x s} →
                [ g ] x ∈ g A nt ∙ s → [ g ] x ∈ ! nt ∙ s
  return-sem  : ∀ {A} {x : A} → [ g ] x ∈ return x ∙ []
  token-sem   : ∀ {t} → [ g ] t ∈ token ∙ t ∷ []
  >>=-sem     : ∀ {A B} {p₁ : Prod NT A} {p₂ : A → Prod NT B}
                  {x y s₁ s₂} →
                [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ x ∙ s₂ →
                [ g ] y ∈ p₁ >>= p₂ ∙ s₁ ++ s₂
  ∣-left-sem  : ∀ {A} {p₁ p₂ : Prod NT A} {x s} →
                [ g ] x ∈ p₁ ∙ s → [ g ] x ∈ p₁ ∣ p₂ ∙ s
  ∣-right-sem : ∀ {A} {p₁ p₂ : Prod NT A} {x s} →
                [ g ] x ∈ p₂ ∙ s → [ g ] x ∈ p₁ ∣ p₂ ∙ s
  ⋆-sem       : ∀ {A} {p : Prod NT A} {xs s} →
                [ g ] xs ∈ return [] ∣ p + ∙ s → [ g ] xs ∈ p ⋆ ∙ s

-- Cast lemma.

cast : ∀ {NT g A} {p : Prod NT A} {x s₁ s₂} →
       s₁ ≡ s₂ → [ g ] x ∈ p ∙ s₁ → [ g ] x ∈ p ∙ s₂
cast P.refl = id

------------------------------------------------------------------------
-- Semantics combinators

>>-sem : ∀ {NT g A B} {p₁ : Prod NT A} {p₂ : Prod NT B} {x y s₁ s₂} →
         [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ ∙ s₂ →
         [ g ] y ∈ p₁ >> p₂ ∙ s₁ ++ s₂
>>-sem = >>=-sem

<$>-sem : ∀ {NT} {g : Grammar NT} {A B} {f : A → B} {x p s} →
          [ g ] x ∈ p ∙ s → [ g ] f x ∈ f <$> p ∙ s
<$>-sem x∈ = cast (proj₂ LM.identity _) (>>=-sem x∈ return-sem)

<$-sem : ∀ {NT g A B} {p : Prod NT B} {x : A} {y s} →
         [ g ] y ∈ p ∙ s → [ g ] x ∈ x <$ p ∙ s
<$-sem = <$>-sem

⊛-sem : ∀ {NT g A B} {p₁ : Prod NT (A → B)} {p₂ : Prod NT A}
          {f x s₁ s₂} →
        [ g ] f ∈ p₁ ∙ s₁ → [ g ] x ∈ p₂ ∙ s₂ →
        [ g ] f x ∈ p₁ ⊛ p₂ ∙ s₁ ++ s₂
⊛-sem f∈ x∈ = >>=-sem f∈ (<$>-sem x∈)

<⊛-sem : ∀ {NT g A B} {p₁ : Prod NT A} {p₂ : Prod NT B}
           {x y s₁ s₂} →
         [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ ∙ s₂ →
         [ g ] x ∈ p₁ <⊛ p₂ ∙ s₁ ++ s₂
<⊛-sem x∈ y∈ = >>=-sem x∈ (<$-sem y∈)

⊛>-sem : ∀ {NT g A B} {p₁ : Prod NT A} {p₂ : Prod NT B} {x y s₁ s₂} →
         [ g ] x ∈ p₁ ∙ s₁ → [ g ] y ∈ p₂ ∙ s₂ →
         [ g ] y ∈ p₁ ⊛> p₂ ∙ s₁ ++ s₂
⊛>-sem = >>-sem

+-sem : ∀ {NT g A} {p : Prod NT A} {x xs s₁ s₂} →
        [ g ] x ∈ p ∙ s₁ → [ g ] xs ∈ p ⋆ ∙ s₂ →
        [ g ] x ∷ xs ∈ p + ∙ s₁ ++ s₂
+-sem x∈ xs∈ = ⊛-sem (<$>-sem x∈) xs∈

⋆-sem-[] : ∀ {NT g A} {p : Prod NT A} →
           [ g ] [] ∈ p ⋆ ∙ []
⋆-sem-[] = ⋆-sem (∣-left-sem return-sem)

⋆-sem-∷ : ∀ {NT g A} {p : Prod NT A} {x xs s₁ s₂} →
          [ g ] x ∈ p ∙ s₁ → [ g ] xs ∈ p ⋆ ∙ s₂ →
          [ g ] x ∷ xs ∈ p ⋆ ∙ s₁ ++ s₂
⋆-sem-∷ x∈ xs∈ = ⋆-sem (∣-right-sem (+-sem x∈ xs∈))

sep-by-sem-singleton :
  ∀ {NT g A B} {p : Prod NT A} {sep : Prod NT B} {x s} →
  [ g ] x ∈ p ∙ s → [ g ] [ x ] ∈ p sep-by sep ∙ s
sep-by-sem-singleton x∈ =
  cast (proj₂ LM.identity _) (⊛-sem (<$>-sem x∈) ⋆-sem-[])

sep-by-sem-∷ :
  ∀ {NT g A B} {p : Prod NT A} {sep : Prod NT B} {x y xs s₁ s₂ s₃} →
  [ g ] x ∈ p ∙ s₁ → [ g ] y ∈ sep ∙ s₂ → [ g ] xs ∈ p sep-by sep ∙ s₃ →
  [ g ] x ∷ xs ∈ p sep-by sep ∙ s₁ ++ s₂ ++ s₃
sep-by-sem-∷ {s₂ = s₂}
             x∈ y∈ (>>=-sem (>>=-sem x′∈ return-sem) (>>=-sem xs∈ return-sem)) =
  ⊛-sem (<$>-sem x∈) (cast lemma (⋆-sem-∷ (>>-sem y∈ x′∈) xs∈))
  where
  open List-solver

  lemma = solve 3 (λ a b c → (a ⊕ b) ⊕ c ⊜ a ⊕ (b ⊕ nil) ⊕ c ⊕ nil)
                  P.refl s₂ _ _

if-true-sem : ∀ {NT} {g : Grammar NT} {b}
              (t : T b) → [ g ] t ∈ if-true b ∙ []
if-true-sem {b = true}  _  = return-sem
if-true-sem {b = false} ()

sat-sem : ∀ {NT} {g : Grammar NT} {p t}
          (pt : T (p t)) → [ g ] (t , pt) ∈ sat p ∙ t ∷ []
sat-sem pt = >>=-sem token-sem (<$>-sem (if-true-sem pt))

tok-sem : ∀ {NT} {g : Grammar NT} {t} → [ g ] t ∈ tok t ∙ t ∷ []
tok-sem = <$>-sem (sat-sem ≟C-refl)

whitespace-sem-space : ∀ {NT} {g : Grammar NT} →
                       [ g ] ' ' ∈ whitespace ∙ [ ' ' ]
whitespace-sem-space = ∣-left-sem tok-sem

whitespace-sem-newline : ∀ {NT} {g : Grammar NT} →
                         [ g ] '\n' ∈ whitespace ∙ [ '\n' ]
whitespace-sem-newline = ∣-right-sem tok-sem

string-sem : ∀ {NT} {g : Grammar NT} {s} →
             [ g ] s ∈ string s ∙ s
string-sem {s = []}    = return-sem
string-sem {s = t ∷ s} = ⊛-sem (<$>-sem tok-sem) string-sem

symbol-sem : ∀ {NT} {g : Grammar NT} {s s′ s″} →
             [ g ] s″ ∈ whitespace ⋆ ∙ s′ → [ g ] s ∈ symbol s ∙ s ++ s′
symbol-sem s″∈ = <⊛-sem string-sem s″∈
