------------------------------------------------------------------------
-- Infinite grammars
------------------------------------------------------------------------

module Grammar.Infinite where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.Bool
open import Data.Char
open import Data.List as List
open import Data.List.Properties using (module List-solver)
open import Data.Maybe as Maybe
open import Data.Nat
open import Data.Product
open import Data.String using () renaming (toList to str)
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

private
  module LM {A : Set} = Monoid (List.monoid A)
  open module MM {f} = RawMonadPlus (Maybe.monadPlus {f = f})
    using () renaming (_<$>_ to _<$>M_; _⊛_ to _⊛M_)

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

infix  30 _⋆
infixl 20 _<$>_ _⊛_ _<⊛_ _⊛>_
infixl 15 _>>=_
infixl 10 _∣_

data Grammar : Set → Set₁ where
  fail   : ∀ {A} → Grammar A
  return : ∀ {A} → A → Grammar A
  token  : Grammar Char
  tok    : Char → Grammar Char
  _<$>_  : ∀ {A B} → (A → B) → ∞ (Grammar A) → Grammar B
  _⊛_    : ∀ {A B} → ∞ (Grammar (A → B)) → ∞ (Grammar A) → Grammar B
  _<⊛_   : ∀ {A B} → ∞ (Grammar A) → ∞ (Grammar B) → Grammar A
  _⊛>_   : ∀ {A B} → ∞ (Grammar A) → ∞ (Grammar B) → Grammar B
  _>>=_  : ∀ {A B} → ∞ (Grammar A) → (A → ∞ (Grammar B)) → Grammar B
  _∣_    : ∀ {A} → ∞ (Grammar A) → ∞ (Grammar A) → Grammar A
  _⋆     : ∀ {A} → ∞ (Grammar A) → Grammar (List A)

------------------------------------------------------------------------
-- Grammar combinators

-- A grammar that always returns the same result.

infixr 20 _<$_

_<$_ : ∀ {A B} → A → Grammar B → Grammar A
x <$ g = ♯ return x <⊛ ♯ g

-- Kleene plus.

infix 30 _+

_+ : ∀ {A} → ∞ (Grammar A) → Grammar (List A)
p + = ♯ (_∷_ <$> p) ⊛ ♯ (p ⋆)

-- Elements preceded by something.

infixl 18 _prec-by_

_prec-by_ : ∀ {A B} → Grammar A → Grammar B → Grammar (List A)
g prec-by prec = ♯ (♯ prec ⊛> ♯ g) ⋆

-- Elements separated by something.

infixl 18 _sep-by_

_sep-by_ : ∀ {A B} → Grammar A → Grammar B → Grammar (List A)
g sep-by sep = ♯ (_∷_ <$> ♯ g) ⊛ ♯ (g prec-by sep)

-- A grammar for tokens satisfying a given predicate.

if-true : (b : Bool) → Grammar (T b)
if-true true  = return tt
if-true false = fail

sat : (p : Char → Bool) → Grammar (∃ λ t → T (p t))
sat p = ♯ token >>= λ t → ♯ (_,_ t <$> ♯ if-true (p t))

-- Grammars for whitespace.

whitespace : Grammar Char
whitespace = ♯ tok ' ' ∣ ♯ tok '\n'

♯whitespace : ∞ (Grammar Char)
♯whitespace = ♯ whitespace

whitespace⋆ : Grammar (List Char)
whitespace⋆ = ♯whitespace ⋆

whitespace+ : Grammar (List Char)
whitespace+ = ♯whitespace +

-- A grammar for the given string.

string : List Char → Grammar (List Char)
string []      = return []
string (t ∷ s) = ♯ (_∷_ <$> ♯ tok t) ⊛ ♯ string s

-- A grammar for the given string, possibly followed by some
-- whitespace.

symbol : List Char → Grammar (List Char)
symbol s = ♯ string s <⊛ ♯ whitespace⋆

-- Variants that take non-delayed arguments.

infix  30 _⋆′ _+′
infixl 20 _<$>′_ _⊛′_ _<⊛′_ _⊛>′_
infixl 15 _>>=′_

_<$>′_ : ∀ {A B} → (A → B) → Grammar A → Grammar B
f <$>′ g = f <$> ♯ g

_⊛′_ : ∀ {A B} → Grammar (A → B) → Grammar A → Grammar B
g₁ ⊛′ g₂ = ♯ g₁ ⊛ ♯ g₂

_<⊛′_ : ∀ {A B} → Grammar A → Grammar B → Grammar A
g₁ <⊛′ g₂ = ♯ g₁ <⊛ ♯ g₂

_⊛>′_ : ∀ {A B} → Grammar A → Grammar B → Grammar B
g₁ ⊛>′ g₂ = ♯ g₁ ⊛> ♯ g₂

_>>=′_ : ∀ {A B} → Grammar A → (A → Grammar B) → Grammar B
g₁ >>=′ g₂ = ♯ g₁ >>= λ x → ♯ g₂ x

_⋆′ : ∀ {A} → Grammar A → Grammar (List A)
g ⋆′ = ♯ g ⋆

_+′ : ∀ {A} → Grammar A → Grammar (List A)
g +′ = ♯ g +

------------------------------------------------------------------------
-- Semantics

-- Semantics of grammars (parse trees). Here x ∈ g ∙ s means that x is
-- one of the possible results of parsing the string s using the
-- grammar g.

infix 4 _∈_∙_

data _∈_∙_ : ∀ {A} → A → Grammar A → List Char → Set₁ where
  return-sem  : ∀ {A} {x : A} → x ∈ return x ∙ []
  token-sem   : ∀ {t} → t ∈ token ∙ [ t ]
  tok-sem     : ∀ {t} → t ∈ tok t ∙ [ t ]
  <$>-sem     : ∀ {A B} {f : A → B} {g : ∞ (Grammar A)} {x s} →
                x ∈ ♭ g ∙ s → f x ∈ f <$> g ∙ s
  ⊛-sem       : ∀ {A B} {g₁ : ∞ (Grammar (A → B))} {g₂ : ∞ (Grammar A)}
                  {f x s₁ s₂} →
                f ∈ ♭ g₁ ∙ s₁ → x ∈ ♭ g₂ ∙ s₂ → f x ∈ g₁ ⊛ g₂ ∙ s₁ ++ s₂
  <⊛-sem      : ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂ : ∞ (Grammar B)}
                  {x y s₁ s₂} →
                x ∈ ♭ g₁ ∙ s₁ → y ∈ ♭ g₂ ∙ s₂ → x ∈ g₁ <⊛ g₂ ∙ s₁ ++ s₂
  ⊛>-sem      : ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂ : ∞ (Grammar B)}
                  {x y s₁ s₂} →
                x ∈ ♭ g₁ ∙ s₁ → y ∈ ♭ g₂ ∙ s₂ → y ∈ g₁ ⊛> g₂ ∙ s₁ ++ s₂
  >>=-sem     : ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂ : A → ∞ (Grammar B)}
                  {x y s₁ s₂} →
                x ∈ ♭ g₁ ∙ s₁ → y ∈ ♭ (g₂ x) ∙ s₂ →
                y ∈ g₁ >>= g₂ ∙ s₁ ++ s₂
  ∣-left-sem  : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
                x ∈ ♭ g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  ∣-right-sem : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x s} →
                x ∈ ♭ g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  ⋆-[]-sem    : ∀ {A} {g : ∞ (Grammar A)} →
                [] ∈ g ⋆ ∙ []
  ⋆-+-sem     : ∀ {A} {g : ∞ (Grammar A)} {xs s} →
                xs ∈ g + ∙ s → xs ∈ g ⋆ ∙ s

-- Cast lemma.

cast : ∀ {A} {g₁ g₂ : Grammar A} {x s₁ s₂} →
       g₁ ≡ g₂ → s₁ ≡ s₂ → x ∈ g₁ ∙ s₁ → x ∈ g₂ ∙ s₂
cast refl refl = id

------------------------------------------------------------------------
-- Semantics combinators

<$-sem : ∀ {A B} {x : A} {y : B} {g s} →
         y ∈ g ∙ s → x ∈ x <$ g ∙ s
<$-sem y∈ = <⊛-sem return-sem y∈

+-sem : ∀ {A} {g : ∞ (Grammar A)} {x xs s₁ s₂} →
        x ∈ ♭ g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g + ∙ s₁ ++ s₂
+-sem x∈ xs∈ = ⊛-sem (<$>-sem x∈) xs∈

⋆-∷-sem : ∀ {A} {g : ∞ (Grammar A)} {x xs s₁ s₂} →
          x ∈ ♭ g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g ⋆ ∙ s₁ ++ s₂
⋆-∷-sem x∈ xs∈ = ⋆-+-sem (+-sem x∈ xs∈)

⋆-⋆-sem : ∀ {A} {g : ∞ (Grammar A)} {xs₁ xs₂ s₁ s₂} →
          xs₁ ∈ g ⋆ ∙ s₁ → xs₂ ∈ g ⋆ ∙ s₂ → xs₁ ++ xs₂ ∈ g ⋆ ∙ s₁ ++ s₂
⋆-⋆-sem ⋆-[]-sem xs₂∈ = xs₂∈
⋆-⋆-sem (⋆-+-sem (⊛-sem (<$>-sem {s = s₁} x∈) xs₁∈)) xs₂∈ =
  cast refl (P.sym $ LM.assoc s₁ _ _)
       (⋆-∷-sem x∈ (⋆-⋆-sem xs₁∈ xs₂∈))

+-∷-sem : ∀ {A} {g : ∞ (Grammar A)} {x xs s₁ s₂} →
          x ∈ ♭ g ∙ s₁ → xs ∈ g + ∙ s₂ → x ∷ xs ∈ g + ∙ s₁ ++ s₂
+-∷-sem x∈ xs∈ = +-sem x∈ (⋆-+-sem xs∈)

sep-by-sem-singleton :
  ∀ {A B} {g : Grammar A} {sep : Grammar B} {x s} →
  x ∈ g ∙ s → [ x ] ∈ g sep-by sep ∙ s
sep-by-sem-singleton x∈ =
  cast refl (proj₂ LM.identity _)
       (⊛-sem (<$>-sem x∈) ⋆-[]-sem)

sep-by-sem-∷ :
  ∀ {A B} {g : Grammar A} {sep : Grammar B} {x y xs s₁ s₂ s₃} →
  x ∈ g ∙ s₁ → y ∈ sep ∙ s₂ → xs ∈ g sep-by sep ∙ s₃ →
  x ∷ xs ∈ g sep-by sep ∙ s₁ ++ s₂ ++ s₃
sep-by-sem-∷ {s₂ = s₂} x∈ y∈ (⊛-sem (<$>-sem x′∈) xs∈) =
  ⊛-sem (<$>-sem x∈)
        (cast refl (LM.assoc s₂ _ _)
              (⋆-∷-sem (⊛>-sem y∈ x′∈) xs∈))

if-true-sem : ∀ {b} (t : T b) → t ∈ if-true b ∙ []
if-true-sem {b = true}  _  = return-sem
if-true-sem {b = false} ()

sat-sem : ∀ {p : Char → Bool} {t} (pt : T (p t)) →
          (t , pt) ∈ sat p ∙ [ t ]
sat-sem pt = >>=-sem token-sem (<$>-sem (if-true-sem pt))

single-space-sem : str " " ∈ whitespace+ ∙ str " "
single-space-sem = +-sem (∣-left-sem tok-sem) ⋆-[]-sem

string-sem : ∀ {s} → s ∈ string s ∙ s
string-sem {s = []}    = return-sem
string-sem {s = t ∷ s} = ⊛-sem (<$>-sem tok-sem) string-sem

------------------------------------------------------------------------
-- Detecting the whitespace combinator

-- A predicate for the whitespace combinator.

data Is-whitespace : ∀ {A} → Grammar A → Set₁ where
  is-whitespace :
    ∀ {g g₁ g₂} →
    g ≡ g₁ ∣ g₂ →
    ♭ g₁ ≡ tok ' ' →
    ♭ g₂ ≡ tok '\n' →
    Is-whitespace g

-- Detects the whitespace combinator.

is-whitespace? : ∀ {A} (g : Grammar A) → Maybe (Is-whitespace g)
is-whitespace? (g₁ ∣ g₂) = helper _ _ refl refl refl
  where
  helper : ∀ {A B} {g₁ g₂} (g₁′ : Grammar A) (g₂′ : Grammar B) →
           (eq : A ≡ B) → ♭ g₁ ≡ g₁′ → ♭ g₂ ≡ g₂′ →
           Maybe (Is-whitespace (P.subst (∞ ∘ Grammar) eq g₁ ∣ g₂))
  helper (tok ' ') (tok '\n') refl eq₁ eq₂ =
    just (is-whitespace refl eq₁ eq₂)
  helper _ _ _ _ _ = nothing

is-whitespace? _ = nothing

------------------------------------------------------------------------
-- Final whitespace

-- A predicate for grammars that can "swallow" extra whitespace at the
-- end.

Final-whitespace : ∀ {A} → Grammar A → Set₁
Final-whitespace g =
  ∀ {x s₁ s₂ s} →
  x ∈ g ∙ s₁ → s ∈ whitespace⋆ ∙ s₂ → x ∈ g ∙ s₁ ++ s₂

-- A similar but weaker property.

Final-whitespace′ : ∀ {A} → Grammar A → Set₁
Final-whitespace′ g =
  ∀ {x s₁ s₂ s} →
  x ∈ g ∙ s₁ → s ∈ whitespace⋆ ∙ s₂ → ∃ λ y → y ∈ g ∙ s₁ ++ s₂

-- A heuristic (and rather incomplete) procedure that either proves
-- that a production can swallow final whitespace (in the weaker
-- sense), or returns "don't know" as the answer.
--
-- The natural number n is the maximum unfolding (forcing) depth.

final-whitespace′? : ∀ (n : ℕ) {A} (g : Grammar A) →
                     Maybe (Final-whitespace′ g)
final-whitespace′? = final?
  where
  <$>-lemma : ∀ {A B} {f : A → B} {g} →
              Final-whitespace′ (♭ g) →
              Final-whitespace′ (f <$> g)
  <$>-lemma f (<$>-sem x∈) w = , <$>-sem (proj₂ $ f x∈ w)

  ⊛-lemma : ∀ {A B} {g₁ : ∞ (Grammar (A → B))} {g₂ : ∞ (Grammar A)} →
            Final-whitespace′ (♭ g₂) →
            Final-whitespace′ (g₁ ⊛ g₂)
  ⊛-lemma f₂ (⊛-sem {s₁ = s₁} f∈ x∈) w =
    , cast refl (P.sym $ LM.assoc s₁ _ _)
           (⊛-sem f∈ (proj₂ $ f₂ x∈ w))

  <⊛-lemma : ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂ : ∞ (Grammar B)} →
             Final-whitespace′ (♭ g₂) →
             Final-whitespace′ (g₁ <⊛ g₂)
  <⊛-lemma f₂ (<⊛-sem {s₁ = s₁} x∈ y∈) w =
    , cast refl (P.sym $ LM.assoc s₁ _ _)
           (<⊛-sem x∈ (proj₂ $ f₂ y∈ w))

  ⊛>-lemma : ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂ : ∞ (Grammar B)} →
             Final-whitespace′ (♭ g₂) →
             Final-whitespace′ (g₁ ⊛> g₂)
  ⊛>-lemma f₂ (⊛>-sem {s₁ = s₁} x∈ y∈) w =
    , cast refl (P.sym $ LM.assoc s₁ _ _)
           (⊛>-sem x∈ (proj₂ $ f₂ y∈ w))

  ∣-lemma : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} →
            Final-whitespace′ (♭ g₁) →
            Final-whitespace′ (♭ g₂) →
            Final-whitespace′ (g₁ ∣ g₂)
  ∣-lemma f₁ f₂ (∣-left-sem  x∈) w = , ∣-left-sem  (proj₂ $ f₁ x∈ w)
  ∣-lemma f₁ f₂ (∣-right-sem x∈) w = , ∣-right-sem (proj₂ $ f₂ x∈ w)

  whitespace⋆-lemma :
    ∀ {A} {g : ∞ (Grammar A)} →
    Is-whitespace (♭ g) →
    Final-whitespace′ (g ⋆)
  whitespace⋆-lemma {g = g} (is-whitespace eq₁ eq₂ eq₃) xs∈ w =
    , ⋆-⋆-sem xs∈ (coerce w)
    where
    coerce : ∀ {xs s} → xs ∈ whitespace⋆ ∙ s → xs ∈ g ⋆ ∙ s
    coerce ⋆-[]-sem                           = ⋆-[]-sem
    coerce (⋆-+-sem (⊛-sem (<$>-sem x∈) xs∈))
      rewrite eq₁ with x∈
    ... | ∣-left-sem  x∈′ = ⋆-∷-sem
                              (cast (P.sym eq₁) refl
                                    (∣-left-sem (cast (P.sym eq₂) refl
                                                      x∈′)))
                              (coerce xs∈)
    ... | ∣-right-sem x∈′ = ⋆-∷-sem
                              (cast (P.sym eq₁) refl
                                    (∣-right-sem (cast (P.sym eq₃) refl
                                                       x∈′)))
                              (coerce xs∈)

  final? : ℕ → ∀ {A} (g : Grammar A) → Maybe (Final-whitespace′ g)
  final? (suc n) fail       = just (λ ())
  final? (suc n) (f <$> g)  = <$>-lemma <$>M final? n (♭ g)
  final? (suc n) (g₁ ⊛ g₂)  = ⊛-lemma   <$>M final? n (♭ g₂)
  final? (suc n) (g₁ <⊛ g₂) = <⊛-lemma  <$>M final? n (♭ g₂)
  final? (suc n) (g₁ ⊛> g₂) = ⊛>-lemma  <$>M final? n (♭ g₂)
  final? (suc n) (g₁ ∣ g₂)  = ∣-lemma   <$>M final? n (♭ g₁)
                                          ⊛M final? n (♭ g₂)
  final? (suc n) (g ⋆)      = whitespace⋆-lemma <$>M is-whitespace? (♭ g)
  final? _       _          = nothing

-- A heuristic (and rather incomplete) procedure that either proves
-- that a production can swallow final whitespace, or returns "don't
-- know" as the answer.
--
-- The natural number n is the maximum unfolding (forcing) depth.

final-whitespace? : ∀ (n : ℕ) {A} (g : Grammar A) →
                    Maybe (Final-whitespace g)
final-whitespace? = final?
  where
  ++-lemma = solve 2 (λ a b → (a ⊕ b) ⊕ nil ⊜ (a ⊕ nil) ⊕ b) refl
    where open List-solver

  -- The lemmas below are unfortunately rather unreadable. There are
  -- similar lemmas in Grammar.Non-terminal, and they are hopefully
  -- easier to follow.

  <$>-lemma : ∀ {A B} {f : A → B} {g} →
              Final-whitespace (♭ g) →
              Final-whitespace (f <$> g)
  <$>-lemma f (<$>-sem x∈) w = <$>-sem (f x∈ w)

  ⊛-return-lemma :
    ∀ {A B} {g₁ : ∞ (Grammar (A → B))} {g₂ x} →
    ♭ g₂ ≡ return x →
    Final-whitespace (♭ g₁) → Final-whitespace (g₁ ⊛ g₂)
  ⊛-return-lemma eq f₁ (⊛-sem {s₁ = s₁} f∈ x∈) w
    rewrite eq with x∈
  ... | return-sem =
    cast refl (++-lemma s₁ _)
         (⊛-sem (f₁ f∈ w)
                (cast (P.sym eq) refl
                      return-sem))

  +-lemma :
    ∀ {A} {g : ∞ (Grammar A)} →
    Final-whitespace (♭ g) →
    Final-whitespace (g +)
  +-lemma f (⊛-sem {s₁ = s₁} (<$>-sem x∈) ⋆-[]-sem) w =
    cast refl (++-lemma s₁ _)
         (+-sem (f x∈ w) ⋆-[]-sem)
  +-lemma f (⊛-sem {s₁ = s₁} (<$>-sem x∈) (⋆-+-sem xs∈)) w =
    cast refl (P.sym $ LM.assoc s₁ _ _)
         (+-∷-sem x∈ (+-lemma f xs∈ w))

  ⊛-⋆-lemma :
    ∀ {A B} {g₁ : ∞ (Grammar (List A → B))} {g₂ g₂₁} →
    ♭ g₂ ≡ g₂₁ ⋆ →
    Final-whitespace (♭ g₁) →
    Final-whitespace (♭ g₂₁) →
    Final-whitespace (g₁ ⊛ g₂)
  ⊛-⋆-lemma eq f₁ f₂ (⊛-sem {s₁ = s₁} f∈ xs∈) w
    rewrite eq with xs∈
  ... | ⋆-[]-sem     = cast refl (++-lemma s₁ _)
                            (⊛-sem (f₁ f∈ w)
                                   (cast (P.sym eq) refl
                                         ⋆-[]-sem))
  ... | ⋆-+-sem xs∈′ = cast refl (P.sym $ LM.assoc s₁ _ _)
                            (⊛-sem f∈
                                   (cast (P.sym eq) refl
                                         (⋆-+-sem (+-lemma f₂ xs∈′ w))))

  ⊛-∣-lemma : ∀ {A B} {g₁ : ∞ (Grammar (A → B))} {g₂ g₂₁ g₂₂} →
              ♭ g₂ ≡ g₂₁ ∣ g₂₂ →
              Final-whitespace (g₁ ⊛ g₂₁) →
              Final-whitespace (g₁ ⊛ g₂₂) →
              Final-whitespace (g₁ ⊛ g₂)
  ⊛-∣-lemma eq f₁₂ f₁₃ (⊛-sem f∈ x∈) w rewrite eq with x∈
  ⊛-∣-lemma eq f₁₂ f₁₃ {s₂ = s₃}
            (⊛-sem {f = f} {x = x} {s₁ = s₁} {s₂ = s₂} f∈ x∈) w
    | ∣-left-sem x∈′
    with f x | (s₁ ++ s₂) ++ s₃ | f₁₂ (⊛-sem f∈ x∈′) w
  ... | ._ | ._ | ⊛-sem f∈″ x∈″ =
    ⊛-sem f∈″ (cast (P.sym eq) refl (∣-left-sem x∈″))
  ⊛-∣-lemma eq f₁₂ f₁₃ {s₂ = s₃}
            (⊛-sem {f = f} {x = x} {s₁ = s₁} {s₂ = s₂} f∈ x∈) w
    | ∣-right-sem x∈′
    with f x | (s₁ ++ s₂) ++ s₃ | f₁₃ (⊛-sem f∈ x∈′) w
  ... | ._ | ._ | ⊛-sem f∈″ x∈″ =
    ⊛-sem f∈″ (cast (P.sym eq) refl (∣-right-sem x∈″))

  ⊛-lemma : ∀ {A B} {g₁ : ∞ (Grammar (A → B))} {g₂ : ∞ (Grammar A)} →
            Final-whitespace (♭ g₂) →
            Final-whitespace (g₁ ⊛ g₂)
  ⊛-lemma f₂ (⊛-sem {s₁ = s₁} f∈ x∈) w =
    cast refl (P.sym $ LM.assoc s₁ _ _)
         (⊛-sem f∈ (f₂ x∈ w))

  <⊛-return-lemma :
    ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂} {x : B} →
    ♭ g₂ ≡ return x →
    Final-whitespace (♭ g₁) →
    Final-whitespace (g₁ <⊛ g₂)
  <⊛-return-lemma eq f (<⊛-sem {s₁ = s₁} f∈ x∈) w
    rewrite eq with x∈
  ... | return-sem =
    cast refl (++-lemma s₁ _)
         (<⊛-sem (f f∈ w)
                 (cast (P.sym eq) refl
                       return-sem))

  <⊛-lemma : ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂ : ∞ (Grammar B)} →
             Final-whitespace′ (♭ g₂) →
             Final-whitespace (g₁ <⊛ g₂)
  <⊛-lemma f₂ (<⊛-sem {s₁ = s₁} x∈ y∈) w =
    cast refl (P.sym $ LM.assoc s₁ _ _)
         (<⊛-sem x∈ (proj₂ $ f₂ y∈ w))

  ⊛>-lemma : ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂ : ∞ (Grammar B)} →
             Final-whitespace (♭ g₂) →
             Final-whitespace (g₁ ⊛> g₂)
  ⊛>-lemma f₂ (⊛>-sem {s₁ = s₁} x∈ y∈) w =
    cast refl (P.sym $ LM.assoc s₁ _ _)
         (⊛>-sem x∈ (f₂ y∈ w))

  ∣-lemma : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} →
            Final-whitespace (♭ g₁) →
            Final-whitespace (♭ g₂) →
            Final-whitespace (g₁ ∣ g₂)
  ∣-lemma f₁ f₂ (∣-left-sem  x∈) w = ∣-left-sem  (f₁ x∈ w)
  ∣-lemma f₁ f₂ (∣-right-sem x∈) w = ∣-right-sem (f₂ x∈ w)

  final? : ℕ → ∀ {A} (g : Grammar A) → Maybe (Final-whitespace g)

  final? (suc n) fail = just (λ ())

  final? (suc n) (f <$> g) = <$>-lemma <$>M final? n (♭ g)

  final? (suc n) (g₁ ⊛ g₂) with ♭ g₂ | P.inspect ♭ g₂
  ... | return x  | P.[ eq ] = ⊛-return-lemma eq <$>M final? n (♭ g₁)
  ... | g₂₁ ⋆     | P.[ eq ] = ⊛-⋆-lemma eq <$>M final? n (♭ g₁)
                                              ⊛M final? n (♭ g₂₁)
  ... | g₂₁ ∣ g₂₂ | P.[ eq ] = ⊛-∣-lemma eq <$>M final? n (g₁ ⊛ g₂₁)
                                              ⊛M final? n (g₁ ⊛ g₂₂)
  ... | _         | _        = ⊛-lemma <$>M final? n (♭ g₂)

  final? (suc n) (g₁ <⊛ g₂) with ♭ g₂ | P.inspect ♭ g₂
  ... | return x | P.[ eq ] = <⊛-return-lemma eq <$>M final? n (♭ g₁)
  ... | _        | _        = <⊛-lemma <$>M
                                final-whitespace′? (suc n) (♭ g₂)

  final? (suc n) (g₁ ⊛> g₂) = ⊛>-lemma <$>M final? n (♭ g₂)

  final? (suc n) (g₁ ∣ g₂) = ∣-lemma <$>M final? n (♭ g₁)
                                       ⊛M final? n (♭ g₂)

  final? _ _ = nothing

private

  -- Some unit tests.

  test₁ : IsJust (final-whitespace′? 1 whitespace⋆)
  test₁ = _

  test₂ : IsJust (final-whitespace′? 2 whitespace+)
  test₂ = _

  test₃ : IsJust (final-whitespace? 1 (tt <$ whitespace⋆))
  test₃ = _

  test₄ : IsJust (final-whitespace? 2 (tt <$ whitespace+))
  test₄ = _
