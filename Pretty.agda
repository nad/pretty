------------------------------------------------------------------------
-- Pretty-printing
------------------------------------------------------------------------

module Pretty where

open import Algebra
open import Coinduction
open import Data.Bool
open import Data.Char
open import Data.List as List hiding ([_])
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_)
open import Data.List.Properties using (module List-solver)
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String using () renaming (toList to str)
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

private module LM {A : Set} = Monoid (List.monoid A)

open import Grammar.Infinite
open import Tests

------------------------------------------------------------------------
-- Pretty-printers

mutual

  -- Pretty-printer documents. If p : Doc g x, then p is a decorated
  -- parse tree (with respect to the grammar g) for the value x.

  -- One could introduce a smart wrapper for embed, to avoid long
  -- chains of embed constructors. I tried this, and it didn't seem to
  -- have a large impact on the time needed to typecheck the code
  -- (including the examples).

  infixr 20 _·_

  data Doc : ∀ {A} → Grammar A → A → Set₁ where
    nil   : ∀ {A} {x : A} → Doc (return x) x
    text  : ∀ {s} → Doc (string s) s
    _·_   : ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂ : A → ∞ (Grammar B)}
              {x y} →
            Doc (♭ g₁) x → Doc (♭ (g₂ x)) y → Doc (g₁ >>= g₂) y
    line  : Doc (tt <$ whitespace+) tt
    group : ∀ {A} {g : Grammar A} {x} → Doc g x → Doc g x
    nest  : ∀ {A} {g : Grammar A} {x} → ℕ → Doc g x → Doc g x
    embed : ∀ {A B} {g₁ : Grammar A} {g₂ : Grammar B} {x y} →
            (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) → Doc g₁ x → Doc g₂ y
    fill  : ∀ {A} {g : Grammar A} {xs} →
            Docs g xs → Doc (g sep-by whitespace+) xs

  -- Sequences of documents, all based on the same grammar.

  data Docs {A} (g : Grammar A) : List⁺ A → Set₁ where
    [_] : ∀ {x} → Doc g x → Docs g (x ∷ [])
    _∷_ : ∀ {x xs} → Doc g x → Docs g xs → Docs g (x ∷⁺ xs)

-- Pretty-printers. A pretty-printer is a function that for every
-- value constructs a matching document.

Pretty-printer : {A : Set} → Grammar A → Set₁
Pretty-printer g = ∀ x → Doc g x

------------------------------------------------------------------------
-- Derived document combinators

-- A document for the given character.

token-doc : ∀ {t} → Doc token t
token-doc {t} = embed lemma text
  where
  lemma′ : ∀ {x s} → x ∈ string (t ∷ []) ∙ s → x ≡ t ∷ [] →
           t ∈ token ∙ s
  lemma′ (⊛-sem (<$>-sem tok-sem) return-sem) P.refl = token-sem

  lemma : ∀ {s} → t ∷ [] ∈ string (t ∷ []) ∙ s → t ∈ token ∙ s
  lemma t∈ = lemma′ t∈ P.refl

-- A document for the given character.

tok-doc : ∀ {t} → Doc (tok t) t
tok-doc {t} = embed lemma token-doc
  where
  lemma : ∀ {s} → t ∈ token ∙ s → t ∈ tok t ∙ s
  lemma token-sem = tok-sem

-- A combinator corresponding to "map".

<$>-doc : ∀ {A B : Set} {f : A → B} {x g} →
          Doc (♭ g) x → Doc (f <$> g) (f x)
<$>-doc d = embed <$>-sem d

-- Some sequencing combinators.

infixl 20 _⊛-doc_ _<⊛-doc_ _⊛>-doc_

_⊛-doc_ : ∀ {A B g₁ g₂} {f : A → B} {x} →
          Doc (♭ g₁) f → Doc (♭ g₂) x → Doc (g₁ ⊛ g₂) (f x)
_⊛-doc_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (d₁ · <$>-doc d₂)
  where
  lemma : ∀ {x s} → x ∈ (♭ g₁ >>=′ λ f → f <$> g₂) ∙ s → x ∈ g₁ ⊛ g₂ ∙ s
  lemma (>>=-sem f∈ (<$>-sem x∈)) = ⊛-sem f∈ x∈

_<⊛-doc_ : ∀ {A B g₁ g₂} {x : A} {y : B} →
           Doc (♭ g₁) x → Doc (♭ g₂) y → Doc (g₁ <⊛ g₂) x
_<⊛-doc_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (nil ⊛-doc d₁ ⊛-doc d₂)
  where
  lemma : ∀ {x s} →
          x ∈ return (λ x _ → x) ⊛′ ♭ g₁ ⊛′ ♭ g₂ ∙ s → x ∈ g₁ <⊛ g₂ ∙ s
  lemma (⊛-sem (⊛-sem return-sem x∈) y∈) = <⊛-sem x∈ y∈

_⊛>-doc_ : ∀ {A B g₁ g₂} {x : A} {y : B} →
           Doc (♭ g₁) x → Doc (♭ g₂) y → Doc (g₁ ⊛> g₂) y
_⊛>-doc_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (nil ⊛-doc d₁ ⊛-doc d₂)
  where
  lemma : ∀ {y s} →
          y ∈ return (λ _ x → x) ⊛′ ♭ g₁ ⊛′ ♭ g₂ ∙ s → y ∈ g₁ ⊛> g₂ ∙ s
  lemma (⊛-sem (⊛-sem return-sem x∈) y∈) = ⊛>-sem x∈ y∈

<$-doc : ∀ {A B : Set} {x : A} {y : B} {g} →
         Doc g y → Doc (x <$ g) x
<$-doc d = nil <⊛-doc d

-- Document combinators for choices.

∣-left-doc : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x} →
             Doc (♭ g₁) x → Doc (g₁ ∣ g₂) x
∣-left-doc d = embed ∣-left-sem d

∣-right-doc : ∀ {A} {g₁ g₂ : ∞ (Grammar A)} {x} →
              Doc (♭ g₂) x → Doc (g₁ ∣ g₂) x
∣-right-doc d = embed ∣-right-sem d

-- Some Kleene star and plus combinators.

[]-doc : ∀ {A} {g : ∞ (Grammar A)} → Doc (g ⋆) []
[]-doc {A} {g} = embed lemma nil
  where
  lemma : ∀ {s} → [] ∈ return {A = List A} [] ∙ s → [] ∈ g ⋆ ∙ s
  lemma return-sem = ⋆-[]-sem

infixr 20 _+-∷-⋆-doc_ _⋆-∷-doc_

_+-∷-⋆-doc_ : ∀ {A} {g : ∞ (Grammar A)} {x xs} →
              Doc (♭ g) x → Doc (g ⋆) xs → Doc (g +) (x ∷ xs)
d₁ +-∷-⋆-doc d₂ = <$>-doc d₁ ⊛-doc d₂

_⋆-∷-doc_ : ∀ {A} {g : ∞ (Grammar A)} {x xs} →
            Doc (♭ g) x → Doc (g ⋆) xs → Doc (g ⋆) (x ∷ xs)
d₁ ⋆-∷-doc d₂ = embed ⋆-+-sem (d₁ +-∷-⋆-doc d₂)

-- A document for the empty string.

if-true-doc : ∀ {b} {t : T b} → Doc (if-true b) t
if-true-doc {true}     = nil
if-true-doc {false} {}

-- A document for the given character.

sat-doc : ∀ {p : Char → Bool} {t pt} →
          Doc (sat p) (t , pt)
sat-doc = token-doc · <$>-doc if-true-doc

-- A variant of line (with _⋆ instead of _+ in the grammar).

line⋆ : Doc (tt <$ whitespace⋆) tt
line⋆ = embed lemma line
  where
  lemma : ∀ {s} →
          tt ∈ tt <$ whitespace+ ∙ s →
          tt ∈ tt <$ whitespace⋆ ∙ s
  lemma (<⊛-sem return-sem w+) = <⊛-sem return-sem (⋆-+-sem w+)

-- Adds a final "line" combinator to the document. (The grammar has to
-- satisfy a certain predicate.)

final-line : ∀ {A} {g : Grammar A} {x} (n : ℕ)
             {final : IsJust (final-whitespace? n g)} →
             Doc g x → Doc g x
final-line {g = g} n {final} d = embed lemma (d <⊛-doc line⋆)
  where
  lemma : ∀ {x s} → x ∈ g <⊛′ tt <$ whitespace⋆ ∙ s → x ∈ g ∙ s
  lemma (<⊛-sem x∈ (<⊛-sem return-sem white)) =
    toWitness (final-whitespace? n g) final x∈ white

-- A document for the given symbol (and no following whitespace).

symbol-doc : ∀ {s} → Doc (symbol s) s
symbol-doc = text <⊛-doc []-doc

-- A document for the given symbol plus a "line".

symbol-line-doc : ∀ {s} → Doc (symbol s) s
symbol-line-doc = final-line 1 symbol-doc

-- A combinator for bracketed output, based on one in Wadler's "A
-- prettier printer".

bracket : ∀ {A g₁ g₂ g₃ g₁₂ s₁ s₂} {x : A} (n : ℕ) →
          ♭ g₁  ≡ symbol s₁ →
          ♭ g₁₂ ≡ g₁ ⊛> g₂ →
          ♭ g₃  ≡ symbol s₂ →
          {final : IsJust (final-whitespace? n (♭ g₂))} →
          Doc (♭ g₂) x → Doc (g₁₂ <⊛ g₃) x
bracket {g₂ = g₂} {g₃} {g₁₂} {s₁} {s₂} n eq₁ eq₂ eq₃ {final} d =
  group
    (embed lemma₁
       (nest 2 symbol-line-doc
          ⊛>-doc
        final-line n {final = final} (nest 2 d))
       <⊛-doc
     embed lemma₂ symbol-doc)
  where
  lemma₁ : ∀ {x s} → x ∈ symbol s₁ ⊛>′ ♭ g₂ ∙ s → x ∈ ♭ g₁₂ ∙ s
  lemma₁ (⊛>-sem s₁∈ x∈) rewrite eq₂ =
    ⊛>-sem (cast (P.sym eq₁) refl s₁∈) x∈

  lemma₂ : ∀ {x s} → x ∈ symbol s₂ ∙ s → x ∈ ♭ g₃ ∙ s
  lemma₂ s₂∈ rewrite eq₃ = s₂∈

mutual

  -- Converts pretty-printers for elements into pretty-printers for
  -- lists.

  map⋆-doc : {A : Set} {g : ∞ (Grammar A)} →
            Pretty-printer (♭ g) → Pretty-printer (g ⋆)
  map⋆-doc p []       = []-doc
  map⋆-doc p (x ∷ xs) = embed ⋆-+-sem (map+-doc p (x ∷ xs))

  map+-doc : {A : Set} {g : ∞ (Grammar A)} →
             Pretty-printer (♭ g) → Pretty-printer (g +)
  map+-doc p (x ∷ xs) = p x +-∷-⋆-doc map⋆-doc p xs

-- A variant of fill. (The grammar has to satisfy a certain
-- predicate.)

fill+ : ∀ {A} {g : ∞ (Grammar A)} (n : ℕ)
        {final : IsJust (final-whitespace? n (♭ g))} →
        ∀ {xs} → Docs (♭ g) xs → Doc (g +) xs
fill+ {g = g} n {final} ds = embed lemma (fill ds)
  where
  open List-solver

  final! = toWitness (final-whitespace? n (♭ g)) final

  lemma″ = solve 4 (λ a b c d → (a ⊕ b) ⊕ c ⊕ d ⊜ a ⊕ (b ⊕ c) ⊕ d) refl

  lemma′ : ∀ {x xs s₁ s₂} →
           x ∈ ♭ g ∙ s₁ → xs ∈ ♭ g prec-by whitespace+ ∙ s₂ →
           x ∷ xs ∈ g + ∙ s₁ ++ s₂
  lemma′           x∈ ⋆-[]-sem = +-sem x∈ ⋆-[]-sem
  lemma′ {s₁ = s₁} x∈ (⋆-+-sem (⊛-sem (<$>-sem (⊛>-sem w+ x′∈)) xs∈)) =
    cast refl (lemma″ s₁ _ _ _)
         (+-∷-sem (final! x∈ (⋆-+-sem w+)) (lemma′ x′∈ xs∈))

  lemma : ∀ {s xs} → xs ∈ ♭ g sep-by whitespace+ ∙ s → xs ∈ g + ∙ s
  lemma (⊛-sem (<$>-sem x∈) xs∈) = lemma′ x∈ xs∈

-- Variants of map+-doc/map⋆-doc that use fill. (The grammars have to
-- satisfy a certain predicate.)

map+-fill-doc : ∀ {A} {g : ∞ (Grammar A)} (n : ℕ)
                {final : IsJust (final-whitespace? n (♭ g))} →
                Pretty-printer (♭ g) →
                Pretty-printer (g +)
map+-fill-doc {g = g} n {final} p xs =
  fill+ n {final = final} (uncurry to-docs xs)
  where
  to-docs : ∀ x xs → Docs (♭ g) (x ∷ xs)
  to-docs x []        = [ p x ]
  to-docs x (x′ ∷ xs) = p x ∷ to-docs x′ xs

map⋆-fill-doc : ∀ {A} {g : ∞ (Grammar A)} (n : ℕ)
                {final : IsJust (final-whitespace? n (♭ g))} →
                Pretty-printer (♭ g) →
                Pretty-printer (g ⋆)
map⋆-fill-doc n         p []       = []-doc
map⋆-fill-doc n {final} p (x ∷ xs) =
  embed ⋆-+-sem (map+-fill-doc n {final = final} p (x ∷ xs))

------------------------------------------------------------------------
-- Document renderers

record Renderer : Set₁ where
  field
    -- The function that renders.

    render : ∀ {A} {g : Grammar A} {x} → Doc g x → List Char

    -- The rendered string must be parsable.

    parsable : ∀ {A} {g : Grammar A} {x}
               (d : Doc g x) → x ∈ g ∙ render d

  -- Pretty-printers are correct by definition, for any renderer,
  -- assuming that the underlying grammar is unambiguous.

  pretty-printer-correct :
    ∀ {A} {g : Grammar A} (pretty : Pretty-printer g) →
    ∀ x → x ∈ g ∙ render (pretty x)
  pretty-printer-correct pretty x = parsable (pretty x)

-- An example renderer.

ugly-renderer : Renderer
ugly-renderer = record
  { render   = render
  ; parsable = parsable
  }
  where

  mutual

    render : ∀ {A} {g : Grammar A} {x} → Doc g x → List Char
    render nil            = []
    render (text {s = s}) = s
    render (d₁ · d₂)      = render d₁ ++ render d₂
    render line           = str " "
    render (group d)      = render d
    render (nest _ d)     = render d
    render (embed _ d)    = render d
    render (fill ds)      = render-fills ds

    render-fills : ∀ {A} {g : Grammar A} {x} → Docs g x → List Char
    render-fills [ d ]    = render d
    render-fills (d ∷ ds) = render d ++ ' ' ∷ render-fills ds

  mutual

    parsable : ∀ {A x} {g : Grammar A}
               (d : Doc g x) → x ∈ g ∙ render d
    parsable nil         = return-sem
    parsable text        = string-sem
    parsable (d₁ · d₂)   = >>=-sem (parsable d₁) (parsable d₂)
    parsable line        = <$-sem single-space-sem
    parsable (group d)   = parsable d
    parsable (nest _ d)  = parsable d
    parsable (embed f d) = f (parsable d)
    parsable (fill ds)   = parsable-fills ds

    parsable-fills : ∀ {A xs} {g : Grammar A} (ds : Docs g xs) →
                     xs ∈ g sep-by whitespace+ ∙ render-fills ds
    parsable-fills [ d ]    = sep-by-sem-singleton (parsable d)
    parsable-fills (d ∷ ds) =
      sep-by-sem-∷ (parsable d) single-space-sem (parsable-fills ds)

-- An example renderer, based on the one in Wadler's "A prettier
-- printer".
--
-- The natural number is the line width.

wadler's-renderer : ℕ → Renderer
wadler's-renderer w = record
  { render   = render
  ; parsable = parsable
  }
  where

  -- Documents with unions instead of groups, and no fills.

  infixr 20 _·_

  data DocU : ∀ {A} → Grammar A → A → Set₁ where
    nil   : ∀ {A} {x : A} → DocU (return x) x
    text  : ∀ {s} → DocU (string s) s
    _·_   : ∀ {A B} {g₁ : ∞ (Grammar A)} {g₂ : A → ∞ (Grammar B)}
              {x y} →
            DocU (♭ g₁) x → DocU (♭ (g₂ x)) y → DocU (g₁ >>= g₂) y
    line  : DocU (tt <$ whitespace+) tt
    union : ∀ {A} {g : Grammar A} {x} → DocU g x → DocU g x → DocU g x
    nest  : ∀ {A} {g : Grammar A} {x} → ℕ → DocU g x → DocU g x
    embed : ∀ {A B} {g₁ : Grammar A} {g₂ : Grammar B} {x y} →
            (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) → DocU g₁ x → DocU g₂ y

  -- Some derived combinators.

  infixl 20 _⊛-docU_ _<⊛-docU_ _⊛>-docU_

  <$>-docU : ∀ {A B : Set} {f : A → B} {x g} →
             DocU (♭ g) x → DocU (f <$> g) (f x)
  <$>-docU d = embed <$>-sem d

  _⊛-docU_ : ∀ {A B g₁ g₂} {f : A → B} {x} →
             DocU (♭ g₁) f → DocU (♭ g₂) x → DocU (g₁ ⊛ g₂) (f x)
  _⊛-docU_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (d₁ · <$>-docU d₂)
    where
    lemma : ∀ {x s} →
            x ∈ (♭ g₁ >>=′ λ f → f <$> g₂) ∙ s → x ∈ g₁ ⊛ g₂ ∙ s
    lemma (>>=-sem f∈ (<$>-sem x∈)) = ⊛-sem f∈ x∈

  _<⊛-docU_ : ∀ {A B g₁ g₂} {x : A} {y : B} →
              DocU (♭ g₁) x → DocU (♭ g₂) y → DocU (g₁ <⊛ g₂) x
  _<⊛-docU_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (nil ⊛-docU d₁ ⊛-docU d₂)
    where
    lemma : ∀ {x s} →
            x ∈ return (λ x _ → x) ⊛′ ♭ g₁ ⊛′ ♭ g₂ ∙ s →
            x ∈ g₁ <⊛ g₂ ∙ s
    lemma (⊛-sem (⊛-sem return-sem x∈) y∈) = <⊛-sem x∈ y∈

  _⊛>-docU_ : ∀ {A B g₁ g₂} {x : A} {y : B} →
              DocU (♭ g₁) x → DocU (♭ g₂) y → DocU (g₁ ⊛> g₂) y
  _⊛>-docU_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (nil ⊛-docU d₁ ⊛-docU d₂)
    where
    lemma : ∀ {y s} →
            y ∈ return (λ _ x → x) ⊛′ ♭ g₁ ⊛′ ♭ g₂ ∙ s →
            y ∈ g₁ ⊛> g₂ ∙ s
    lemma (⊛-sem (⊛-sem return-sem x∈) y∈) = ⊛>-sem x∈ y∈

  <$-docU : ∀ {A B : Set} {x : A} {y : B} {g} →
            DocU g y → DocU (x <$ g) x
  <$-docU d = nil <⊛-docU d

  cons : ∀ {A B} {g : Grammar A} {sep : Grammar B} {x xs} →
         DocU g x → DocU (tt <$ sep) tt → DocU (g sep-by sep) xs →
         DocU (g sep-by sep) (x ∷⁺ xs)
  cons {g = g} {sep} d₁ d₂ d₃ =
    embed lemma (<$>-docU d₁ ⊛-docU (d₂ ⊛>-docU d₃))
    where
    lemma : ∀ {ys s} →
            ys ∈ _∷⁺_ <$>′ g ⊛′ ((tt <$ sep) ⊛>′ (g sep-by sep)) ∙ s →
            ys ∈ g sep-by sep ∙ s
    lemma (⊛-sem (<$>-sem x∈) (⊛>-sem (<⊛-sem return-sem y∈) xs∈)) =
      sep-by-sem-∷ x∈ y∈ xs∈

  -- A single space character.

  space : DocU (tt <$ whitespace+) tt
  space = embed lemma (<$-docU text)
    where
    lemma : ∀ {s} →
            tt ∈ tt <$ string (str " ") ∙ s →
            tt ∈ tt <$ whitespace+ ∙ s
    lemma (<⊛-sem return-sem (⊛-sem (<$>-sem tok-sem) return-sem)) =
      <$-sem single-space-sem

  mutual

    -- Replaces line constructors with single spaces, removes groups.

    flatten : ∀ {A} {g : Grammar A} {x} → Doc g x → DocU g x
    flatten nil         = nil
    flatten text        = text
    flatten (d₁ · d₂)   = flatten d₁ · flatten d₂
    flatten line        = space
    flatten (group d)   = flatten d
    flatten (nest i d)  = nest i (flatten d)
    flatten (embed f d) = embed f (flatten d)
    flatten (fill ds)   = flatten-fills ds

    flatten-fills : ∀ {A} {g : Grammar A} {xs} →
                    Docs g xs → DocU (g sep-by whitespace+) xs
    flatten-fills [ d ]    = embed sep-by-sem-singleton (flatten d)
    flatten-fills (d ∷ ds) = cons (flatten d) space (flatten-fills ds)

  mutual

    -- Conversion of Docs to DocUs.

    expand-groups : ∀ {A} {g : Grammar A} {x} → Doc g x → DocU g x
    expand-groups nil         = nil
    expand-groups text        = text
    expand-groups (d₁ · d₂)   = expand-groups d₁ · expand-groups d₂
    expand-groups line        = line
    expand-groups (group d)   = union (flatten d) (expand-groups d)
    expand-groups (nest i d)  = nest i (expand-groups d)
    expand-groups (embed f d) = embed f (expand-groups d)
    expand-groups (fill ds)   = expand-fills false ds

    expand-fills : Bool → -- Unconditionally flatten the first document?
                   ∀ {A} {g : Grammar A} {xs} →
                   Docs g xs → DocU (g sep-by whitespace+) xs
    expand-fills fl [ d ] =
      embed sep-by-sem-singleton (flatten/expand fl d)
    expand-fills fl (d ∷ ds) =
      union (cons (flatten d)           space (expand-fills true  ds))
            (cons (flatten/expand fl d) line  (expand-fills false ds))

    flatten/expand : Bool → -- Flatten?
                     ∀ {A} {g : Grammar A} {x} → Doc g x → DocU g x
    flatten/expand true  d = flatten d
    flatten/expand false d = expand-groups d

  -- Layouts (representations of certain strings).

  data Layout-element : Set where
    text      : List Char → Layout-element
    nest-line : ℕ         → Layout-element

  Layout : Set
  Layout = List Layout-element

  -- Conversion of layouts into strings.

  showE : Layout-element → List Char
  showE (text s)      = s
  showE (nest-line i) = '\n' ∷ replicate i ' '

  show : Layout → List Char
  show = concat ∘ List.map showE

  mutual

    -- Does the first line of the layout fit inside a row with the
    -- given number of characters?

    fits : ℕ → Layout → Bool
    fits w []                = true
    fits w (text s      ∷ x) = fits′ w (length s) x
    fits w (nest-line i ∷ x) = true

    fits′ : ℕ → ℕ → Layout → Bool
    fits′ w c x = not (w <?ℕ c) ∧ fits (w ∸ c) x

  -- Chooses the first layout if it fits, otherwise the second (which
  -- is assumed to have a first line that is at most as long as the
  -- first line of the first layout). The natural number is the
  -- current column number.

  better : ℕ → Layout → Layout → Layout
  better c x y = if fits′ w c x then x else y

  -- If, for any starting column c, κ c is the layout for some text,
  -- then best i d κ c is the layout for the document d followed by
  -- this text, given the current indentation i and the current column
  -- number c.

  best : ∀ {A} {g : Grammar A} {x} →
         ℕ → DocU g x → (ℕ → Layout) → (ℕ → Layout)
  best i nil            = id
  best i (text {s = s}) = λ κ c → text s ∷ κ (length s + c)
  best i (d₁ · d₂)      = best i d₁ ∘ best i d₂
  best i line           = λ κ _ → nest-line i ∷ κ i
  best i (union d₁ d₂)  = λ κ c → better c (best i d₁ κ c)
                                           (best i d₂ κ c)
  best i (nest j d)     = best (j + i) d
  best i (embed _ d)    = best i d

  -- Renders a document.

  render : ∀ {A} {g : Grammar A} {x} → Doc g x → List Char
  render d = show (best 0 (expand-groups d) (λ _ → []) 0)

  -- Some simple lemmas.

  replicate-lemma :
    ∀ i → replicate i ' ' ∈ whitespace⋆ ∙ replicate i ' '
  replicate-lemma zero    = ⋆-[]-sem
  replicate-lemma (suc i) =
    ⋆-∷-sem (∣-left-sem tok-sem) (replicate-lemma i)

  nest-line-lemma :
    ∀ {A} {x : A} i →
    x ∈ x <$ whitespace+ ∙ showE (nest-line i)
  nest-line-lemma i =
    <$-sem (+-sem (∣-right-sem tok-sem) (replicate-lemma i))

  if-lemma :
    ∀ {A} {g : Grammar A} {x l₁ l₂} s b →
    x ∈ g ∙ s ++ show l₁ →
    x ∈ g ∙ s ++ show l₂ →
    x ∈ g ∙ s ++ show (if b then l₁ else l₂)
  if-lemma _ true  ∈l₁ ∈l₂ = ∈l₁
  if-lemma _ false ∈l₁ ∈l₂ = ∈l₂

  -- The main correctness property for best.

  best-lemma :
    ∀ {A B} {g : Grammar A} {g′ : Grammar B} {x y c κ}
      s (d : DocU g x) {i} →
    (∀ {s′ c′} → x ∈ g ∙ s′ → y ∈ g′ ∙ s ++ s′ ++ show (κ c′)) →
    y ∈ g′ ∙ s ++ show (best i d κ c)
  best-lemma s nil           hyp = hyp return-sem
  best-lemma s text          hyp = hyp string-sem
  best-lemma s line {i}      hyp = hyp (nest-line-lemma i)
  best-lemma s (union d₁ d₂) hyp = if-lemma s
                                     (fits′ w _ (best _ d₁ _ _))
                                     (best-lemma s d₁ hyp)
                                     (best-lemma s d₂ hyp)
  best-lemma s (nest j d)    hyp = best-lemma s d hyp
  best-lemma s (embed f d)   hyp = best-lemma s d (hyp ∘ f)
  best-lemma s (d₁ · d₂)     hyp =
    best-lemma s d₁ λ {s′} f∈ →
      cast refl (LM.assoc s _ _)
        (best-lemma (s ++ s′) d₂ λ x∈ →
           cast refl (lemma s _ _ _)
             (hyp (>>=-sem f∈ x∈)))
    where
    open List-solver
    lemma = solve 4 (λ a b c d → a ⊕ (b ⊕ c) ⊕ d ⊜ (a ⊕ b) ⊕ c ⊕ d) refl

  -- The renderer is correct.

  parsable : ∀ {A} {g : Grammar A} {x}
             (d : Doc g x) → x ∈ g ∙ render d
  parsable d = best-lemma [] (expand-groups d)
                          (cast refl (P.sym $ proj₂ LM.identity _))
