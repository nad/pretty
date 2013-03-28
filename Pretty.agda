------------------------------------------------------------------------
-- Pretty-printing (documents and document combinators)
------------------------------------------------------------------------

module Pretty where

open import Data.Bool
open import Data.Char
open import Data.List hiding ([_])
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_)
open import Data.List.Properties using (module List-solver)
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Grammar.Infinite as G
  hiding (_<$>_; _<$_; _⊛_; _<⊛_; _⊛>_; token; tok; if-true; sat;
          tok-sat; symbol; list; list⁺)

------------------------------------------------------------------------
-- Pretty-printers

mutual

  -- Pretty-printer documents. If p : Doc g x, then p is a "flexible"
  -- parse tree (with respect to the grammar g) for the value x.
  --
  -- For convenience I have chosen to parametrise Doc by "extended"
  -- grammars rather than basic ones.

  infixr 20 _◇_

  data Doc : ∀ {A} → Grammar A → A → Set₁ where

    -- A string. Note that I do /not/ enforce Wadler's convention
    -- that the string does not contain newline characters. The
    -- correctness property proved below does not rely on this
    -- convention.

    text  : ∀ {s} → Doc (string s) s

    -- Concatenation.

    _◇_   : ∀ {c₁ c₂ A B x y}
              {g₁ : ∞Grammar c₁ A} {g₂ : A → ∞Grammar c₂ B} →
            Doc (♭? g₁) x → Doc (♭? (g₂ x)) y → Doc (g₁ >>= g₂) y

    -- One or more whitespace characters.

    line  : Doc (tt G.<$ whitespace +) tt

    -- Grouping construct.

    group : ∀ {A x} {g : Grammar A} → Doc g x → Doc g x

    -- Increases the nesting level. (Whatever this means. Renderers
    -- are free to ignore group and nest, see ugly-renderer below.)

    nest  : ∀ {A x} {g : Grammar A} → ℕ → Doc g x → Doc g x

    -- Embedding operator: Documents for one grammar/result also
    -- work for other grammars/results, given that the semantics
    -- are, in a certain sense, compatible.

    emb   : ∀ {A B x y} {g₁ : Grammar A} {g₂ : Grammar B} →
            (∀ {s} → x ∈ g₁ · s → y ∈ g₂ · s) →
            Doc g₁ x → Doc g₂ y

    -- Fill operator.

    fill  : ∀ {A xs} {g : Grammar A} →
            Docs g xs → Doc (g sep-by whitespace +) xs

  -- Sequences of documents, all based on the same grammar.

  data Docs {A} (g : Grammar A) : List⁺ A → Set₁ where
    [_] : ∀ {x} → Doc g x → Docs g (x ∷ [])
    _∷_ : ∀ {x xs} → Doc g x → Docs g xs → Docs g (x ∷⁺ xs)

-- Pretty-printers. A pretty-printer is a function that for every
-- value constructs a matching document.

Pretty-printer : {A : Set} → Grammar A → Set₁
Pretty-printer g = ∀ x → Doc g x

Pretty-printer-for : {A : Set} → Grammar-for A → Set₁
Pretty-printer-for g = ∀ x → Doc (g x) (x , refl)

------------------------------------------------------------------------
-- Derived document combinators

-- A "smart" variant of emb. Can be used to avoid long chains of emb
-- constructors.

embed : ∀ {A B} {g₁ : Grammar A} {g₂ : Grammar B} {x y} →
        (∀ {s} → x ∈ g₁ · s → y ∈ g₂ · s) → Doc g₁ x → Doc g₂ y
embed f (emb g d) = emb (f ∘ g) d
embed f d         = emb f d

-- A document for the empty string.

nil : ∀ {A} {x : A} → Doc (return x) x
nil = embed lemma text
  where
  lemma : ∀ {x s} → [] ∈ string [] · s → x ∈ return x · s
  lemma return-sem = return-sem

-- A document for the given character.

token : ∀ {t} → Doc G.token t
token {t} = embed lemma text
  where
  lemma′ : ∀ {x s} → x ∈ string (t ∷ []) · s → x ≡ t ∷ [] →
           t ∈ G.token · s
  lemma′ (⊛-sem (<$>-sem tok-sem) return-sem) refl = token-sem

  lemma : ∀ {s} → t ∷ [] ∈ string (t ∷ []) · s → t ∈ G.token · s
  lemma t∈ = lemma′ t∈ refl

-- A document for the given character.

tok : ∀ {t} → Doc (G.tok t) t
tok {t} = embed lemma token
  where
  lemma : ∀ {s} → t ∈ G.token · s → t ∈ G.tok t · s
  lemma token-sem = tok-sem

-- Some mapping combinators.

infix 20 <$>_ <$_

<$>_ : ∀ {c A B} {f : A → B} {x} {g : ∞Grammar c A} →
       Doc (♭? g) x → Doc (f G.<$> g) (f x)
<$> d = embed <$>-sem d

<$_ : ∀ {c A B} {x : A} {y} {g : ∞Grammar c B} →
      Doc (♭? g) y → Doc (x G.<$ g) x
<$ d = embed <$-sem d

-- Some sequencing combinators.

infixl 20 _⊛_ _<⊛_ _⊛>_ _<⊛-tt_ _tt-⊛>_

_⊛_ : ∀ {c₁ c₂ A B f x}
        {g₁ : ∞Grammar c₁ (A → B)} {g₂ : ∞Grammar c₂ A} →
      Doc (♭? g₁) f → Doc (♭? g₂) x → Doc (g₁ G.⊛ g₂) (f x)
_⊛_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (d₁ ◇ <$> d₂)
  where
  lemma : ∀ {x s} →
          x ∈ (g₁ >>= λ f → f G.<$> g₂) · s → x ∈ g₁ G.⊛ g₂ · s
  lemma (>>=-sem f∈ (<$>-sem x∈)) = ⊛-sem f∈ x∈

_<⊛_ : ∀ {c₁ c₂ A B x y} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
       Doc (♭? g₁) x → Doc (♭? g₂) y → Doc (g₁ G.<⊛ g₂) x
_<⊛_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (d₁ ◇ <$ d₂)
  where
  lemma : ∀ {x s} →
          x ∈ (g₁ >>= λ x → x G.<$ g₂) · s → x ∈ g₁ G.<⊛ g₂ · s
  lemma (>>=-sem x∈ (<$-sem y∈)) = <⊛-sem x∈ y∈

_⊛>_ : ∀ {c₁ c₂ A B x y} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
       Doc (♭? g₁) x → Doc (♭? g₂) y → Doc (g₁ G.⊛> g₂) y
_⊛>_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (d₁ ◇ d₂)
  where
  lemma : ∀ {y s} →
          y ∈ (g₁ >>= λ _ → g₂) · s → y ∈ g₁ G.⊛> g₂ · s
  lemma (>>=-sem x∈ y∈) = ⊛>-sem x∈ y∈

_<⊛-tt_ : ∀ {c₁ c₂ A B x} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
          Doc (♭? g₁) x → Doc (tt G.<$ g₂) tt → Doc (g₁ G.<⊛ g₂) x
_<⊛-tt_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (d₁ <⊛ d₂)
  where
  lemma : ∀ {x s} → x ∈ g₁ G.<⊛ (tt G.<$ g₂) · s → x ∈ g₁ G.<⊛ g₂ · s
  lemma (<⊛-sem x∈ (<$-sem y∈)) = <⊛-sem x∈ y∈

_tt-⊛>_ : ∀ {c₁ c₂ A B x} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
          Doc (tt G.<$ g₁) tt → Doc (♭? g₂) x → Doc (g₁ G.⊛> g₂) x
_tt-⊛>_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (d₁ ⊛> d₂)
  where
  lemma : ∀ {x s} → x ∈ (tt G.<$ g₁) G.⊛> g₂ · s → x ∈ g₁ G.⊛> g₂ · s
  lemma (⊛>-sem (<$-sem x∈) y∈) = ⊛>-sem x∈ y∈

-- Document combinators for choices.

left : ∀ {c₁ c₂ A x} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A} →
       Doc (♭? g₁) x → Doc (g₁ ∣ g₂) x
left d = embed left-sem d

right : ∀ {c₁ c₂ A x} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A} →
        Doc (♭? g₂) x → Doc (g₁ ∣ g₂) x
right d = embed right-sem d

-- Some Kleene star and plus combinators.

nil-⋆ : ∀ {c A} {g : ∞Grammar c A} → Doc (g ⋆) []
nil-⋆ {A = A} {g} = embed lemma nil
  where
  lemma : ∀ {s} → [] ∈ return {A = List A} [] · s → [] ∈ g ⋆ · s
  lemma return-sem = ⋆-[]-sem

cons-⋆+ : ∀ {c A} {g : ∞Grammar c A} {x xs} →
          Doc (♭? g) x → Doc (g ⋆) xs → Doc (g +) (x ∷ xs)
cons-⋆+ d₁ d₂ = <$> d₁ ⊛ d₂

cons-⋆ : ∀ {c A} {g : ∞Grammar c A} {x xs} →
         Doc (♭? g) x → Doc (g ⋆) xs → Doc (g ⋆) (x ∷ xs)
cons-⋆ d₁ d₂ = embed ⋆-+-sem (cons-⋆+ d₁ d₂)

-- A document for the empty string.

if-true : ∀ b (t : T b) → Doc (G.if-true b) t
if-true true  _  = nil
if-true false ()

-- Documents for the given character.

sat : ∀ {p : Char → Bool} {t pt} →
      Doc (G.sat p) (t , pt)
sat = token ◇ <$> if-true _ _

tok-sat : {p : Char → Bool} → Pretty-printer-for (G.tok-sat p)
tok-sat _ = <$ tok

-- A single space character.

space : Doc (whitespace ⋆) (' ' ∷ [])
space = embed lemma tok
  where
  lemma : ∀ {s} →
          ' ' ∈ G.tok ' ' · s →
          (' ' ∷ []) ∈ whitespace ⋆ · s
  lemma tok-sem = ⋆-+-sem single-space-sem

-- A variant of line (with _⋆ instead of _+ in the grammar).

line⋆ : Doc (tt G.<$ whitespace ⋆) tt
line⋆ = embed lemma line
  where
  lemma : ∀ {s} →
          tt ∈ tt G.<$ whitespace + · s →
          tt ∈ tt G.<$ whitespace ⋆ · s
  lemma (<$-sem w+) = <$-sem (⋆-+-sem w+)

-- Combinators that add a final "line" to the document, nested i
-- steps. (The grammars have to satisfy certain predicates.)

final-line′ : ∀ {A} {g : Grammar A} {x} (i : ℕ) →
              Trailing-whitespace g → Doc g x → Doc g x
final-line′ i trailing d = embed trailing (d <⊛-tt nest i line⋆)

final-line : ∀ {A} {g : Grammar A} {x} (i n : ℕ)
             {trailing : IsJust (trailing-whitespace n g)} →
             Doc g x → Doc g x
final-line i n {trailing} d =
  final-line′ i (toWitness (trailing-whitespace n _) trailing) d

-- A document for the given symbol (and no following whitespace).

symbol : ∀ {s} → Doc (G.symbol s) s
symbol = text <⊛ nil-⋆

-- A document for the given symbol plus a "line".

symbol-line : ∀ {s} → Doc (G.symbol s) s
symbol-line = final-line 0 1 symbol

-- A document for the given symbol plus a space character.

symbol-space : ∀ {s} → Doc (G.symbol s) s
symbol-space = text <⊛ space

-- A combinator for bracketed output, based on one in Wadler's "A
-- prettier printer".

bracket : ∀ {c A x s₁ s₂} {g : ∞Grammar c A} (n : ℕ) →
          {trailing : IsJust (trailing-whitespace n (♭? g))} →
          Doc (♭? g) x → Doc (G.symbol s₁ G.⊛> g G.<⊛ G.symbol s₂) x
bracket n {trailing} d =
  group (nest 2 symbol-line
           ⊛>
         final-line 0 n {trailing = trailing} (nest 2 d)
           <⊛
         symbol)

mutual

  -- Conversion of pretty-printers for elements into pretty-printers
  -- for lists.

  map⋆ : ∀ {c A} {g : ∞Grammar c A} →
         Pretty-printer (♭? g) → Pretty-printer (g ⋆)
  map⋆ p []       = nil-⋆
  map⋆ p (x ∷ xs) = embed ⋆-+-sem (map+ p (x ∷ xs))

  map+ : ∀ {c A} {g : ∞Grammar c A} →
         Pretty-printer (♭? g) → Pretty-printer (g +)
  map+ p (x ∷ xs) = cons-⋆+ (p x) (map⋆ p xs)

mutual

  -- Conversion of pretty-printers for specific elements into
  -- pretty-printers for specific lists.

  list : ∀ {A} {elem : Grammar-for A} →
         Pretty-printer-for elem →
         Pretty-printer-for (G.list elem)
  list e []       = nil
  list e (x ∷ xs) = <$> (list⁺ e (x ∷ xs))

  list⁺ : ∀ {A} {elem : Grammar-for A} →
          Pretty-printer-for elem →
          Pretty-printer-for (G.list⁺ elem)
  list⁺ e (x ∷ xs) = <$> (e x) ⊛ list e xs

-- A variant of fill. (The grammar has to satisfy a certain
-- predicate.)

fill+ : ∀ {c A} {g : ∞Grammar c A} (n : ℕ)
        {trailing : IsJust (trailing-whitespace n (♭? g))} →
        ∀ {xs} → Docs (♭? g) xs → Doc (g +) xs
fill+ {g = g} n {trailing} ds = embed lemma (fill ds)
  where
  open List-solver

  trailing! = toWitness (trailing-whitespace n (♭? g)) trailing

  lemma″ = solve 4 (λ a b c d → (a ⊕ b) ⊕ c ⊕ d ⊜ a ⊕ (b ⊕ c) ⊕ d) refl

  lemma′ : ∀ {x xs s₁ s₂} →
           x ∈ ♭? g · s₁ → xs ∈ ♭? g prec-by whitespace + · s₂ →
           x ∷ xs ∈ g + · s₁ ++ s₂
  lemma′           x∈ ⋆-[]-sem = +-sem x∈ ⋆-[]-sem
  lemma′ {s₁ = s₁} x∈ (⋆-+-sem (⊛-sem (<$>-sem (⊛>-sem w+ x′∈)) xs∈)) =
    cast (lemma″ s₁ _ _ _)
         (+-∷-sem (trailing! (<⊛-sem x∈ (⋆-+-sem w+))) (lemma′ x′∈ xs∈))

  lemma : ∀ {s xs} → xs ∈ ♭? g sep-by whitespace + · s → xs ∈ g + · s
  lemma (⊛-sem (<$>-sem x∈) xs∈) = lemma′ x∈ xs∈

-- Variants of map+/map⋆ that use fill. (The grammars have to satisfy
-- a certain predicate.)

map+-fill : ∀ {c A} {g : ∞Grammar c A} (n : ℕ)
            {trailing : IsJust (trailing-whitespace n (♭? g))} →
            Pretty-printer (♭? g) →
            Pretty-printer (g +)
map+-fill {g = g} n {trailing} p xs =
  fill+ n {trailing = trailing} (uncurry to-docs xs)
  where
  to-docs : ∀ x xs → Docs (♭? g) (x ∷ xs)
  to-docs x []        = [ p x ]
  to-docs x (x′ ∷ xs) = p x ∷ to-docs x′ xs

map⋆-fill : ∀ {c A} {g : ∞Grammar c A} (n : ℕ)
            {trailing : IsJust (trailing-whitespace n (♭? g))} →
            Pretty-printer (♭? g) →
            Pretty-printer (g ⋆)
map⋆-fill n         p []       = nil-⋆
map⋆-fill n {trailing} p (x ∷ xs) =
  embed ⋆-+-sem (map+-fill n {trailing = trailing} p (x ∷ xs))
