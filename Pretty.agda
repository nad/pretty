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

open import Grammar.Infinite

------------------------------------------------------------------------
-- Pretty-printers

mutual

  -- Pretty-printer documents. If p : Doc g x, then p is a decorated
  -- parse tree (with respect to the grammar g) for the value x.
  --
  -- For convenience I have chosen to parametrise Doc by "extended"
  -- grammars rather than basic ones.

  infixr 20 _·_

  data Doc : ∀ {A} → Grammar A → A → Set₁ where

    -- The empty string. (This constructor could be removed.)

    nil   : ∀ {A} {x : A} → Doc (return x) x

    -- A string. Note that I do /not/ enforce Wadler's convention
    -- that the string does not contain newline characters. The
    -- correctness property proved below does not rely on this
    -- convention.

    text  : ∀ {s} → Doc (string s) s

    -- Concatenation.

    _·_   : ∀ {c₁ c₂ A B x y}
              {g₁ : ∞Grammar c₁ A} {g₂ : A → ∞Grammar c₂ B} →
            Doc (♭? g₁) x → Doc (♭? (g₂ x)) y → Doc (g₁ >>= g₂) y

    -- One or more whitespace characters.

    line  : Doc (tt <$ whitespace +) tt

    -- Grouping construct.

    group : ∀ {A x} {g : Grammar A} → Doc g x → Doc g x

    -- Increases the nesting level. (Whatever this means. Renderers
    -- are free to ignore group and nest, see ugly-renderer below.)

    nest  : ∀ {A x} {g : Grammar A} → ℕ → Doc g x → Doc g x

    -- Embedding operator: Documents for one grammar/result also
    -- work for other grammars/results, given that the semantics
    -- are, in a certain sense, compatible.

    emb   : ∀ {A B x y} {g₁ : Grammar A} {g₂ : Grammar B} →
            (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) →
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
        (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) → Doc g₁ x → Doc g₂ y
embed f (emb g d) = emb (f ∘ g) d
embed f d         = emb f d

-- A document for the given character.

token-doc : ∀ {t} → Doc token t
token-doc {t} = embed lemma text
  where
  lemma′ : ∀ {x s} → x ∈ string (t ∷ []) ∙ s → x ≡ t ∷ [] →
           t ∈ token ∙ s
  lemma′ (⊛-sem (<$>-sem tok-sem) return-sem) refl = token-sem

  lemma : ∀ {s} → t ∷ [] ∈ string (t ∷ []) ∙ s → t ∈ token ∙ s
  lemma t∈ = lemma′ t∈ refl

-- A document for the given character.

tok-doc : ∀ {t} → Doc (tok t) t
tok-doc {t} = embed lemma token-doc
  where
  lemma : ∀ {s} → t ∈ token ∙ s → t ∈ tok t ∙ s
  lemma token-sem = tok-sem

-- A combinator corresponding to "map".

<$>-doc : ∀ {c A B} {f : A → B} {x} {g : ∞Grammar c A} →
          Doc (♭? g) x → Doc (f <$> g) (f x)
<$>-doc d = embed <$>-sem d

-- Some sequencing combinators.

infixl 20 _⊛-doc_ _<⊛-doc_ _⊛>-doc_

_⊛-doc_ : ∀ {c₁ c₂ A B f x} {g₁ : ∞Grammar c₁ (A → B)}
            {g₂ : ∞Grammar c₂ A} →
          Doc (♭? g₁) f → Doc (♭? g₂) x → Doc (g₁ ⊛ g₂) (f x)
_⊛-doc_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (d₁ · <$>-doc d₂)
  where
  lemma : ∀ {x s} → x ∈ (g₁ >>= λ f → f <$> g₂) ∙ s → x ∈ g₁ ⊛ g₂ ∙ s
  lemma (>>=-sem f∈ (<$>-sem x∈)) = ⊛-sem f∈ x∈

_<⊛-doc_ : ∀ {c₁ c₂ A B x y} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
           Doc (♭? g₁) x → Doc (♭? g₂) y → Doc (g₁ <⊛ g₂) x
_<⊛-doc_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (nil ⊛-doc d₁ ⊛-doc d₂)
  where
  lemma : ∀ {x s} →
          x ∈ return (λ x _ → x) ⊛ g₁ ⊛ g₂ ∙ s → x ∈ g₁ <⊛ g₂ ∙ s
  lemma (⊛-sem (⊛-sem return-sem x∈) y∈) = <⊛-sem x∈ y∈

_⊛>-doc_ : ∀ {c₁ c₂ A B x y} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ B} →
           Doc (♭? g₁) x → Doc (♭? g₂) y → Doc (g₁ ⊛> g₂) y
_⊛>-doc_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (nil ⊛-doc d₁ ⊛-doc d₂)
  where
  lemma : ∀ {y s} →
          y ∈ return (λ _ x → x) ⊛ g₁ ⊛ g₂ ∙ s → y ∈ g₁ ⊛> g₂ ∙ s
  lemma (⊛-sem (⊛-sem return-sem x∈) y∈) = ⊛>-sem x∈ y∈

<$-doc : ∀ {A B : Set} {x : A} {y : B} {g} →
         Doc g y → Doc (x <$ g) x
<$-doc d = nil <⊛-doc d

-- Document combinators for choices.

∣-left-doc : ∀ {c₁ c₂ A x} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A} →
             Doc (♭? g₁) x → Doc (g₁ ∣ g₂) x
∣-left-doc d = embed ∣-left-sem d

∣-right-doc : ∀ {c₁ c₂ A x} {g₁ : ∞Grammar c₁ A} {g₂ : ∞Grammar c₂ A} →
              Doc (♭? g₂) x → Doc (g₁ ∣ g₂) x
∣-right-doc d = embed ∣-right-sem d

-- Some Kleene star and plus combinators.

[]-doc : ∀ {c A} {g : ∞Grammar c A} → Doc (g ⋆) []
[]-doc {A = A} {g} = embed lemma nil
  where
  lemma : ∀ {s} → [] ∈ return {A = List A} [] ∙ s → [] ∈ g ⋆ ∙ s
  lemma return-sem = ⋆-[]-sem

infixr 20 _+-∷-⋆-doc_ _⋆-∷-doc_

_+-∷-⋆-doc_ : ∀ {c A} {g : ∞Grammar c A} {x xs} →
              Doc (♭? g) x → Doc (g ⋆) xs → Doc (g +) (x ∷ xs)
d₁ +-∷-⋆-doc d₂ = <$>-doc d₁ ⊛-doc d₂

_⋆-∷-doc_ : ∀ {c A} {g : ∞Grammar c A} {x xs} →
            Doc (♭? g) x → Doc (g ⋆) xs → Doc (g ⋆) (x ∷ xs)
d₁ ⋆-∷-doc d₂ = embed ⋆-+-sem (d₁ +-∷-⋆-doc d₂)

-- A document for the empty string.

if-true-doc : ∀ {b} {t : T b} → Doc (if-true b) t
if-true-doc {true}     = nil
if-true-doc {false} {}

-- Documents for the given character.

sat-doc : ∀ {p : Char → Bool} {t pt} →
          Doc (sat p) (t , pt)
sat-doc = token-doc · <$>-doc if-true-doc

tok-sat-doc : {p : Char → Bool} → Pretty-printer-for (tok-sat p)
tok-sat-doc _ = <$-doc tok-doc

-- A single space character.

space-doc : Doc (whitespace ⋆) (' ' ∷ [])
space-doc = embed lemma tok-doc
  where
  lemma : ∀ {s} →
          ' ' ∈ tok ' ' ∙ s →
          (' ' ∷ []) ∈ whitespace ⋆ ∙ s
  lemma tok-sem = ⋆-+-sem single-space-sem

-- A variant of line (with _⋆ instead of _+ in the grammar).

line⋆ : Doc (tt <$ whitespace ⋆) tt
line⋆ = embed lemma line
  where
  lemma : ∀ {s} →
          tt ∈ tt <$ whitespace + ∙ s →
          tt ∈ tt <$ whitespace ⋆ ∙ s
  lemma (<⊛-sem return-sem w+) = <⊛-sem return-sem (⋆-+-sem w+)

-- Combinators that add a final "line" to the document, nested i
-- steps. (The grammars have to satisfy certain predicates.)

final-line′ : ∀ {A} {g : Grammar A} {x} (i : ℕ) →
              Final-whitespace g → Doc g x → Doc g x
final-line′ {g = g} i final d = embed lemma (d <⊛-doc nest i line⋆)
  where
  lemma : ∀ {x s} → x ∈ g <⊛ (tt <$ whitespace ⋆) ∙ s → x ∈ g ∙ s
  lemma (<⊛-sem x∈ (<⊛-sem return-sem white)) = final x∈ white

final-line : ∀ {A} {g : Grammar A} {x} (i n : ℕ)
             {final : IsJust (final-whitespace? n g)} →
             Doc g x → Doc g x
final-line i n {final} d =
  final-line′ i (toWitness (final-whitespace? n _) final) d

-- A document for the given symbol (and no following whitespace).

symbol-doc : ∀ {s} → Doc (symbol s) s
symbol-doc = text <⊛-doc []-doc

-- A document for the given symbol plus a "line".

symbol-line-doc : ∀ {s} → Doc (symbol s) s
symbol-line-doc = final-line 0 1 symbol-doc

-- A document for the given symbol plus a space character.

symbol-space-doc : ∀ {s} → Doc (symbol s) s
symbol-space-doc = text <⊛-doc space-doc

-- A combinator for bracketed output, based on one in Wadler's "A
-- prettier printer".

bracket : ∀ {c A x s₁ s₂} {g : ∞Grammar c A} (n : ℕ) →
          {final : IsJust (final-whitespace? n (♭? g))} →
          Doc (♭? g) x → Doc (symbol s₁ ⊛> g <⊛ symbol s₂) x
bracket n {final} d =
  group (nest 2 symbol-line-doc
           ⊛>-doc
         final-line 0 n {final = final} (nest 2 d)
           <⊛-doc
         symbol-doc)

mutual

  -- Conversion of pretty-printers for elements into pretty-printers
  -- for lists.

  map⋆-doc : ∀ {c A} {g : ∞Grammar c A} →
            Pretty-printer (♭? g) → Pretty-printer (g ⋆)
  map⋆-doc p []       = []-doc
  map⋆-doc p (x ∷ xs) = embed ⋆-+-sem (map+-doc p (x ∷ xs))

  map+-doc : ∀ {c A} {g : ∞Grammar c A} →
             Pretty-printer (♭? g) → Pretty-printer (g +)
  map+-doc p (x ∷ xs) = p x +-∷-⋆-doc map⋆-doc p xs

mutual

  -- Conversion of pretty-printers for specific elements into
  -- pretty-printers for specific lists.

  list-doc : ∀ {A} {elem : Grammar-for A} →
             Pretty-printer-for elem →
             Pretty-printer-for (list elem)
  list-doc e []       = nil
  list-doc e (x ∷ xs) = <$>-doc (list⁺-doc e (x ∷ xs))

  list⁺-doc : ∀ {A} {elem : Grammar-for A} →
              Pretty-printer-for elem →
              Pretty-printer-for (list⁺ elem)
  list⁺-doc e (x ∷ xs) = <$>-doc (e x) ⊛-doc list-doc e xs

-- A variant of fill. (The grammar has to satisfy a certain
-- predicate.)

fill+ : ∀ {c A} {g : ∞Grammar c A} (n : ℕ)
        {final : IsJust (final-whitespace? n (♭? g))} →
        ∀ {xs} → Docs (♭? g) xs → Doc (g +) xs
fill+ {g = g} n {final} ds = embed lemma (fill ds)
  where
  open List-solver

  final! = toWitness (final-whitespace? n (♭? g)) final

  lemma″ = solve 4 (λ a b c d → (a ⊕ b) ⊕ c ⊕ d ⊜ a ⊕ (b ⊕ c) ⊕ d) refl

  lemma′ : ∀ {x xs s₁ s₂} →
           x ∈ ♭? g ∙ s₁ → xs ∈ ♭? g prec-by whitespace + ∙ s₂ →
           x ∷ xs ∈ g + ∙ s₁ ++ s₂
  lemma′           x∈ ⋆-[]-sem = +-sem x∈ ⋆-[]-sem
  lemma′ {s₁ = s₁} x∈ (⋆-+-sem (⊛-sem (<$>-sem (⊛>-sem w+ x′∈)) xs∈)) =
    cast (lemma″ s₁ _ _ _)
         (+-∷-sem (final! x∈ (⋆-+-sem w+)) (lemma′ x′∈ xs∈))

  lemma : ∀ {s xs} → xs ∈ ♭? g sep-by whitespace + ∙ s → xs ∈ g + ∙ s
  lemma (⊛-sem (<$>-sem x∈) xs∈) = lemma′ x∈ xs∈

-- Variants of map+-doc/map⋆-doc that use fill. (The grammars have to
-- satisfy a certain predicate.)

map+-fill-doc : ∀ {c A} {g : ∞Grammar c A} (n : ℕ)
                {final : IsJust (final-whitespace? n (♭? g))} →
                Pretty-printer (♭? g) →
                Pretty-printer (g +)
map+-fill-doc {g = g} n {final} p xs =
  fill+ n {final = final} (uncurry to-docs xs)
  where
  to-docs : ∀ x xs → Docs (♭? g) (x ∷ xs)
  to-docs x []        = [ p x ]
  to-docs x (x′ ∷ xs) = p x ∷ to-docs x′ xs

map⋆-fill-doc : ∀ {c A} {g : ∞Grammar c A} (n : ℕ)
                {final : IsJust (final-whitespace? n (♭? g))} →
                Pretty-printer (♭? g) →
                Pretty-printer (g ⋆)
map⋆-fill-doc n         p []       = []-doc
map⋆-fill-doc n {final} p (x ∷ xs) =
  embed ⋆-+-sem (map+-fill-doc n {final = final} p (x ∷ xs))
