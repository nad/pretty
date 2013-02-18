------------------------------------------------------------------------
-- Sketch of parsing/pretty-printing library which guarantees that
-- pretty-printers are correct (on the assumption that grammars are
-- unambiguous)
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- I don't start from the pretty-printer, but treat pretty-printer
-- documents as a kind of decorated parse trees.

module Pretty where

open import Data.Char
open import Data.List
open import Data.Nat
import Data.String as String
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infix  30 _⋆ _+
infixl 20 _·_ _<$>_ _<$_ _<·_ _·>_ _<·-d_ _·>-d_
infix  20 <$>-d_ <$-d_
infixr 20 _∷-d_
infixl 10 _∣_

------------------------------------------------------------------------
-- Grammars (regular expressions with semantic actions)

-- I could probably have based the development on my parser
-- combinators (presented in ICFP 2010), but decided to stick to
-- regular expressions with semantics actions in this sketch.
--
-- Note that instead of including a primitive combinator for single
-- tokens I include a primitive combinator "text" for sequences of
-- tokens.

data G : Set → Set₁ where
  ∅    : ∀ {A} → G A
  ε    : ∀ {A} → A → G A
  text : List Char → G (List Char)
  _·_  : ∀ {A B} → G (A → B) → G A → G B
  _∣_  : ∀ {A} → G A → G A → G A
  _⋆   : ∀ {A} → G A → G (List A)

-- Semantics of grammars (parse trees). Here x ∈ g ∙ s means that x is
-- one of the possible results of parsing the string s using the
-- grammar g.

infix 4 _∈_∙_

data _∈_∙_ : ∀ {A} → A → G A → List Char → Set₁ where
  ε    : ∀ {A} {x : A} → x ∈ ε x ∙ []
  text : ∀ {s} → s ∈ text s ∙ s
  _·_  : ∀ {A B} {g₁ : G (A → B)} {g₂ : G A} {f x s₁ s₂} →
         f ∈ g₁ ∙ s₁ → x ∈ g₂ ∙ s₂ → f x ∈ g₁ · g₂ ∙ s₁ ++ s₂
  ∣ˡ   : ∀ {A} {g₁ g₂ : G A} {x s} →
         x ∈ g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  ∣ʳ   : ∀ {A} {g₁ g₂ : G A} {x s} →
         x ∈ g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  _⋆   : ∀ {A} {g : G A} {x s} →
         x ∈ ε [] ∣ ε _∷_ · g · g ⋆ ∙ s → x ∈ g ⋆ ∙ s

-- Some derived grammar combinators.

_<$>_ : ∀ {A B} → (A → B) → G A → G B
f <$> g = ε f · g

_<·_ : ∀ {A B} → G A → G B → G A
g₁ <· g₂ = const <$> g₁ · g₂

_·>_ : ∀ {A B} → G A → G B → G B
g₁ ·> g₂ = flip const <$> g₁ · g₂

_<$_ : ∀ {A B} → A → G B → G A
x <$ g = ε x <· g

_+ : ∀ {A} → G A → G (List A)
g + = _∷_ <$> g · g ⋆

tok : Char → G Char
tok t = t <$ text [ t ]

whitespace : G Char
whitespace = tok ' ' ∣ tok '\n'

text-w : List Char → G (List Char)
text-w s = text s <· whitespace ⋆

------------------------------------------------------------------------
-- Pretty-printers

-- Pretty-printer documents. If p : Doc g x, then p is a decorated
-- parse tree (with respect to the grammar g) for the value x.

data Doc : ∀ {A} → G A → A → Set₁ where
  ε     : ∀ {A} {x : A} → Doc (ε x) x
  text  : ∀ {s} → Doc (text s) s
  _·_   : ∀ {A B} {g₁ : G (A → B)} {g₂ : G A} {f x} →
          Doc g₁ f → Doc g₂ x → Doc (g₁ · g₂) (f x)
  line  : ∀ {A} {x : A} → Doc (x <$ whitespace +) x
  group : ∀ {A} {g : G A} {x} → Doc g x → Doc g x
  nest  : ∀ {A} {g : G A} {x} → ℕ → Doc g x → Doc g x
  cast  : ∀ {A} {g₁ g₂ : G A} {x} →
          (∀ {s} → x ∈ g₁ ∙ s → x ∈ g₂ ∙ s) → Doc g₁ x → Doc g₂ x

-- Pretty-printers. A pretty-printer is a function that for every
-- value constructs a matching document.

Pretty-printer : {A : Set} → G A → Set₁
Pretty-printer g = ∀ x → Doc g x

-- Derived document combinators.

∣ˡ-d : ∀ {A} {g₁ g₂ : G A} {x} → Doc g₁ x → Doc (g₁ ∣ g₂) x
∣ˡ-d d = cast ∣ˡ d

∣ʳ-d : ∀ {A} {g₁ g₂ : G A} {x} → Doc g₂ x → Doc (g₁ ∣ g₂) x
∣ʳ-d d = cast ∣ʳ d

[]-d : ∀ {A} {g : G A} → Doc (g ⋆) []
[]-d = cast _⋆ (∣ˡ-d ε)

_∷-d_ : ∀ {A} {g : G A} {x xs} →
       Doc g x → Doc (g ⋆) xs → Doc (g ⋆) (x ∷ xs)
d₁ ∷-d d₂ = cast _⋆ (∣ʳ-d (ε · d₁ · d₂))

<$>-d_ : ∀ {A B : Set} {f : A → B} {x g} →
         Doc g x → Doc (f <$> g) (f x)
<$>-d d = ε · d

_<·-d_ : ∀ {A B : Set} {x : A} {y : B} {g₁ g₂} →
         Doc g₁ x → Doc g₂ y → Doc (g₁ <· g₂) x
d₁ <·-d d₂ = <$>-d d₁ · d₂

_·>-d_ : ∀ {A B : Set} {x : A} {y : B} {g₁ g₂} →
         Doc g₁ x → Doc g₂ y → Doc (g₁ ·> g₂) y
d₁ ·>-d d₂ = <$>-d d₁ · d₂

<$-d_ : ∀ {A B : Set} {x : A} {y : B} {g} →
        Doc g y → Doc (x <$ g) x
<$-d d = ε <·-d d

text-w-d : ∀ {s} → Doc (text-w s) s
text-w-d = ε · text · []-d

text·line : ∀ {s} → Doc (text-w s) s
text·line = cast lemma (text <·-d line)
  where
  lemma : ∀ {x ts s} →
          x ∈ text ts <· (tt <$ whitespace +) ∙ s →
          x ∈ text ts <· whitespace ⋆ ∙ s
  lemma (ε · x∈ · (ε · ε · w+)) = ε · x∈ · ∣ʳ w+ ⋆

map-d : {A : Set} {g : G A} →
        Pretty-printer g → Pretty-printer (g ⋆)
map-d p []       = []-d
map-d p (x ∷ xs) = p x ∷-d map-d p xs

-- Document renderers.

record Renderer : Set₁ where
  field
    -- The function that renders.

    render : ∀ {A} {g : G A} {x} → Doc g x → List Char

    -- The rendered string must be parsable.

    parsable : ∀ {A} {g : G A} {x} (d : Doc g x) → x ∈ g ∙ render d

  -- Pretty-printers are correct by definition, for any renderer,
  -- assuming that the underlying grammar is unambiguous.

  pretty-printer-correct :
    ∀ {A} {g : G A} (pretty : Pretty-printer g) →
    ∀ x → x ∈ g ∙ render (pretty x)
  pretty-printer-correct pretty x = parsable (pretty x)

-- An example renderer.

ugly-renderer : Renderer
ugly-renderer = record
  { render   = render
  ; parsable = parsable
  }
  where
  render : ∀ {A} {g : G A} {x} → Doc g x → List Char
  render ε              = []
  render (text {s = s}) = s
  render (d₁ · d₂)      = render d₁ ++ render d₂
  render line           = [ ' ' ]
  render (group d)      = render d
  render (nest _ d)     = render d
  render (cast _ d)     = render d

  parsable : ∀ {A x} {g : G A} (d : Doc g x) → x ∈ g ∙ render d
  parsable ε          = ε
  parsable text       = text
  parsable (d₁ · d₂)  = parsable d₁ · parsable d₂
  parsable line       = ε · ε · (ε · ∣ˡ (ε · ε · text) · ∣ˡ ε ⋆)
  parsable (group d)  = parsable d
  parsable (nest _ d) = parsable d
  parsable (cast f d) = f (parsable d)

------------------------------------------------------------------------
-- Example

private

  -- Bits.

  data Bit : Set where
    [0] [1] : Bit

  bit : G Bit
  bit = [0] <$ text-w [ '0' ]
      ∣ [1] <$ text-w [ '1' ]

  bit-printer : Pretty-printer bit
  bit-printer [0] = ∣ˡ-d (ε · ε · (ε · text · []-d))
  bit-printer [1] = ∣ʳ-d (<$-d text-w-d)

  -- Lists of bits. This example is based on one in Swierstra and
  -- Chitil's "Linear, bounded, functional pretty-printing".

  bit-list-body : G (List Bit)
  bit-list-body = ε []
                ∣ _∷_ <$> bit · (text-w [ ',' ] ·> bit) ⋆

  bit-list : G (List Bit)
  bit-list = text-w [ '[' ] ·> bit-list-body <· text-w [ ']' ]

  bit-list-printer : Pretty-printer bit-list
  bit-list-printer bs = text-w-d ·>-d body bs <·-d text-w-d
    where
    body : Pretty-printer bit-list-body
    body []       = ∣ˡ-d ε
    body (b ∷ bs) =
      ∣ʳ-d (<$>-d bit-printer b ·
            map-d (λ b → group text·line ·>-d bit-printer b) bs)

  ex : List Bit
  ex = [0] ∷ [1] ∷ [0] ∷ []

  ex′ : List Char
  ex′ = Renderer.render ugly-renderer (bit-list-printer ex)

  ex″ : String.fromList ex′ ≡ "[0, 1, 0]"
  ex″ = refl
