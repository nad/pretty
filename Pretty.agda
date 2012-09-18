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
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infix  30 _⋆ _+
infixl 20 _·_ _<$>_ _<$_ _<·_ _·>_ _<·-d_ _·>-d_
infix  20 <$>-d_ <$-d_
infix  20 _·line
infixr 20 _∷_
infixl 10 _∣_

------------------------------------------------------------------------
-- Grammars (regular expressions with semantic actions)

-- I could probably have based the development on my parser
-- combinators (presented in ICFP 2010), but decided to stick to
-- simple regular expressions in this sketch.

data G : Set → Set₁ where
  ∅       : ∀ {A} → G A
  ε       : ∀ {A} → A → G A
  tok     : Char → G Char
  _·_     : ∀ {A B} → G (A → B) → G A → G B
  _∣_     : ∀ {A} → G A → G A → G A
  _⋆      : ∀ {A} → G A → G (List A)

-- Semantics of grammars (parse trees). Here x ∈ g ∙ s means that x is
-- one of the possible results of parsing the string s using the
-- grammar g.

infix 4 _∈_∙_

data _∈_∙_ : ∀ {A} → A → G A → List Char → Set₁ where
  ε   : ∀ {A} {x : A} → x ∈ ε x ∙ []
  tok : ∀ {t} → t ∈ tok t ∙ [ t ]
  _·_ : ∀ {A B} {g₁ : G (A → B)} {g₂ : G A} {f x s₁ s₂} →
        f ∈ g₁ ∙ s₁ → x ∈ g₂ ∙ s₂ → f x ∈ g₁ · g₂ ∙ s₁ ++ s₂
  ∣ˡ  : ∀ {A} {g₁ g₂ : G A} {x s} →
        x ∈ g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  ∣ʳ  : ∀ {A} {g₁ g₂ : G A} {x s} →
        x ∈ g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  _⋆  : ∀ {A} {g : G A} {x s} →
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

whitespace : G (List Char)
whitespace = (tok ' ' ∣ tok '\n') ⋆

symbol : List Char → G (List Char)
symbol []      = ε []
symbol (t ∷ s) = _∷_ <$> tok t · symbol s

symbol-lemma : ∀ s → s ∈ symbol s ∙ s
symbol-lemma []      = ε
symbol-lemma (t ∷ s) = ε · tok · symbol-lemma s

symbol-w : List Char → G (List Char)
symbol-w s = symbol s <· whitespace

------------------------------------------------------------------------
-- Pretty-printers

-- Pretty-printer documents. If p : Doc g x, then p is a decorated
-- parse tree (with respect to the grammar g) for the value x.

data Doc : ∀ {A} → G A → A → Set₁ where
  ε      : ∀ {A} {x : A} → Doc (ε x) x
  text   : ∀ {s} → Doc (symbol s) s
  _·_    : ∀ {A B} {g₁ : G (A → B)} {g₂ : G A} {f x} →
           Doc g₁ f → Doc g₂ x → Doc (g₁ · g₂) (f x)
  ∣ˡ     : ∀ {A} {g₁ g₂ : G A} {x} → Doc g₁ x → Doc (g₁ ∣ g₂) x
  ∣ʳ     : ∀ {A} {g₁ g₂ : G A} {x} → Doc g₂ x → Doc (g₁ ∣ g₂) x
  []     : ∀ {A} {g : G A} → Doc (g ⋆) []
  _∷_    : ∀ {A} {g : G A} {x xs} →
           Doc g x → Doc (g ⋆) xs → Doc (g ⋆) (x ∷ xs)
  _·line : ∀ {A} {g : G A} {x} → Doc g x → Doc (g <· whitespace) x
  group  : ∀ {A} {g : G A} {x} → Doc g x → Doc g x
  nest   : ∀ {A} {g : G A} {x} → ℕ → Doc g x → Doc g x

  -- It is perhaps useful to add some kind of cast combinator.

-- Pretty-printers. A pretty-printer is a function that for every
-- value constructs a matching document.

Pretty-printer : {A : Set} → G A → Set₁
Pretty-printer g = ∀ x → Doc g x

-- Derived document combinators.

line : ∀ {A} {x : A} → Doc (x <$ whitespace) x
line = ε ·line

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

symbol-w-d : ∀ {s} → Doc (symbol-w s) s
symbol-w-d = ε · text · []

map-d : {A : Set} {g : G A} →
        Pretty-printer g → (xs : List A) → Doc (g ⋆) xs
map-d p []       = []
map-d p (x ∷ xs) = p x ∷ map-d p xs

-- Document renderers.

record Renderer : Set₁ where
  field
    -- The function that renders.
    renderer : ∀ {A} {g : G A} {x} → Doc g x → List Char

    -- The renderer must produce parsable results. This means that
    -- pretty-printers are correct by definition, assuming that the
    -- underlying grammar is unambiguous.
    parsable : ∀ {A} {g : G A} (pretty : Pretty-printer g) →
               ∀ x → x ∈ g ∙ renderer (pretty x)

-- An example renderer.

ugly-renderer : Renderer
ugly-renderer = record
  { renderer = renderer
  ; parsable = λ pretty x → parse-tree (pretty x)
  }
  where
  renderer : ∀ {A} {g : G A} {x} → Doc g x → List Char
  renderer ε              = []
  renderer (text {s = s}) = s
  renderer (d₁ · d₂)      = renderer d₁ ++ renderer d₂
  renderer (∣ˡ d)         = renderer d
  renderer (∣ʳ d)         = renderer d
  renderer []             = []
  renderer (d ∷ ds)       = renderer d ++ renderer ds
  renderer (d ·line)      = renderer d ++ [ ' ' ]
  renderer (group d)      = renderer d
  renderer (nest x d)     = renderer d

  -- A document's underlying parse tree (with respect to renderer).

  parse-tree : ∀ {A x} {g : G A} (d : Doc g x) → x ∈ g ∙ renderer d
  parse-tree ε          = ε
  parse-tree text       = symbol-lemma _
  parse-tree (d₁ · d₂)  = parse-tree d₁ · parse-tree d₂
  parse-tree (∣ˡ d)     = ∣ˡ (parse-tree d)
  parse-tree (∣ʳ d)     = ∣ʳ (parse-tree d)
  parse-tree []         = ∣ˡ ε ⋆
  parse-tree (d ∷ ds)   = ∣ʳ (ε · parse-tree d · parse-tree ds) ⋆
  parse-tree (d ·line)  = ε · parse-tree d · ∣ʳ (ε · ∣ˡ tok · ∣ˡ ε ⋆) ⋆
  parse-tree (nest k d) = parse-tree d
  parse-tree (group d)  = parse-tree d

------------------------------------------------------------------------
-- Example

private

  -- Bits.

  data Bit : Set where
    [0] [1] : Bit

  bit : G Bit
  bit = [0] <$ symbol-w [ '0' ]
      ∣ [1] <$ symbol-w [ '1' ]

  bit-printer : Pretty-printer bit
  bit-printer [0] = ∣ˡ (ε · ε · (ε · text · []))
  bit-printer [1] = ∣ʳ (<$-d symbol-w-d)

  -- Lists of bits. This example is based on one in Swierstra and
  -- Chitil's "Linear, Bounded, Functional Pretty-Printing".

  bit-list-body : G (List Bit)
  bit-list-body = ε []
                ∣ _∷_ <$> bit · (symbol-w [ ',' ] ·> bit) ⋆

  bit-list : G (List Bit)
  bit-list = symbol-w [ '[' ] ·> bit-list-body <· symbol-w [ ']' ]

  bit-list-printer : Pretty-printer bit-list
  bit-list-printer bs = symbol-w-d ·>-d body bs <·-d symbol-w-d
    where
    body : Pretty-printer bit-list-body
    body []       = ∣ˡ ε
    body (b ∷ bs) = ∣ʳ (<$>-d bit-printer b ·
                        map-d (λ b → group (text ·line) ·>-d bit-printer b) bs)

  ex : List Bit
  ex = [0] ∷ [1] ∷ [0] ∷ []

  ex′ : List Char
  ex′ = Renderer.renderer ugly-renderer (bit-list-printer ex)

  ex″ : String.fromList ex′ ≡ "[0, 1, 0]"
  ex″ = refl
