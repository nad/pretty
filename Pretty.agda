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

open import Data.Bool
open import Data.Char
open import Data.List
open import Data.Nat as Nat
open import Data.Product
open import Data.String as String using (String)
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Props.DecTotalOrder as DTO
open import Relation.Nullary.Decidable

open StrictTotalOrder (DTO.strictTotalOrder Nat.decTotalOrder)
  using (_<?_)

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

-- An example renderer, closely based on the one in Wadler's "A
-- prettier printer".
--
-- The natural number is the line width.

wadler's-renderer : ℕ → Renderer
wadler's-renderer w = record
  { render   = λ d → layout (best d)
  ; parsable = {!!}
  }
  where
  Layout : Set
  Layout = List (List Char ⊎ ℕ)

  layout : Layout → List Char
  layout []           = []
  layout (inj₁ s ∷ x) = s ++ layout x
  layout (inj₂ i ∷ x) = '\n' ∷ replicate i ' ' ++ layout x

  infixl 20 _·_

  data DocU : ∀ {A} → G A → A → Set₁ where
    ε     : ∀ {A} {x : A} → DocU (ε x) x
    text  : ∀ {s} → DocU (text s) s
    _·_   : ∀ {A B} {g₁ : G (A → B)} {g₂ : G A} {f x} →
            DocU g₁ f → DocU g₂ x → DocU (g₁ · g₂) (f x)
    line  : ∀ {A} {x : A} → DocU (x <$ whitespace +) x
    union : ∀ {A} {g : G A} {x} → DocU g x → DocU g x → DocU g x
    nest  : ∀ {A} {g : G A} {x} → ℕ → DocU g x → DocU g x
    cast  : ∀ {A} {g₁ g₂ : G A} {x} →
            (∀ {s} → x ∈ g₁ ∙ s → x ∈ g₂ ∙ s) → DocU g₁ x → DocU g₂ x

  flatten : ∀ {A} {g : G A} {x} → Doc g x → DocU g x
  flatten ε          = ε
  flatten text       = text
  flatten (d₁ · d₂)  = flatten d₁ · flatten d₂
  flatten (group d)  = flatten d
  flatten (nest i d) = nest i (flatten d)
  flatten (cast f d) = cast f (flatten d)
  flatten line       = ε · ε · cast lemma (text {s = [ ' ' ]})
    where
    lemma : ∀ {x s} →
            x ∈ text [ ' ' ] ∙ s →
            x ∈ whitespace + ∙ s
    lemma text = ε · ∣ˡ (ε · ε · text) · ∣ˡ ε ⋆

  expand-groups : ∀ {A} {g : G A} {x} → Doc g x → DocU g x
  expand-groups ε          = ε
  expand-groups text       = text
  expand-groups (d₁ · d₂)  = expand-groups d₁ · expand-groups d₂
  expand-groups line       = line
  expand-groups (group d)  = union (flatten d) (expand-groups d)
  expand-groups (nest i d) = nest i (expand-groups d)
  expand-groups (cast f d) = cast f (expand-groups d)

  mutual

    fits : ℕ → Layout → Bool
    fits w []           = true
    fits w (inj₁ s ∷ x) = fits′ w (length s) x
    fits w (inj₂ i ∷ x) = true

    fits′ : ℕ → ℕ → Layout → Bool
    fits′ w k x = not ⌊ w <? k ⌋ ∧ fits (w ∸ k) x

  better : Layout → Layout → (ℕ → Layout)
  better x y k = if fits′ w k x then x else y

  be : ∀ {A} {g : G A} {x} →
       ℕ → DocU g x → (ℕ → Layout) → (ℕ → Layout)
  be i ε              = id
  be i (text {s = s}) = λ c k → inj₁ s ∷ c (length s + k)
  be i (d₁ · d₂)      = be i d₁ ∘ be i d₂
  be i line           = λ c _ → inj₂ i ∷ c i
  be i (union d₁ d₂)  = λ c k → better (be i d₁ c k) (be i d₂ c k) k
  be i (nest j d)     = be (j + i) d
  be i (cast f d)     = be i d

  best : ∀ {A} {g : G A} {x} →
         Doc g x → Layout
  best d = be 0 (expand-groups d) (λ _ → []) 0

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
  ex = [0] ∷ [1] ∷ [0] ∷ [0] ∷ [1] ∷ []

  ex′ : ℕ → String
  ex′ w =
    String.fromList $
      Renderer.render (wadler's-renderer w) (bit-list-printer ex)

  ex″ : ex′ 9 ≡ "[0, 1, 0,\n0, 1]"
  ex″ = refl

  ex‴ : ex′ 6 ≡ "[0, 1,\n0, 0,\n1]"
  ex‴ = refl

  ex⁗ : ex′ 3 ≡ "[0,\n1,\n0,\n0,\n1]"
  ex⁗ = refl
