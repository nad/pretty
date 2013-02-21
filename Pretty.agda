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

open import Algebra
open import Data.Bool
open import Data.Char
open import Data.List as List
open import Data.Nat as Nat
open import Data.Product
open import Data.String as String using (String)
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
import Relation.Binary.Props.DecTotalOrder as DTO
open import Relation.Nullary.Decidable

open StrictTotalOrder (DTO.strictTotalOrder Nat.decTotalOrder)
  using (_<?_)
private
  module LM {A : Set} = Monoid (List.monoid A)

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
  text  : ∀ s → Doc (text s) s
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
text-w-d = ε · text _ · []-d

text·line : ∀ {s} → Doc (text-w s) s
text·line = cast lemma (text _ <·-d line)
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
  render ε          = []
  render (text s)   = s
  render (d₁ · d₂)  = render d₁ ++ render d₂
  render line       = [ ' ' ]
  render (group d)  = render d
  render (nest _ d) = render d
  render (cast _ d) = render d

  parsable : ∀ {A x} {g : G A} (d : Doc g x) → x ∈ g ∙ render d
  parsable ε          = ε
  parsable (text _)   = text
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
  { render   = render
  ; parsable = parsable
  }
  where

  -- Documents with unions instead of groups.

  infixl 20 _·_

  data DocU : ∀ {A} → G A → A → Set₁ where
    ε     : ∀ {A} {x : A} → DocU (ε x) x
    text  : ∀ s → DocU (text s) s
    _·_   : ∀ {A B} {g₁ : G (A → B)} {g₂ : G A} {f x} →
            DocU g₁ f → DocU g₂ x → DocU (g₁ · g₂) (f x)
    line  : ∀ {A} {x : A} → DocU (x <$ whitespace +) x
    union : ∀ {A} {g : G A} {x} → DocU g x → DocU g x → DocU g x
    nest  : ∀ {A} {g : G A} {x} → ℕ → DocU g x → DocU g x
    cast  : ∀ {A} {g₁ g₂ : G A} {x} →
            (∀ {s} → x ∈ g₁ ∙ s → x ∈ g₂ ∙ s) → DocU g₁ x → DocU g₂ x

  -- Replaces line constructors with single spaces, removes groups.

  flatten : ∀ {A} {g : G A} {x} → Doc g x → DocU g x
  flatten ε          = ε
  flatten (text s)   = text s
  flatten (d₁ · d₂)  = flatten d₁ · flatten d₂
  flatten (group d)  = flatten d
  flatten (nest i d) = nest i (flatten d)
  flatten (cast f d) = cast f (flatten d)
  flatten line       = ε · ε · cast lemma (text [ ' ' ])
    where
    lemma : ∀ {x s} →
            x ∈ text [ ' ' ] ∙ s →
            x ∈ whitespace + ∙ s
    lemma text = ε · ∣ˡ (ε · ε · text) · ∣ˡ ε ⋆

  -- Conversion of Docs to DocUs.

  expand-groups : ∀ {A} {g : G A} {x} → Doc g x → DocU g x
  expand-groups ε          = ε
  expand-groups (text s)   = text s
  expand-groups (d₁ · d₂)  = expand-groups d₁ · expand-groups d₂
  expand-groups line       = line
  expand-groups (group d)  = union (flatten d) (expand-groups d)
  expand-groups (nest i d) = nest i (expand-groups d)
  expand-groups (cast f d) = cast f (expand-groups d)

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
    fits′ w c x = not ⌊ w <? c ⌋ ∧ fits (w ∸ c) x

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

  best : ∀ {A} {g : G A} {x} →
         ℕ → DocU g x → (ℕ → Layout) → (ℕ → Layout)
  best i ε             = id
  best i (text s)      = λ κ c → text s ∷ κ (length s + c)
  best i (d₁ · d₂)     = best i d₁ ∘ best i d₂
  best i line          = λ κ _ → nest-line i ∷ κ i
  best i (union d₁ d₂) = λ κ c → better c (best i d₁ κ c)
                                          (best i d₂ κ c)
  best i (nest j d)    = best (j + i) d
  best i (cast f d)    = best i d

  -- Renders a document.

  render : ∀ {A} {g : G A} {x} → Doc g x → List Char
  render d = show (best 0 (expand-groups d) (λ _ → []) 0)

  -- Some simple lemmas.

  replicate-lemma :
    ∀ i → replicate i ' ' ∈ whitespace ⋆ ∙ replicate i ' '
  replicate-lemma zero    = ∣ˡ ε ⋆
  replicate-lemma (suc i) =
    ∣ʳ (ε · ∣ˡ (ε · ε · text) · replicate-lemma i) ⋆

  nest-line-lemma :
    ∀ {A} {x : A} i →
    x ∈ x <$ whitespace + ∙ showE (nest-line i)
  nest-line-lemma i =
    ε · ε · (ε · ∣ʳ (ε · ε · text) · replicate-lemma i)

  if-lemma :
    ∀ {A} {g : G A} {x l₁ l₂} s b →
    x ∈ g ∙ s ++ show l₁ →
    x ∈ g ∙ s ++ show l₂ →
    x ∈ g ∙ s ++ show (if b then l₁ else l₂)
  if-lemma _ true  ∈l₁ ∈l₂ = ∈l₁
  if-lemma _ false ∈l₁ ∈l₂ = ∈l₂

  ++-lemma : {A : Set} (a b c d : List A) →
             a ++ (b ++ c) ++ d ≡ (a ++ b) ++ c ++ d
  ++-lemma a b c d = begin
    a ++ (b ++ c) ++ d  ≡⟨ P.cong (_++_ a) $ LM.assoc b c d ⟩
    a ++ b ++ c ++ d    ≡⟨ P.sym $ LM.assoc a b (c ++ d) ⟩
    (a ++ b) ++ c ++ d  ∎
    where open P.≡-Reasoning

  -- The main correctness property for best.

  best-lemma :
    ∀ {i A B} {g : G A} {x c κ} s {g′ : G B} {y} (d : DocU g x) →
    (∀ {s′ c′} → x ∈ g ∙ s′ → y ∈ g′ ∙ s ++ s′ ++ show (κ c′)) →
    y ∈ g′ ∙ s ++ show (best i d κ c)
  best-lemma s ε                  hyp = hyp ε
  best-lemma s (text s′)          hyp = hyp text
  best-lemma {i} s line           hyp = hyp (nest-line-lemma i)
  best-lemma s (union d₁ d₂)      hyp = if-lemma s
                                          (fits′ w _ (best _ d₁ _ _))
                                          (best-lemma s d₁ hyp)
                                          (best-lemma s d₂ hyp)
  best-lemma s (nest j d)         hyp = best-lemma s d hyp
  best-lemma s (cast f d)         hyp = best-lemma s d (hyp ∘ f)
  best-lemma s {g′} {y} (d₁ · d₂) hyp =
    best-lemma s d₁ λ {s′} f∈ →
      P.subst (λ s → y ∈ g′ ∙ s) (LM.assoc s _ _)
        (best-lemma (s ++ s′) d₂ λ x∈ →
           P.subst (λ s → y ∈ g′ ∙ s) (++-lemma s _ _ _)
             (hyp (f∈ · x∈)))

  -- The renderer is correct.

  parsable : ∀ {A} {g : G A} {x} (d : Doc g x) → x ∈ g ∙ render d
  parsable {g = g} {x} d = best-lemma [] (expand-groups d) hyp
    where
    hyp : ∀ {s} → x ∈ g ∙ s → x ∈ g ∙ s ++ []
    hyp = P.subst (λ s → x ∈ g ∙ s) (P.sym $ proj₂ LM.identity _)

------------------------------------------------------------------------
-- Example

private

  -- Bits.

  data Bit : Set where
    [0] [1] : Bit

  bit : G Bit
  bit = [0] <$ text-w [ '0' ]
      ∣ [1] <$ text-w [ '1' ]

  -- The first case below is defined using primitive combinators, the
  -- second one using derived ones.

  bit-printer : Pretty-printer bit
  bit-printer [0] = cast ∣ˡ (ε · ε · (ε · text [ '0' ] ·
                                          cast _⋆ (cast ∣ˡ ε)))
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
