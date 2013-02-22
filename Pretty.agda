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
open import Coinduction
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
infixr 20 _·_ _<$_ _∷-doc_
infixl 15 _>>=_
infixl 10 _∣_

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

data G : Set → Set₁ where
  fail   : ∀ {A} → G A
  return : ∀ {A} → A → G A
  text   : List Char → G (List Char)
  _>>=_  : ∀ {A B} → ∞ (G A) → (A → ∞ (G B)) → G B
  _∣_    : ∀ {A} → ∞ (G A) → ∞ (G A) → G A

-- Semantics of grammars (parse trees). Here x ∈ g ∙ s means that x is
-- one of the possible results of parsing the string s using the
-- grammar g.

infix 4 _∈_∙_

data _∈_∙_ : ∀ {A} → A → G A → List Char → Set₁ where
  return  : ∀ {A} {x : A} → x ∈ return x ∙ []
  text    : ∀ {s} → s ∈ text s ∙ s
  _>>=_   : ∀ {A B} {g₁ : ∞ (G A)} {g₂ : A → ∞ (G B)} {x y s₁ s₂} →
            x ∈ ♭ g₁ ∙ s₁ → y ∈ ♭ (g₂ x) ∙ s₂ → y ∈ g₁ >>= g₂ ∙ s₁ ++ s₂
  ∣-left  : ∀ {A} {g₁ g₂ : ∞ (G A)} {x s} →
            x ∈ ♭ g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  ∣-right : ∀ {A} {g₁ g₂ : ∞ (G A)} {x s} →
            x ∈ ♭ g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s

-- Some derived grammar combinators.

_<$_ : ∀ {A B} → A → G B → G A
x <$ g = ♯ g       >>= λ _ → ♯
         return x

<$-sem : ∀ {A B} {x : A} {y : B} {g s} →
         y ∈ g ∙ s → x ∈ x <$ g ∙ s
<$-sem {x = x} {g = g} y∈ =
  P.subst (λ s → x ∈ x <$ g ∙ s) (proj₂ LM.identity _)
          (y∈ >>= return)

mutual

  _⋆ : ∀ {A} → G A → G (List A)
  g ⋆ = ♯ return [] ∣ ♯ (g +)

  _+ : ∀ {A} → G A → G (List A)
  g + = ♯ g              >>= λ x  → ♯ (
        ♯ (g ⋆)          >>= λ xs → ♯
        return (x ∷ xs)  )

[]-sem : ∀ {A} {g : G A} → [] ∈ g ⋆ ∙ []
[]-sem = ∣-left return

∷-sem+ : ∀ {A} {g : G A} {x xs s₁ s₂} →
         x ∈ g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g + ∙ s₁ ++ s₂
∷-sem+ {g = g} {x} {xs} {s₁} x∈ xs∈ =
  P.subst (λ s → x ∷ xs ∈ g + ∙ s)
          (P.cong (_++_ s₁) (proj₂ LM.identity _))
          (x∈ >>= (xs∈ >>= return))

∷-sem⋆ : ∀ {A} {g : G A} {x xs s₁ s₂} →
         x ∈ g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g ⋆ ∙ s₁ ++ s₂
∷-sem⋆ x∈ xs∈ = ∣-right (∷-sem+ x∈ xs∈)

tok : Char → G Char
tok t = t <$ text [ t ]

tok-sem : ∀ {t} → t ∈ tok t ∙ [ t ]
tok-sem = <$-sem text

whitespace : G Char
whitespace = ♯ tok ' ' ∣ ♯ tok '\n'

-- A grammar for the given string, possibly followed by some
-- whitespace.

symbol : List Char → G (List Char)
symbol s = ♯ text s           >>= λ s → ♯ (
           s <$ whitespace ⋆  )

------------------------------------------------------------------------
-- Pretty-printers

-- Pretty-printer documents. If p : Doc g x, then p is a decorated
-- parse tree (with respect to the grammar g) for the value x.

data Doc : ∀ {A} → G A → A → Set₁ where
  nil   : ∀ {A} {x : A} → Doc (return x) x
  text  : ∀ s → Doc (text s) s
  _·_   : ∀ {A B} {g₁ : ∞ (G A)} {g₂ : A → ∞ (G B)} {x y} →
          Doc (♭ g₁) x → Doc (♭ (g₂ x)) y → Doc (g₁ >>= g₂) y
  line  : ∀ {A} {x : A} → Doc (x <$ whitespace +) x
  group : ∀ {A} {g : G A} {x} → Doc g x → Doc g x
  nest  : ∀ {A} {g : G A} {x} → ℕ → Doc g x → Doc g x
  cast  : ∀ {A B} {g₁ : G A} {g₂ : G B} {x y} →
          (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) → Doc g₁ x → Doc g₂ y

-- Pretty-printers. A pretty-printer is a function that for every
-- value constructs a matching document.

Pretty-printer : {A : Set} → G A → Set₁
Pretty-printer g = ∀ x → Doc g x

-- Derived document combinators.

∣-left-doc : ∀ {A} {g₁ g₂ : ∞ (G A)} {x} →
             Doc (♭ g₁) x → Doc (g₁ ∣ g₂) x
∣-left-doc d = cast ∣-left d

∣-right-doc : ∀ {A} {g₁ g₂ : ∞ (G A)} {x} →
              Doc (♭ g₂) x → Doc (g₁ ∣ g₂) x
∣-right-doc d = cast ∣-right d

<$-doc : ∀ {A B : Set} {x : A} {y : B} {g} →
         Doc g y → Doc (x <$ g) x
<$-doc d = d · nil

[]-doc : ∀ {A} {g : G A} → Doc (g ⋆) []
[]-doc = ∣-left-doc nil

_∷-doc_ : ∀ {A} {g : G A} {x xs} →
          Doc g x → Doc (g ⋆) xs → Doc (g ⋆) (x ∷ xs)
d₁ ∷-doc d₂ = ∣-right-doc (d₁ · d₂ · nil)

-- A document for the given symbol (and no following whitespace).

symbol-doc : ∀ {s} → Doc (symbol s) s
symbol-doc = text _ · <$-doc []-doc

-- A document for the given symbol plus a "line".

symbol-line-doc : ∀ {s} → Doc (symbol s) s
symbol-line-doc = text _ · cast lemma line
  where
  lemma : ∀ {s s′ : List Char} →
          tt ∈ tt <$ whitespace + ∙ s′ →
          s  ∈ s  <$ whitespace ⋆  ∙ s′
  lemma (w+ >>= return) = ∣-right w+ >>= return

map-doc : {A : Set} {g : G A} →
          Pretty-printer g → Pretty-printer (g ⋆)
map-doc p []       = []-doc
map-doc p (x ∷ xs) = p x ∷-doc map-doc p xs

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
  render nil        = []
  render (text s)   = s
  render (d₁ · d₂)  = render d₁ ++ render d₂
  render line       = [ ' ' ]
  render (group d)  = render d
  render (nest _ d) = render d
  render (cast _ d) = render d

  parsable : ∀ {A x} {g : G A} (d : Doc g x) → x ∈ g ∙ render d
  parsable nil        = return
  parsable (text _)   = text
  parsable (d₁ · d₂)  = parsable d₁ >>= parsable d₂
  parsable line       = <$-sem (∷-sem+ (∣-left tok-sem) []-sem)
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
    nil   : ∀ {A} {x : A} → DocU (return x) x
    text  : ∀ s → DocU (text s) s
    _·_   : ∀ {A B} {g₁ : ∞ (G A)} {g₂ : A → ∞ (G B)} {x y} →
            DocU (♭ g₁) x → DocU (♭ (g₂ x)) y → DocU (g₁ >>= g₂) y
    line  : ∀ {A} {x : A} → DocU (x <$ whitespace +) x
    union : ∀ {A} {g : G A} {x} → DocU g x → DocU g x → DocU g x
    nest  : ∀ {A} {g : G A} {x} → ℕ → DocU g x → DocU g x
    cast  : ∀ {A B} {g₁ : G A} {g₂ : G B} {x y} →
            (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) → DocU g₁ x → DocU g₂ y

  -- Replaces line constructors with single spaces, removes groups.

  flatten : ∀ {A} {g : G A} {x} → Doc g x → DocU g x
  flatten nil        = nil
  flatten (text s)   = text s
  flatten (d₁ · d₂)  = flatten d₁ · flatten d₂
  flatten (group d)  = flatten d
  flatten (nest i d) = nest i (flatten d)
  flatten (cast f d) = cast f (flatten d)
  flatten line       = cast lemma (text [ ' ' ]) · nil
    where
    lemma : ∀ {x s} →
            x ∈ text [ ' ' ] ∙ s →
            x ∈ whitespace + ∙ s
    lemma text = ∷-sem+ (∣-left tok-sem) []-sem

  -- Conversion of Docs to DocUs.

  expand-groups : ∀ {A} {g : G A} {x} → Doc g x → DocU g x
  expand-groups nil        = nil
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
  best i nil           = id
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
  replicate-lemma zero    = []-sem
  replicate-lemma (suc i) = ∷-sem⋆ (∣-left tok-sem) (replicate-lemma i)

  nest-line-lemma :
    ∀ {A} {x : A} i →
    x ∈ x <$ whitespace + ∙ showE (nest-line i)
  nest-line-lemma i =
    <$-sem (∷-sem+ (∣-right tok-sem) (replicate-lemma i))

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
  best-lemma s nil                hyp = hyp return
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
             (hyp (f∈ >>= x∈)))

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
  bit = ♯ ([0] <$ symbol [ '0' ])
      ∣ ♯ ([1] <$ symbol [ '1' ])

  -- The first case below is defined using primitive combinators, the
  -- second one using derived ones.

  bit-printer : Pretty-printer bit
  bit-printer [0] = cast ∣-left ((text [ '0' ] ·
                                  (cast ∣-left nil · nil)) ·
                                 nil)
  bit-printer [1] = ∣-right-doc (<$-doc symbol-doc)

  -- Lists of bits. This example is based on one in Swierstra and
  -- Chitil's "Linear, bounded, functional pretty-printing".

  comma-and-bit : G Bit
  comma-and-bit = ♯ symbol [ ',' ]  >>= λ _ → ♯
                  bit

  bit-list-body : G (List Bit)
  bit-list-body = ♯ return []
                ∣ ♯ (♯ bit                >>= λ b  → ♯ (
                     ♯ (comma-and-bit ⋆)  >>= λ bs → ♯
                     return (b ∷ bs)      ))

  bit-list : G (List Bit)
  bit-list = ♯ symbol [ '[' ]  >>= λ _  → ♯ (
             ♯ bit-list-body   >>= λ bs → ♯ (
             ♯ symbol [ ']' ]  >>= λ _  → ♯
             return bs         ))

  comma-and-bit-printer : Pretty-printer comma-and-bit
  comma-and-bit-printer b = group symbol-line-doc · bit-printer b

  bit-list-printer : Pretty-printer bit-list
  bit-list-printer bs = symbol-doc · body bs · symbol-doc · nil
    where
    body : Pretty-printer bit-list-body
    body []       = ∣-left-doc nil
    body (b ∷ bs) = ∣-right-doc
      (bit-printer b · map-doc comma-and-bit-printer bs · nil)

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
