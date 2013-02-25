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
open import Data.Char as Char
open import Data.Empty
open import Data.List as List
open import Data.List.Properties using (module List-solver)
open import Data.Nat as Nat
open import Data.Product
open import Data.String as String using (String)
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
import Relation.Binary.Props.DecTotalOrder as DTO
import Relation.Binary.Props.StrictTotalOrder as STO
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Product

open StrictTotalOrder (DTO.strictTotalOrder Nat.decTotalOrder)
  using (_<?_)
open DecTotalOrder (STO.decTotalOrder Char.strictTotalOrder)
  using () renaming (_≤_ to _≤C_; _≤?_ to _≤?C_)
private
  module LM {A : Set} = Monoid (List.monoid A)

infix  30 _⋆ _+
infixr 20 _·_ _<$_ _∷-doc_
infixl 15 _>>=_
infixl 10 _∣_

------------------------------------------------------------------------
-- Some boring lemmas

private

  ++-lemma₀ : {A : Set} (a b c d : List A) →
              a ++ (b ++ c) ++ d ≡ (a ++ b) ++ c ++ d
  ++-lemma₀ = solve 4 (λ a b c d → a ⊕ (b ⊕ c) ⊕ d ⊜
                                   (a ⊕ b) ⊕ c ⊕ d)
                      refl
    where open List-solver

  ++-lemma₁ : {A : Set} (a b c d : List A) →
              a ++ (b ++ c ++ d) ++ [] ≡
              (a ++ (b ++ c) ++ []) ++ d
  ++-lemma₁ = solve 4 (λ a b c d → a ⊕ (b ⊕ c ⊕ d) ⊕ nil ⊜
                                   (a ⊕ (b ⊕ c) ⊕ nil) ⊕ d)
                      refl
    where open List-solver

  ++-lemma₂ : {A : Set} (a b c d e : List A) →
              a ++ (b ++ c ++ (d ++ e) ++ []) ++ [] ≡
              (a ++ (b ++ c ++ d ++ []) ++ []) ++ e
  ++-lemma₂ = solve 5 (λ a b c d e → a ⊕ (b ⊕ c ⊕ (d ⊕ e) ⊕ nil) ⊕ nil ⊜
                                     (a ⊕ (b ⊕ c ⊕ d ⊕ nil) ⊕ nil) ⊕ e)
                      refl
    where open List-solver

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
  token  : G Char
  _>>=_  : ∀ {A B} → ∞ (G A) → (A → ∞ (G B)) → G B
  _∣_    : ∀ {A} → ∞ (G A) → ∞ (G A) → G A

-- Semantics of grammars (parse trees). Here x ∈ g ∙ s means that x is
-- one of the possible results of parsing the string s using the
-- grammar g.

infix 4 _∈_∙_

data _∈_∙_ : ∀ {A} → A → G A → List Char → Set₁ where
  return  : ∀ {A} {x : A} → x ∈ return x ∙ []
  token   : ∀ {t} → t ∈ token ∙ [ t ]
  _>>=_   : ∀ {A B} {g₁ : ∞ (G A)} {g₂ : A → ∞ (G B)} {x y s₁ s₂} →
            x ∈ ♭ g₁ ∙ s₁ → y ∈ ♭ (g₂ x) ∙ s₂ → y ∈ g₁ >>= g₂ ∙ s₁ ++ s₂
  ∣-left  : ∀ {A} {g₁ g₂ : ∞ (G A)} {x s} →
            x ∈ ♭ g₁ ∙ s → x ∈ g₁ ∣ g₂ ∙ s
  ∣-right : ∀ {A} {g₁ g₂ : ∞ (G A)} {x s} →
            x ∈ ♭ g₂ ∙ s → x ∈ g₁ ∣ g₂ ∙ s

-- Cast lemma.

cast : ∀ {A} {g : G A} {x s₁ s₂} →
       s₁ ≡ s₂ → x ∈ g ∙ s₁ → x ∈ g ∙ s₂
cast refl = id

-- Some derived grammar combinators.

_<$_ : ∀ {A B} → A → G B → G A
x <$ g = ♯ g         >>= λ _ →
         ♯ return x

<$-sem : ∀ {A B} {x : A} {y : B} {g s} →
         y ∈ g ∙ s → x ∈ x <$ g ∙ s
<$-sem y∈ = cast (proj₂ LM.identity _) (y∈ >>= return)

mutual

  _⋆ : ∀ {A} → G A → G (List A)
  g ⋆ = ♯ return [] ∣ ♯ (g +)

  _+ : ∀ {A} → G A → G (List A)
  g + = ♯ g                >>= λ x  → ♯ (
        ♯ (g ⋆)            >>= λ xs →
        ♯ return (x ∷ xs)  )

[]-sem : ∀ {A} {g : G A} → [] ∈ g ⋆ ∙ []
[]-sem = ∣-left return

∷-sem+ : ∀ {A} {g : G A} {x xs s₁ s₂} →
         x ∈ g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g + ∙ s₁ ++ s₂
∷-sem+ {s₁ = s₁} x∈ xs∈ =
  cast (P.cong (_++_ s₁) (proj₂ LM.identity _))
       (x∈ >>= (xs∈ >>= return))

∷-sem⋆ : ∀ {A} {g : G A} {x xs s₁ s₂} →
         x ∈ g ∙ s₁ → xs ∈ g ⋆ ∙ s₂ → x ∷ xs ∈ g ⋆ ∙ s₁ ++ s₂
∷-sem⋆ x∈ xs∈ = ∣-right (∷-sem+ x∈ xs∈)

if-true : (b : Bool) → G (T b)
if-true true  = return tt
if-true false = fail

if-true-sem : ∀ {b} (t : T b) → t ∈ if-true b ∙ []
if-true-sem {b = true}  _  = return
if-true-sem {b = false} ()

sat : (p : Char → Bool) → G (∃ λ t → T (p t))
sat p = ♯ token            >>= λ t  → ♯ (
        ♯ if-true (p t)    >>= λ pt →
        ♯ return (t , pt)  )

sat-sem : ∀ {p : Char → Bool} {t} (pt : T (p t)) →
          (t , pt) ∈ sat p ∙ [ t ]
sat-sem pt = token >>= (if-true-sem pt >>= return)

sat-sem⁻¹ : ∀ {p : Char → Bool} {t pt s} →
            (t , pt) ∈ sat p ∙ s → s ≡ [ t ]
sat-sem⁻¹ {p = p}
          (_>>=_ {x = t} token (pt∈    >>= return)) with p t
sat-sem⁻¹ (_>>=_ {x = t} token (return >>= return)) | true  = refl
sat-sem⁻¹ (_>>=_ {x = t} token (()     >>= return)) | false

tok : Char → G Char
tok t = ♯ sat (λ t′ → ⌊ t Char.≟ t′ ⌋)  >>= λ { (t , _) →
        ♯ return t                      }

tok-sem : ∀ {t} → t ∈ tok t ∙ [ t ]
tok-sem = sat-sem (lemma _) >>= return
  where
  lemma : ∀ {t} (d : Dec (t ≡ t)) → T ⌊ d ⌋
  lemma (yes refl) = tt
  lemma (no t≢t)   = ⊥-elim (t≢t refl)

tok-sem⁻¹ : ∀ {t t′ s} → t ∈ tok t′ ∙ s → t ≡ t′ × s ≡ [ t ]
tok-sem⁻¹ (_>>=_ {x = _ , t′≡t} tp∈ return) =
  P.sym (toWitness t′≡t) , P.cong (λ s → s ++ []) (sat-sem⁻¹ tp∈)

whitespace : G Char
whitespace = ♯ tok ' ' ∣ ♯ tok '\n'

-- A grammar for the given string.

string : List Char → G (List Char)
string []      = return []
string (t ∷ s) = ♯ tok t           >>= λ t → ♯ (
                 ♯ string s        >>= λ s →
                 ♯ return (t ∷ s)  )

string-sem : ∀ s → s ∈ string s ∙ s
string-sem []      = return
string-sem (t ∷ s) =
  cast (P.cong (_∷_ t) $ proj₂ LM.identity s)
       (tok-sem >>= (string-sem s >>= return))

-- A grammar for the given string, possibly followed by some
-- whitespace.

symbol : List Char → G (List Char)
symbol s = ♯ string s             >>= λ s →
           ♯ (s <$ whitespace ⋆)

------------------------------------------------------------------------
-- Pretty-printers

-- Pretty-printer documents. If p : Doc g x, then p is a decorated
-- parse tree (with respect to the grammar g) for the value x.

data Doc : ∀ {A} → G A → A → Set₁ where
  nil   : ∀ {A} {x : A} → Doc (return x) x
  text  : ∀ s → Doc (string s) s
  _·_   : ∀ {A B} {g₁ : ∞ (G A)} {g₂ : A → ∞ (G B)} {x y} →
          Doc (♭ g₁) x → Doc (♭ (g₂ x)) y → Doc (g₁ >>= g₂) y
  line  : ∀ {A} {x : A} → Doc (x <$ whitespace +) x
  group : ∀ {A} {g : G A} {x} → Doc g x → Doc g x
  nest  : ∀ {A} {g : G A} {x} → ℕ → Doc g x → Doc g x
  embed : ∀ {A B} {g₁ : G A} {g₂ : G B} {x y} →
          (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) → Doc g₁ x → Doc g₂ y

-- Pretty-printers. A pretty-printer is a function that for every
-- value constructs a matching document.

Pretty-printer : {A : Set} → G A → Set₁
Pretty-printer g = ∀ x → Doc g x

-- Derived document combinators.

∣-left-doc : ∀ {A} {g₁ g₂ : ∞ (G A)} {x} →
             Doc (♭ g₁) x → Doc (g₁ ∣ g₂) x
∣-left-doc d = embed ∣-left d

∣-right-doc : ∀ {A} {g₁ g₂ : ∞ (G A)} {x} →
              Doc (♭ g₂) x → Doc (g₁ ∣ g₂) x
∣-right-doc d = embed ∣-right d

<$-doc : ∀ {A B : Set} {x : A} {y : B} {g} →
         Doc g y → Doc (x <$ g) x
<$-doc d = d · nil

[]-doc : ∀ {A} {g : G A} → Doc (g ⋆) []
[]-doc = ∣-left-doc nil

_∷-doc_ : ∀ {A} {g : G A} {x xs} →
          Doc g x → Doc (g ⋆) xs → Doc (g ⋆) (x ∷ xs)
d₁ ∷-doc d₂ = ∣-right-doc (d₁ · d₂ · nil)

-- A document for the given character.

token-doc : ∀ {t} → Doc token t
token-doc {t} = embed lemma (text [ t ])
  where
  lemma : ∀ {s} → [ t ] ∈ string [ t ] ∙ s → t ∈ token ∙ s
  lemma (t∈tok >>= (return >>= return))
    rewrite proj₂ (tok-sem⁻¹ t∈tok)
    = token

-- A document for the empty string.

if-true-doc : ∀ {b} {t : T b} → Doc (if-true b) t
if-true-doc {true}     = nil
if-true-doc {false} {}

-- A document for the given character.

sat-doc : ∀ {p : Char → Bool} {t pt} →
          Doc (sat p) (t , pt)
sat-doc = token-doc · if-true-doc · nil

-- A document for the given symbol (and no following whitespace).

symbol-doc : ∀ {s} → Doc (symbol s) s
symbol-doc = text _ · <$-doc []-doc

-- A document for the given symbol plus a "line".

symbol-line-doc : ∀ {s} → Doc (symbol s) s
symbol-line-doc = text _ · embed lemma line
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
  render nil         = []
  render (text s)    = s
  render (d₁ · d₂)   = render d₁ ++ render d₂
  render line        = [ ' ' ]
  render (group d)   = render d
  render (nest _ d)  = render d
  render (embed _ d) = render d

  parsable : ∀ {A x} {g : G A} (d : Doc g x) → x ∈ g ∙ render d
  parsable nil         = return
  parsable (text s)    = string-sem s
  parsable (d₁ · d₂)   = parsable d₁ >>= parsable d₂
  parsable line        = <$-sem (∷-sem+ (∣-left tok-sem) []-sem)
  parsable (group d)   = parsable d
  parsable (nest _ d)  = parsable d
  parsable (embed f d) = f (parsable d)

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

  infixr 20 _·_

  data DocU : ∀ {A} → G A → A → Set₁ where
    nil   : ∀ {A} {x : A} → DocU (return x) x
    text  : ∀ s → DocU (string s) s
    _·_   : ∀ {A B} {g₁ : ∞ (G A)} {g₂ : A → ∞ (G B)} {x y} →
            DocU (♭ g₁) x → DocU (♭ (g₂ x)) y → DocU (g₁ >>= g₂) y
    line  : ∀ {A} {x : A} → DocU (x <$ whitespace +) x
    union : ∀ {A} {g : G A} {x} → DocU g x → DocU g x → DocU g x
    nest  : ∀ {A} {g : G A} {x} → ℕ → DocU g x → DocU g x
    embed : ∀ {A B} {g₁ : G A} {g₂ : G B} {x y} →
            (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) → DocU g₁ x → DocU g₂ y

  -- Replaces line constructors with single spaces, removes groups.

  flatten : ∀ {A} {g : G A} {x} → Doc g x → DocU g x
  flatten nil         = nil
  flatten (text s)    = text s
  flatten (d₁ · d₂)   = flatten d₁ · flatten d₂
  flatten (group d)   = flatten d
  flatten (nest i d)  = nest i (flatten d)
  flatten (embed f d) = embed f (flatten d)
  flatten line        = embed lemma (text [ ' ' ]) · nil
    where
    lemma : ∀ {x s} →
            x ∈ string [ ' ' ] ∙ s →
            x ∈ whitespace + ∙ s
    lemma (space >>= (return >>= return)) =
      ∷-sem+ (∣-left space) []-sem

  -- Conversion of Docs to DocUs.

  expand-groups : ∀ {A} {g : G A} {x} → Doc g x → DocU g x
  expand-groups nil         = nil
  expand-groups (text s)    = text s
  expand-groups (d₁ · d₂)   = expand-groups d₁ · expand-groups d₂
  expand-groups line        = line
  expand-groups (group d)   = union (flatten d) (expand-groups d)
  expand-groups (nest i d)  = nest i (expand-groups d)
  expand-groups (embed f d) = embed f (expand-groups d)

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
  best i (embed _ d)   = best i d

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

  -- The main correctness property for best.

  best-lemma :
    ∀ {A B} {g : G A} {g′ : G B} {x y c κ} s (d : DocU g x) {i} →
    (∀ {s′ c′} → x ∈ g ∙ s′ → y ∈ g′ ∙ s ++ s′ ++ show (κ c′)) →
    y ∈ g′ ∙ s ++ show (best i d κ c)
  best-lemma s nil           hyp = hyp return
  best-lemma s (text s′)     hyp = hyp (string-sem s′)
  best-lemma s line {i}      hyp = hyp (nest-line-lemma i)
  best-lemma s (union d₁ d₂) hyp = if-lemma s
                                     (fits′ w _ (best _ d₁ _ _))
                                     (best-lemma s d₁ hyp)
                                     (best-lemma s d₂ hyp)
  best-lemma s (nest j d)    hyp = best-lemma s d hyp
  best-lemma s (embed f d)   hyp = best-lemma s d (hyp ∘ f)
  best-lemma s (d₁ · d₂)     hyp =
    best-lemma s d₁ λ {s′} f∈ →
      cast (LM.assoc s _ _)
        (best-lemma (s ++ s′) d₂ λ x∈ →
           cast (++-lemma₀ s _ _ _)
             (hyp (f∈ >>= x∈)))

  -- The renderer is correct.

  parsable : ∀ {A} {g : G A} {x} (d : Doc g x) → x ∈ g ∙ render d
  parsable d = best-lemma [] (expand-groups d)
                          (cast (P.sym $ proj₂ LM.identity _))

------------------------------------------------------------------------
-- Examples

-- Uses wadler's-renderer to render a document using the given line
-- width.

render : ∀ {A} {g : G A} {x} → ℕ → Doc g x → String
render w d = String.fromList (Renderer.render (wadler's-renderer w) d)

module Bit where

  -- Bits.

  data Bit : Set where
    [0] [1] : Bit

  bit : G Bit
  bit = ♯ ([0] <$ symbol [ '0' ])
      ∣ ♯ ([1] <$ symbol [ '1' ])

  -- The first case below is defined using primitive combinators, the
  -- second one using derived ones.

  bit-printer : Pretty-printer bit
  bit-printer [0] = embed ∣-left ((text [ '0' ] ·
                                   (embed ∣-left nil · nil)) ·
                                  nil)
  bit-printer [1] = ∣-right-doc (<$-doc symbol-doc)

  test₁ : render 4 (bit-printer [0]) ≡ "0"
  test₁ = refl

  test₂ : render 0 (bit-printer [1]) ≡ "1"
  test₂ = refl

module Name where

  -- Lower-case characters.

  Lower-case-char : Set
  Lower-case-char =
    ∃ λ (t : Char) → True (('a' ≤?C t) ×-dec (t ≤?C 'z'))

  lower-case-char : G Lower-case-char
  lower-case-char = sat (λ t → ⌊ ('a' ≤?C t) ×-dec (t ≤?C 'z') ⌋)

  lower-case-char-printer : Pretty-printer lower-case-char
  lower-case-char-printer _ = sat-doc

  -- Note that if we had defined Lower-case-char = Char, then it
  -- wouldn't have been possible to define lower-case-char-printer.

  -- Names. Note that names are allowed to be empty.

  Name : Set
  Name = List Lower-case-char

  name : G Name
  name = ♯ (lower-case-char ⋆)  >>= λ n → ♯ (
         ♯ (whitespace ⋆)       >>= λ _ →
         ♯ return n             )

  name-printer : Pretty-printer name
  name-printer n =
    map-doc lower-case-char-printer n · []-doc · nil

  as : Name
  as = replicate 3 ('a' , _)

  bs : Name
  bs = replicate 5 ('b' , _)

  cs : Name
  cs = replicate 3 ('c' , _)

  ds : Name
  ds = replicate 2 ('d' , _)

  es : Name
  es = replicate 3 ('e' , _)

  fs : Name
  fs = replicate 4 ('f' , _)

  gs : Name
  gs = replicate 2 ('g' , _)

  hs : Name
  hs = replicate 3 ('h' , _)

  is : Name
  is = replicate 2 ('i' , _)

  test : render 80 (name-printer as) ≡ "aaa"
  test = refl

module Name-list where

  open Name

  -- Lists of names. This example is based on one in Swierstra and
  -- Chitil's "Linear, bounded, functional pretty-printing".

  comma-and-name : G Name
  comma-and-name = ♯ symbol [ ',' ]  >>= λ _ →
                   ♯ name

  name-list-body : G (List Name)
  name-list-body = ♯ return []
                 ∣ ♯ (♯ name                >>= λ n  → ♯ (
                      ♯ (comma-and-name ⋆)  >>= λ ns →
                      ♯ return (n ∷ ns)     ))

  name-list : G (List Name)
  name-list = ♯ symbol [ '[' ]  >>= λ _  → ♯ (
              ♯ name-list-body  >>= λ ns → ♯ (
              ♯ symbol [ ']' ]  >>= λ _  →
              ♯ return ns       ))

  comma-and-name-printer : Pretty-printer comma-and-name
  comma-and-name-printer n = group symbol-line-doc · name-printer n

  name-list-printer : Pretty-printer name-list
  name-list-printer ns = symbol-doc · body ns · symbol-doc · nil
    where
    body : Pretty-printer name-list-body
    body []       = ∣-left-doc nil
    body (n ∷ ns) = ∣-right-doc
      (name-printer n · map-doc comma-and-name-printer ns · nil)

  names : List Name
  names = as ∷ bs ∷ cs ∷ ds ∷ es ∷ []

  test₁ : render 80 (name-list-printer names) ≡
          "[aaa, bbbbb, ccc, dd, eee]"
  test₁ = refl

  test₂ : render 11 (name-list-printer names) ≡
          "[aaa,\nbbbbb, ccc,\ndd, eee]"
  test₂ = refl

  test₃ : render 8 (name-list-printer names) ≡
          "[aaa,\nbbbbb,\nccc, dd,\neee]"
  test₃ = refl

module Tree where

  open Name

  -- Trees. This example is based on one in Wadler's "A prettier
  -- printer".

  data Tree : Set where
    node : Name → List Tree → Tree

  mutual

    tree : G Tree
    tree = ♯ name                >>= λ n  → ♯ (
           ♯ brackets            >>= λ ts →
           ♯ return (node n ts)  )

    brackets : G (List Tree)
    brackets = ♯ return []
             ∣ ♯ (♯ symbol [ '[' ]  >>= λ _  → ♯ (
                  ♯ trees           >>= λ ts → ♯ (
                  ♯ symbol [ ']' ]  >>= λ _  →
                  ♯ return ts       )))

    trees : G (List Tree)
    trees = ♯ tree              >>= λ t  → ♯ (
            ♯ commas-and-trees  >>= λ ts →
            ♯ return (t ∷ ts)   )

    commas-and-trees : G (List Tree)
    commas-and-trees = ♯ return []
                     ∣ ♯ (♯ symbol [ ',' ] >>= λ _ →
                          ♯ trees)

  -- Wadler presents two pretty-printers for trees in his final code
  -- listing (§11.7). I've included corresponding implementations
  -- here. (One of Wadler's implementations is buggy: recursive calls
  -- to showTree/showTrees should most likely have referred to
  -- showTree'/showTrees'. The code below is intended to match a
  -- corrected version of Wadler's.)

  module Printer₁ where

    mutual

      tree-printer : Pretty-printer tree
      tree-printer (node s ts) = group
        (name-printer s · nest (length s) (brackets-printer ts) · nil)

      brackets-printer : Pretty-printer brackets
      brackets-printer []       = ∣-left-doc nil
      brackets-printer (t ∷ ts) = ∣-right-doc
        (symbol-doc · nest 1 (trees-printer t ts) · symbol-doc · nil)

      trees-printer : ∀ t ts → Doc trees (t ∷ ts)
      trees-printer t ts =
        tree-printer t · commas-and-trees-printer ts · nil

      commas-and-trees-printer : Pretty-printer commas-and-trees
      commas-and-trees-printer []       = ∣-left-doc nil
      commas-and-trees-printer (t ∷ ts) =
        ∣-right-doc (symbol-line-doc · trees-printer t ts)

  module Printer₂ where

    -- A bunch of lemmas that show that one can append whitespace to
    -- various strings without changing their meanings (with respect
    -- to given grammars, and assuming that these grammars are
    -- unambiguous).

    whitespace⋆-lemma :
      ∀ {x y s₁ s₂} →
      x ∈ whitespace ⋆ ∙ s₁ → y ∈ whitespace + ∙ s₂ →
      x ++ y ∈ whitespace ⋆ ∙ s₁ ++ s₂
    whitespace⋆-lemma (∣-left return) w+ = ∣-right w+
    whitespace⋆-lemma (∣-right (_>>=_ {s₁ = s} w
                                      (_>>=_ {s₁ = s′} w⋆ return))) w+ =
      cast (++-lemma₁ s [] s′ _)
           (∣-right (w >>= (whitespace⋆-lemma w⋆ w+ >>= return)))

    name-lemma : ∀ {n x s₁ s₂} →
                 n ∈ name ∙ s₁ → x ∈ whitespace + ∙ s₂ →
                 n ∈ name ∙ s₁ ++ s₂
    name-lemma (_>>=_ {s₁ = s} n∈ (_>>=_ {s₁ = s′} w⋆ return)) w+ =
      cast (++-lemma₁ s [] s′ _)
           (n∈ >>= (whitespace⋆-lemma w⋆ w+ >>= return))

    symbol-lemma : ∀ {s s′ s₁ s₂ x} →
                   s ∈ symbol s′ ∙ s₁ → x ∈ whitespace + ∙ s₂ →
                   s ∈ symbol s′ ∙ s₁ ++ s₂
    symbol-lemma (_>>=_ {s₁ = s} sym (_>>=_ {s₁ = s′} w⋆ return)) w+ =
      cast (++-lemma₁ s [] s′ _)
           (sym >>= (whitespace⋆-lemma w⋆ w+ >>= return))

    tree-lemma : ∀ {t x s₁ s₂} →
                 t ∈ tree ∙ s₁ → x ∈ whitespace + ∙ s₂ →
                 t ∈ tree ∙ s₁ ++ s₂
    tree-lemma (_>>=_ {s₁ = s} name (∣-left return >>= return)) w+ =
      cast (++-lemma₁ [] [] s _)
           (name-lemma name w+ >>= (∣-left return >>= return))
    tree-lemma (_>>=_ {s₁ = s} name (∣-right (_>>=_ {s₁ = s′} left
                (_>>=_ {s₁ = s″} ts∈ (_>>=_ {s₁ = s‴} right return)))
                >>= return)) w+ =
      cast (++-lemma₂ s s′ s″ s‴ _)
           (name >>= (∣-right (left >>= (ts∈ >>= (symbol-lemma right w+
            >>= return))) >>= return))

    trees-lemma : ∀ {ts x s₁ s₂} →
                  ts ∈ trees ∙ s₁ → x ∈ whitespace + ∙ s₂ →
                  ts ∈ trees ∙ s₁ ++ s₂
    trees-lemma (_>>=_ {s₁ = s} t∈ (∣-left return >>= return)) w+ =
      cast (++-lemma₁ [] [] s _)
           (tree-lemma t∈ w+ >>= (∣-left return >>= return))
    trees-lemma (_>>=_ {s₁ = s} t∈
                       (∣-right (_>>=_ {s₁ = s′} comma ts∈) >>= return))
                w+ =
      cast (++-lemma₁ s s′ _ _)
           (t∈ >>= (∣-right (comma >>= trees-lemma ts∈ w+) >>= return))

    trees′ : G (List Tree)
    trees′ = ♯ trees                 >>= λ ts →
             ♯ (ts <$ whitespace +)

    trees′-lemma : ∀ {ts s} → ts ∈ trees′ ∙ s → ts ∈ trees ∙ s
    trees′-lemma (_>>=_ {s₁ = s₁} ts∈ (w+ >>= return)) =
      cast (P.cong (_++_ s₁) $ P.sym $ proj₂ LM.identity _)
           (trees-lemma ts∈ w+)

    mutual

      tree-printer : Pretty-printer tree
      tree-printer (node s ts) =
        name-printer s · brackets-printer ts · nil

      -- Note that this printer is not defined in exactly the same way
      -- as Wadler's: Wadler used "nest 2" once, here it is used
      -- twice. Why? His one nest spanned over two parts of the
      -- grammar (the opening bracket and the rest, respectively), but
      -- not all of the second part (not the closing bracket).
      --
      -- This issue could probably have been addressed by defining the
      -- grammar in a different way.
      --
      -- This issue also leads me to a question: how expressive is
      -- this pretty-printing framework?

      -- Another observation is that proving trees′-lemma is quite
      -- cumbersome. Could this have been avoided? A simple solution
      -- would have been to add some extra whitespace to the grammar,
      -- at the cost of making the grammar ambiguous. However, I want
      -- to avoid ambiguity. Perhaps there is a better solution.

      brackets-printer : Pretty-printer brackets
      brackets-printer []       = ∣-left-doc nil
      brackets-printer (t ∷ ts) =
        group
          (∣-right-doc
            (nest 2 symbol-line-doc ·
             embed trees′-lemma (nest 2 (trees-printer t ts) · line) ·
             symbol-doc · nil))

      trees-printer : ∀ t ts → Doc trees (t ∷ ts)
      trees-printer t ts =
        tree-printer t · commas-and-trees-printer ts · nil

      commas-and-trees-printer : Pretty-printer commas-and-trees
      commas-and-trees-printer []       = ∣-left-doc nil
      commas-and-trees-printer (t ∷ ts) =
        ∣-right-doc (symbol-line-doc · trees-printer t ts)

  t : Tree
  t = node as
        (node bs
           (node cs [] ∷
            node ds [] ∷
            []) ∷
         node es [] ∷
         node fs
           (node gs [] ∷
            node hs [] ∷
            node is [] ∷
            []) ∷
         [])

  test₁ : render 0 (Printer₁.tree-printer t) ≡
          "aaa[bbbbb[ccc,\n          dd],\n    eee,\n    ffff[gg,\n         hhh,\n         ii]]"
  test₁ = refl

  test₂ : render 30 (Printer₁.tree-printer t) ≡
          "aaa[bbbbb[ccc, dd],\n    eee,\n    ffff[gg, hhh, ii]]"
  test₂ = refl

  test₃ : render 0 (Printer₂.tree-printer t) ≡
          "aaa[\n  bbbbb[\n    ccc,\n    dd\n  ],\n  eee,\n  ffff[\n    gg,\n    hhh,\n    ii\n  ]\n]"
  test₃ = refl

  test₄ : render 80 (Printer₂.tree-printer t) ≡
          "aaa[ bbbbb[ ccc, dd ], eee, ffff[ gg, hhh, ii ] ]"
  test₄ = refl
