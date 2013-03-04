------------------------------------------------------------------------
-- Pretty-printing
------------------------------------------------------------------------

module Pretty where

open import Algebra
open import Coinduction
open import Data.Bool
open import Data.Char
open import Data.List as List hiding ([_])
open import Data.List.Properties using (module List-solver)
open import Data.Nat
open import Data.Product
open import Data.String using () renaming (toList to str)
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

private module LM {A : Set} = Monoid (List.monoid A)

open import Grammar.Infinite
open import Tests

infixr 20 _·_ _∷-doc_

------------------------------------------------------------------------
-- Some boring lemmas

private

  ++-lemma₁ : {A : Set} (a b c d : List A) →
              a ++ (b ++ c) ++ d ≡ (a ++ b) ++ c ++ d
  ++-lemma₁ = solve 4 (λ a b c d → a ⊕ (b ⊕ c) ⊕ d ⊜
                                   (a ⊕ b) ⊕ c ⊕ d)
                      refl
    where open List-solver

  ++-lemma₂ : {A : Set} (a b c : List A) →
              a ++ b ++ c ≡ a ++ (b ++ []) ++ c ++ []
  ++-lemma₂ = solve 3 (λ a b c → a ⊕ b ⊕ c ⊜ a ⊕ (b ⊕ nil) ⊕ c ⊕ nil)
                      refl
    where open List-solver

------------------------------------------------------------------------
-- Pretty-printers

mutual

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
    fill  : ∀ {A} {g : G A} {xs} →
            Docs g xs → Doc (g sep-by whitespace +) xs

  -- Sequences of documents, all based on the same grammar.

  data Docs {A} (g : G A) : List A → Set₁ where
    [_] : ∀ {x} → Doc g x → Docs g (x ∷ [])
    _∷_ : ∀ {x xs} → Doc g x → Docs g xs → Docs g (x ∷ xs)

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
token-doc {t} = embed lemma (text (t ∷ []))
  where
  lemma : ∀ {s} → t ∷ [] ∈ string (t ∷ []) ∙ s → t ∈ token ∙ s
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

-- A variant of line (with _⋆ instead of _+ in the grammar).

line⋆ : ∀ {A} {x : A} → Doc (x <$ whitespace ⋆) x
line⋆ {x = x} = embed lemma line
  where
  lemma : ∀ {s} →
          x ∈ x <$ whitespace + ∙ s →
          x ∈ x <$ whitespace ⋆ ∙ s
  lemma (w+ >>= return) = ∣-right w+ >>= return

-- A document for the given symbol (and no following whitespace).

symbol-doc : ∀ {s} → Doc (symbol s) s
symbol-doc = text _ · <$-doc []-doc

-- A document for the given symbol plus a "line".

symbol-line-doc : ∀ {s} → Doc (symbol s) s
symbol-line-doc = text _ · line⋆

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

  mutual

    render : ∀ {A} {g : G A} {x} → Doc g x → List Char
    render nil         = []
    render (text s)    = s
    render (d₁ · d₂)   = render d₁ ++ render d₂
    render line        = str " "
    render (group d)   = render d
    render (nest _ d)  = render d
    render (embed _ d) = render d
    render (fill ds)   = render-fills ds

    render-fills : ∀ {A} {g : G A} {x} → Docs g x → List Char
    render-fills [ d ]    = render d
    render-fills (d ∷ ds) = render d ++ ' ' ∷ render-fills ds

  mutual

    parsable : ∀ {A x} {g : G A} (d : Doc g x) → x ∈ g ∙ render d
    parsable nil         = return
    parsable (text s)    = string-sem s
    parsable (d₁ · d₂)   = parsable d₁ >>= parsable d₂
    parsable line        = <$-sem single-space-sem
    parsable (group d)   = parsable d
    parsable (nest _ d)  = parsable d
    parsable (embed f d) = f (parsable d)
    parsable (fill ds)   = parsable-fills ds

    parsable-fills : ∀ {A xs} {g : G A} (ds : Docs g xs) →
                     xs ∈ g sep-by whitespace + ∙ render-fills ds
    parsable-fills [ d ]    = sep-by-sem-singleton (parsable d)
    parsable-fills (d ∷ ds) =
      sep-by-sem-cons (parsable d) single-space-sem (parsable-fills ds)

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

  -- A single space character.

  space : ∀ {A} {x : A} → DocU (x <$ whitespace +) x
  space = embed lemma (text (str " ")) · nil
    where
    lemma : ∀ {x s} →
            x ∈ string (str " ") ∙ s →
            x ∈ whitespace + ∙ s
    lemma (space >>= (return >>= return)) =
      ∷-sem+ (∣-left space) []-sem

  -- Utility function used by the fill machinery.

  cons : ∀ {A} {g : G A} {x xs} →
         DocU g x → DocU (tt <$ whitespace +) tt →
         DocU (g sep-by whitespace +) xs →
         DocU (g sep-by whitespace +) (x ∷ xs)
  cons {g = g} d₁ d₂ d₃ = embed lemma (d₁ · d₂ · d₃ · nil)
    where
    lemma : ∀ {xs s} →
            xs ∈ (g                       ≫= λ x →
                  (tt <$ whitespace +)    >>
                  (g sep-by whitespace +  ≫= λ xs →
                   return (x ∷ xs))) ∙ s →
            xs ∈ g sep-by whitespace + ∙ s
    lemma (_>>=_ {s₁ = s₁} x∈ (_>>=_ {s₁ = s₂} w+ return >>=
                               (xs∈ >>= return))) =
      cast (++-lemma₂ s₁ s₂ _) (sep-by-sem-cons x∈ w+ xs∈)

  mutual

    -- Replaces line constructors with single spaces, removes groups.

    flatten : ∀ {A} {g : G A} {x} → Doc g x → DocU g x
    flatten nil         = nil
    flatten (text s)    = text s
    flatten (d₁ · d₂)   = flatten d₁ · flatten d₂
    flatten line        = space
    flatten (group d)   = flatten d
    flatten (nest i d)  = nest i (flatten d)
    flatten (embed f d) = embed f (flatten d)
    flatten (fill ds)   = flatten-fills ds

    flatten-fills : ∀ {A} {g : G A} {xs} →
                    Docs g xs → DocU (g sep-by whitespace +) xs
    flatten-fills [ d ]    = embed sep-by-sem-singleton (flatten d)
    flatten-fills (d ∷ ds) = cons (flatten d) space (flatten-fills ds)

  mutual

    -- Conversion of Docs to DocUs.

    expand-groups : ∀ {A} {g : G A} {x} → Doc g x → DocU g x
    expand-groups nil         = nil
    expand-groups (text s)    = text s
    expand-groups (d₁ · d₂)   = expand-groups d₁ · expand-groups d₂
    expand-groups line        = line
    expand-groups (group d)   = union (flatten d) (expand-groups d)
    expand-groups (nest i d)  = nest i (expand-groups d)
    expand-groups (embed f d) = embed f (expand-groups d)
    expand-groups (fill ds)   = expand-fills false ds

    expand-fills : Bool → -- Unconditionally flatten the first document?
                   ∀ {A} {g : G A} {xs} →
                   Docs g xs → DocU (g sep-by whitespace +) xs
    expand-fills fl [ d ] =
      embed sep-by-sem-singleton (flatten/expand fl d)
    expand-fills fl (d ∷ ds) =
      union (cons (flatten d)           space (expand-fills true  ds))
            (cons (flatten/expand fl d) line  (expand-fills false ds))

    flatten/expand : Bool → -- Flatten?
                     ∀ {A} {g : G A} {x} → Doc g x → DocU g x
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
           cast (++-lemma₁ s _ _ _)
             (hyp (f∈ >>= x∈)))

  -- The renderer is correct.

  parsable : ∀ {A} {g : G A} {x} (d : Doc g x) → x ∈ g ∙ render d
  parsable d = best-lemma [] (expand-groups d)
                          (cast (P.sym $ proj₂ LM.identity _))
