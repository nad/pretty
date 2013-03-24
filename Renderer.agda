------------------------------------------------------------------------
-- Document renderers
------------------------------------------------------------------------

module Renderer where

open import Algebra
open import Data.Bool
open import Data.Char
open import Data.List as List hiding ([_])
open import Data.List.NonEmpty using (_∷⁺_)
open import Data.List.Properties using (module List-solver)
open import Data.Nat
open import Data.Product
open import Data.String as String using (String)
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (module Inverse)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

private module LM {A : Set} = Monoid (List.monoid A)

open import Grammar.Infinite as G hiding (_⊛_; _<⊛_; _⊛>_)
open import Pretty using (Doc; Docs; Pretty-printer)
open Pretty.Doc
open Pretty.Docs
open import Utilities

------------------------------------------------------------------------
-- Renderers

record Renderer : Set₁ where
  field
    -- The function that renders.

    render : ∀ {A} {g : Grammar A} {x : A} → Doc g x → List Char

    -- The rendered string must be parsable.

    parsable : ∀ {A} {g : Grammar A} {x : A}
               (d : Doc g x) → x ∈ g ∙ render d

  ----------------------------------------------------------------------
  -- Some derived definitions and properties

  -- Pretty-printers are correct by definition, for any renderer,
  -- assuming that the underlying grammar is unambiguous.

  pretty-printer-correct :
    ∀ {A} {g : Grammar A} (pretty : Pretty-printer g) →
    ∀ x → x ∈ g ∙ render (pretty x)
  pretty-printer-correct pretty x = parsable (pretty x)

  -- If there is only one grammatically correct string, then the
  -- renderer returns this string.

  render-unique-string : ∀ {A} {g : Grammar A} {x s} →
                         (∀ {s′} → x ∈ g ∙ s′ → s′ ≡ s) →
                         (d : Doc g x) → render d ≡ s
  render-unique-string unique d = unique (parsable d)

  -- Thus, in particular, documents for the grammar "string s" are
  -- always rendered in the same way.

  render-string : ∀ {s s′} (d : Doc (string s) s′) → render d ≡ s
  render-string = render-unique-string λ s′∈ →
    P.sym $ proj₂ (Inverse.to string-sem′ ⟨$⟩ s′∈)

  -- The property of ignoring (top-level) emb constructors.

  Ignores-emb : Set₁
  Ignores-emb =
    ∀ {A B x y} {g₁ : Grammar A} {g₂ : Grammar B}
    {f : ∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s} {d : Doc g₁ x} →
    render (emb f d) ≡ render d

  -- If the renderer ignores emb constructors then, for every valid
  -- string, there is a document that renders to that string. (The
  -- renderers below ignore emb.)

  every-string-possible :
    Ignores-emb →
    ∀ {A} {g : Grammar A} {x s} →
    x ∈ g ∙ s → ∃ λ (d : Doc g x) → render d ≡ s
  every-string-possible ignores-emb {g = g} {x} {s} x∈ =
    (Pretty.embed lemma₁ text , lemma₂)
    where
    open P.≡-Reasoning

    lemma₁ : ∀ {s′} → s ∈ string s ∙ s′ → x ∈ g ∙ s′
    lemma₁ s∈ = cast (proj₂ (Inverse.to string-sem′ ⟨$⟩ s∈)) x∈

    lemma₂ = begin
      render (Pretty.embed lemma₁ text)  ≡⟨ ignores-emb ⟩
      render text                        ≡⟨ render-string _ ⟩
      s                                  ∎

------------------------------------------------------------------------
-- An example renderer

-- This renderer replaces every occurrence of "line" with a single
-- space character.

ugly-renderer : Renderer
ugly-renderer = record
  { render   = render
  ; parsable = parsable
  }
  where

  mutual

    render : ∀ {A} {g : Grammar A} {x} → Doc g x → List Char
    render nil            = String.toList ""
    render (text {s = s}) = s
    render (d₁ ◇ d₂)      = render d₁ ++ render d₂
    render line           = String.toList " "
    render (group d)      = render d
    render (nest _ d)     = render d
    render (emb _ d)      = render d
    render (fill ds)      = render-fills ds

    render-fills : ∀ {A} {g : Grammar A} {x} → Docs g x → List Char
    render-fills [ d ]    = render d
    render-fills (d ∷ ds) = render d ++ ' ' ∷ render-fills ds

  mutual

    parsable : ∀ {A x} {g : Grammar A}
               (d : Doc g x) → x ∈ g ∙ render d
    parsable nil        = return-sem
    parsable text       = string-sem
    parsable (d₁ ◇ d₂)  = >>=-sem (parsable d₁) (parsable d₂)
    parsable line       = <$-sem single-space-sem
    parsable (group d)  = parsable d
    parsable (nest _ d) = parsable d
    parsable (emb f d)  = f (parsable d)
    parsable (fill ds)  = parsable-fills ds

    parsable-fills : ∀ {A xs} {g : Grammar A} (ds : Docs g xs) →
                     xs ∈ g sep-by whitespace + ∙ render-fills ds
    parsable-fills [ d ]    = sep-by-sem-singleton (parsable d)
    parsable-fills (d ∷ ds) =
      sep-by-sem-∷ (parsable d) single-space-sem (parsable-fills ds)

-- The "ugly renderer" ignores emb constructors.

ugly-renderer-ignores-emb : Renderer.Ignores-emb ugly-renderer
ugly-renderer-ignores-emb = P.refl

------------------------------------------------------------------------
-- Some general document properties, proved using ugly-renderer

-- For every document of type Doc g x there is a string that witnesses
-- that the value x is generated by the grammar g.

string-exists : ∀ {A} {g : Grammar A} {x} →
                Doc g x → ∃ λ s → x ∈ g ∙ s
string-exists d = (render d , parsable d)
  where open Renderer ugly-renderer

-- Thus, if there is no witness, then there is no document.

no-string⇒no-document : ∀ {A} {g : Grammar A} {x} →
                        (∄ λ s → x ∈ g ∙ s) → ¬ Doc g x
no-string⇒no-document no-witness d = no-witness (string-exists d)

------------------------------------------------------------------------
-- An example renderer, based on the one in Wadler's "A prettier
-- printer"

-- The natural number is the line width.

wadler's-renderer : ℕ → Renderer
wadler's-renderer w = record
  { render   = render
  ; parsable = parsable
  }
  module Wadler's-renderer where

  -- Documents with unions instead of groups, and no fills.

  infixr 20 _◇_

  data DocU : ∀ {A} → Grammar A → A → Set₁ where
    nil   : ∀ {A} {x : A} → DocU (return x) x
    text  : ∀ {s} → DocU (string s) s
    _◇_   : ∀ {c₁ c₂ A B x y}
              {g₁ : ∞Grammar c₁ A} {g₂ : A → ∞Grammar c₂ B} →
            DocU (♭? g₁) x → DocU (♭? (g₂ x)) y → DocU (g₁ >>= g₂) y
    line  : DocU (tt <$ whitespace +) tt
    union : ∀ {A} {g : Grammar A} {x} → DocU g x → DocU g x → DocU g x
    nest  : ∀ {A} {g : Grammar A} {x} → ℕ → DocU g x → DocU g x
    emb   : ∀ {A B} {g₁ : Grammar A} {g₂ : Grammar B} {x y} →
            (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) → DocU g₁ x → DocU g₂ y

  -- Some derived combinators.

  infixl 20 _⊛_ _<⊛_ _⊛>_
  infix  20 <$>_ <$_

  embed : ∀ {A B} {g₁ : Grammar A} {g₂ : Grammar B} {x y} →
          (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) → DocU g₁ x → DocU g₂ y
  embed f (emb g d) = emb (f ∘ g) d
  embed f d         = emb f d

  <$>_ : ∀ {c A B} {f : A → B} {x} {g : ∞Grammar c A} →
         DocU (♭? g) x → DocU (f <$> g) (f x)
  <$> d = embed <$>-sem d

  <$_ : ∀ {A B : Set} {x : A} {y : B} {g} →
        DocU g y → DocU (x <$ g) x
  <$ d = embed <$-sem d

  _⊛_ : ∀ {c₁ c₂ A B f x} {g₁ : ∞Grammar c₁ (A → B)}
          {g₂ : ∞Grammar c₂ A} →
        DocU (♭? g₁) f → DocU (♭? g₂) x → DocU (g₁ G.⊛ g₂) (f x)
  _⊛_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (d₁ ◇ <$> d₂)
    where
    lemma : ∀ {x s} →
            x ∈ (g₁ >>= λ f → f <$> g₂) ∙ s → x ∈ g₁ G.⊛ g₂ ∙ s
    lemma (>>=-sem f∈ (<$>-sem x∈)) = ⊛-sem f∈ x∈

  _<⊛_ : ∀ {c₁ c₂ A B x y} {g₁ : ∞Grammar c₁ A}
           {g₂ : ∞Grammar c₂ B} →
         DocU (♭? g₁) x → DocU (♭? g₂) y → DocU (g₁ G.<⊛ g₂) x
  _<⊛_ {g₁ = g₁} {g₂} d₁ d₂ =
    embed lemma (nil ⊛ d₁ ⊛ d₂)
    where
    lemma : ∀ {x s} →
            x ∈ return (λ x _ → x) G.⊛ g₁ G.⊛ g₂ ∙ s →
            x ∈ g₁ G.<⊛ g₂ ∙ s
    lemma (⊛-sem (⊛-sem return-sem x∈) y∈) = <⊛-sem x∈ y∈

  _⊛>_ : ∀ {c₁ c₂ A B x y} {g₁ : ∞Grammar c₁ A}
           {g₂ : ∞Grammar c₂ B} →
         DocU (♭? g₁) x → DocU (♭? g₂) y → DocU (g₁ G.⊛> g₂) y
  _⊛>_ {g₁ = g₁} {g₂} d₁ d₂ =
    embed lemma (nil ⊛ d₁ ⊛ d₂)
    where
    lemma : ∀ {y s} →
            y ∈ return (λ _ x → x) G.⊛ g₁ G.⊛ g₂ ∙ s →
            y ∈ g₁ G.⊛> g₂ ∙ s
    lemma (⊛-sem (⊛-sem return-sem x∈) y∈) = ⊛>-sem x∈ y∈

  cons : ∀ {A B} {g : Grammar A} {sep : Grammar B} {x xs} →
         DocU g x → DocU (tt <$ sep) tt → DocU (g sep-by sep) xs →
         DocU (g sep-by sep) (x ∷⁺ xs)
  cons {g = g} {sep} d₁ d₂ d₃ =
    embed lemma (<$> d₁ ⊛ (d₂ ⊛> d₃))
    where
    lemma : ∀ {ys s} →
            ys ∈ _∷⁺_ <$> g G.⊛ ((tt <$ sep) G.⊛> (g sep-by sep)) ∙ s →
            ys ∈ g sep-by sep ∙ s
    lemma (⊛-sem (<$>-sem x∈) (⊛>-sem (<$-sem y∈) xs∈)) =
      sep-by-sem-∷ x∈ y∈ xs∈

  -- A single space character.

  space : DocU (tt <$ whitespace +) tt
  space = embed lemma (<$ text)
    where
    lemma : ∀ {s} →
            tt ∈ tt <$ string′ " " ∙ s →
            tt ∈ tt <$ whitespace + ∙ s
    lemma (<$-sem (⊛-sem (<$>-sem tok-sem) return-sem)) =
      <$-sem single-space-sem

  mutual

    -- Replaces line constructors with single spaces, removes groups.

    flatten : ∀ {A} {g : Grammar A} {x} → Doc g x → DocU g x
    flatten nil        = nil
    flatten text       = text
    flatten (d₁ ◇ d₂)  = flatten d₁ ◇ flatten d₂
    flatten line       = space
    flatten (group d)  = flatten d
    flatten (nest i d) = nest i (flatten d)
    flatten (emb f d)  = embed f (flatten d)
    flatten (fill ds)  = flatten-fills ds

    flatten-fills : ∀ {A} {g : Grammar A} {xs} →
                    Docs g xs → DocU (g sep-by whitespace +) xs
    flatten-fills [ d ]    = embed sep-by-sem-singleton (flatten d)
    flatten-fills (d ∷ ds) = cons (flatten d) space (flatten-fills ds)

  mutual

    -- Converts ("expands") groups to unions.

    expand : ∀ {A} {g : Grammar A} {x} → Doc g x → DocU g x
    expand nil        = nil
    expand text       = text
    expand (d₁ ◇ d₂)  = expand d₁ ◇ expand d₂
    expand line       = line
    expand (group d)  = union (flatten d) (expand d)
    expand (nest i d) = nest i (expand d)
    expand (emb f d)  = embed f (expand d)
    expand (fill ds)  = expand-fills false ds

    expand-fills : Bool → -- Unconditionally flatten the first document?
                   ∀ {A} {g : Grammar A} {xs} →
                   Docs g xs → DocU (g sep-by whitespace +) xs
    expand-fills fl [ d ] =
      embed sep-by-sem-singleton (flatten/expand fl d)
    expand-fills fl (d ∷ ds) =
      union (cons (flatten d)           space (expand-fills true  ds))
            (cons (flatten/expand fl d) line  (expand-fills false ds))

    flatten/expand : Bool → -- Flatten?
                     ∀ {A} {g : Grammar A} {x} → Doc g x → DocU g x
    flatten/expand true  d = flatten d
    flatten/expand false d = expand d

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
  best i (d₁ ◇ d₂)      = best i d₁ ∘ best i d₂
  best i line           = λ κ _ → nest-line i ∷ κ i
  best i (union d₁ d₂)  = λ κ c → better c (best i d₁ κ c)
                                           (best i d₂ κ c)
  best i (nest j d)     = best (j + i) d
  best i (emb _ d)      = best i d

  -- Renders a document.

  render : ∀ {A} {g : Grammar A} {x} → Doc g x → List Char
  render d = show (best 0 (expand d) (λ _ → []) 0)

  -- Some simple lemmas.

  replicate-lemma :
    ∀ i → replicate i ' ' ∈ whitespace ⋆ ∙ replicate i ' '
  replicate-lemma zero    = ⋆-[]-sem
  replicate-lemma (suc i) =
    ⋆-∷-sem (left-sem tok-sem) (replicate-lemma i)

  nest-line-lemma :
    ∀ {A} {x : A} i →
    x ∈ x <$ whitespace + ∙ showE (nest-line i)
  nest-line-lemma i =
    <$-sem (+-sem (right-sem tok-sem) (replicate-lemma i))

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
  best-lemma s (emb f d)     hyp = best-lemma s d (hyp ∘ f)
  best-lemma s (d₁ ◇ d₂)     hyp =
    best-lemma s d₁ λ {s′} f∈ →
      cast (LM.assoc s _ _)
        (best-lemma (s ++ s′) d₂ λ x∈ →
           cast (lemma s _ _ _)
             (hyp (>>=-sem f∈ x∈)))
    where
    open List-solver
    lemma = solve 4 (λ a b c d → a ⊕ (b ⊕ c) ⊕ d ⊜ (a ⊕ b) ⊕ c ⊕ d)
                    P.refl

  -- The renderer is correct.

  parsable : ∀ {A} {g : Grammar A} {x}
             (d : Doc g x) → x ∈ g ∙ render d
  parsable d = best-lemma [] (expand d)
                          (cast (P.sym $ proj₂ LM.identity _))

-- Wadler's renderer ignores emb constructors.

wadler's-renderer-ignores-emb :
  ∀ {w} → Renderer.Ignores-emb (wadler's-renderer w)
wadler's-renderer-ignores-emb {w} {d = d}
  with Wadler's-renderer.expand w d
... | Wadler's-renderer.nil       = P.refl
... | Wadler's-renderer.text      = P.refl
... | _ Wadler's-renderer.◇ _     = P.refl
... | Wadler's-renderer.line      = P.refl
... | Wadler's-renderer.union _ _ = P.refl
... | Wadler's-renderer.nest _ _  = P.refl
... | Wadler's-renderer.emb _ _   = P.refl

-- Uses wadler's-renderer to render a document using the given line
-- width.

render : ∀ {A} {g : Grammar A} {x} → ℕ → Doc g x → String
render w d = String.fromList (Renderer.render (wadler's-renderer w) d)
