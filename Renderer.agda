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
import Relation.Binary.PropositionalEquality as P

private module LM {A : Set} = Monoid (List.monoid A)

open import Grammar.Infinite
open import Pretty
open import Utilities

-- Renderers.

record Renderer : Set₁ where
  field
    -- The function that renders.

    render : ∀ {A} {g : Grammar A} {x : A} → Doc g x → List Char

    -- The rendered string must be parsable.

    parsable : ∀ {A} {g : Grammar A} {x : A}
               (d : Doc g x) → x ∈ g ∙ render d

  -- Pretty-printers are correct by definition, for any renderer,
  -- assuming that the underlying grammar is unambiguous.

  pretty-printer-correct :
    ∀ {A} {g : Grammar A} (pretty : Pretty-printer g) →
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

    render : ∀ {A} {g : Grammar A} {x} → Doc g x → List Char
    render nil            = []
    render (text {s = s}) = s
    render (d₁ · d₂)      = render d₁ ++ render d₂
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
    parsable (d₁ · d₂)  = >>=-sem (parsable d₁) (parsable d₂)
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

-- An example renderer, based on the one in Wadler's "A prettier
-- printer".
--
-- The natural number is the line width.

wadler's-renderer : ℕ → Renderer
wadler's-renderer w = record
  { render   = render
  ; parsable = parsable
  }
  where

  -- Documents with unions instead of groups, and no fills.

  infixr 20 _·_

  data DocU : ∀ {A} → Grammar A → A → Set₁ where
    nil   : ∀ {A} {x : A} → DocU (return x) x
    text  : ∀ {s} → DocU (string s) s
    _·_   : ∀ {c₁ c₂ A B x y}
              {g₁ : ∞Grammar c₁ A} {g₂ : A → ∞Grammar c₂ B} →
            DocU (♭? g₁) x → DocU (♭? (g₂ x)) y → DocU (g₁ >>= g₂) y
    line  : DocU (tt <$ whitespace +) tt
    union : ∀ {A} {g : Grammar A} {x} → DocU g x → DocU g x → DocU g x
    nest  : ∀ {A} {g : Grammar A} {x} → ℕ → DocU g x → DocU g x
    emb   : ∀ {A B} {g₁ : Grammar A} {g₂ : Grammar B} {x y} →
            (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) → DocU g₁ x → DocU g₂ y

  -- Some derived combinators.

  infixl 20 _⊛-docU_ _<⊛-docU_ _⊛>-docU_

  embedU : ∀ {A B} {g₁ : Grammar A} {g₂ : Grammar B} {x y} →
           (∀ {s} → x ∈ g₁ ∙ s → y ∈ g₂ ∙ s) → DocU g₁ x → DocU g₂ y
  embedU f (emb g d) = emb (f ∘ g) d
  embedU f d         = emb f d

  <$>-docU : ∀ {c A B} {f : A → B} {x} {g : ∞Grammar c A} →
             DocU (♭? g) x → DocU (f <$> g) (f x)
  <$>-docU d = embedU <$>-sem d

  _⊛-docU_ : ∀ {c₁ c₂ A B f x} {g₁ : ∞Grammar c₁ (A → B)}
               {g₂ : ∞Grammar c₂ A} →
             DocU (♭? g₁) f → DocU (♭? g₂) x → DocU (g₁ ⊛ g₂) (f x)
  _⊛-docU_ {g₁ = g₁} {g₂} d₁ d₂ = embedU lemma (d₁ · <$>-docU d₂)
    where
    lemma : ∀ {x s} →
            x ∈ (g₁ >>= λ f → f <$> g₂) ∙ s → x ∈ g₁ ⊛ g₂ ∙ s
    lemma (>>=-sem f∈ (<$>-sem x∈)) = ⊛-sem f∈ x∈

  _<⊛-docU_ : ∀ {c₁ c₂ A B x y} {g₁ : ∞Grammar c₁ A}
                {g₂ : ∞Grammar c₂ B} →
              DocU (♭? g₁) x → DocU (♭? g₂) y → DocU (g₁ <⊛ g₂) x
  _<⊛-docU_ {g₁ = g₁} {g₂} d₁ d₂ =
    embedU lemma (nil ⊛-docU d₁ ⊛-docU d₂)
    where
    lemma : ∀ {x s} →
            x ∈ return (λ x _ → x) ⊛ g₁ ⊛ g₂ ∙ s → x ∈ g₁ <⊛ g₂ ∙ s
    lemma (⊛-sem (⊛-sem return-sem x∈) y∈) = <⊛-sem x∈ y∈

  _⊛>-docU_ : ∀ {c₁ c₂ A B x y} {g₁ : ∞Grammar c₁ A}
                {g₂ : ∞Grammar c₂ B} →
              DocU (♭? g₁) x → DocU (♭? g₂) y → DocU (g₁ ⊛> g₂) y
  _⊛>-docU_ {g₁ = g₁} {g₂} d₁ d₂ =
    embedU lemma (nil ⊛-docU d₁ ⊛-docU d₂)
    where
    lemma : ∀ {y s} →
            y ∈ return (λ _ x → x) ⊛ g₁ ⊛ g₂ ∙ s → y ∈ g₁ ⊛> g₂ ∙ s
    lemma (⊛-sem (⊛-sem return-sem x∈) y∈) = ⊛>-sem x∈ y∈

  <$-docU : ∀ {A B : Set} {x : A} {y : B} {g} →
            DocU g y → DocU (x <$ g) x
  <$-docU d = nil <⊛-docU d

  cons : ∀ {A B} {g : Grammar A} {sep : Grammar B} {x xs} →
         DocU g x → DocU (tt <$ sep) tt → DocU (g sep-by sep) xs →
         DocU (g sep-by sep) (x ∷⁺ xs)
  cons {g = g} {sep} d₁ d₂ d₃ =
    embedU lemma (<$>-docU d₁ ⊛-docU (d₂ ⊛>-docU d₃))
    where
    lemma : ∀ {ys s} →
            ys ∈ _∷⁺_ <$> g ⊛ ((tt <$ sep) ⊛> (g sep-by sep)) ∙ s →
            ys ∈ g sep-by sep ∙ s
    lemma (⊛-sem (<$>-sem x∈) (⊛>-sem (<⊛-sem return-sem y∈) xs∈)) =
      sep-by-sem-∷ x∈ y∈ xs∈

  -- A single space character.

  space : DocU (tt <$ whitespace +) tt
  space = embedU lemma (<$-docU text)
    where
    lemma : ∀ {s} →
            tt ∈ tt <$ string′ " " ∙ s →
            tt ∈ tt <$ whitespace + ∙ s
    lemma (<⊛-sem return-sem (⊛-sem (<$>-sem tok-sem) return-sem)) =
      <$-sem single-space-sem

  mutual

    -- Replaces line constructors with single spaces, removes groups.

    flatten : ∀ {A} {g : Grammar A} {x} → Doc g x → DocU g x
    flatten nil        = nil
    flatten text       = text
    flatten (d₁ · d₂)  = flatten d₁ · flatten d₂
    flatten line       = space
    flatten (group d)  = flatten d
    flatten (nest i d) = nest i (flatten d)
    flatten (emb f d)  = embedU f (flatten d)
    flatten (fill ds)  = flatten-fills ds

    flatten-fills : ∀ {A} {g : Grammar A} {xs} →
                    Docs g xs → DocU (g sep-by whitespace +) xs
    flatten-fills [ d ]    = embedU sep-by-sem-singleton (flatten d)
    flatten-fills (d ∷ ds) = cons (flatten d) space (flatten-fills ds)

  mutual

    -- Conversion of Docs to DocUs.

    expand-groups : ∀ {A} {g : Grammar A} {x} → Doc g x → DocU g x
    expand-groups nil        = nil
    expand-groups text       = text
    expand-groups (d₁ · d₂)  = expand-groups d₁ · expand-groups d₂
    expand-groups line       = line
    expand-groups (group d)  = union (flatten d) (expand-groups d)
    expand-groups (nest i d) = nest i (expand-groups d)
    expand-groups (emb f d)  = embedU f (expand-groups d)
    expand-groups (fill ds)  = expand-fills false ds

    expand-fills : Bool → -- Unconditionally flatten the first document?
                   ∀ {A} {g : Grammar A} {xs} →
                   Docs g xs → DocU (g sep-by whitespace +) xs
    expand-fills fl [ d ] =
      embedU sep-by-sem-singleton (flatten/expand fl d)
    expand-fills fl (d ∷ ds) =
      union (cons (flatten d)           space (expand-fills true  ds))
            (cons (flatten/expand fl d) line  (expand-fills false ds))

    flatten/expand : Bool → -- Flatten?
                     ∀ {A} {g : Grammar A} {x} → Doc g x → DocU g x
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

  best : ∀ {A} {g : Grammar A} {x} →
         ℕ → DocU g x → (ℕ → Layout) → (ℕ → Layout)
  best i nil            = id
  best i (text {s = s}) = λ κ c → text s ∷ κ (length s + c)
  best i (d₁ · d₂)      = best i d₁ ∘ best i d₂
  best i line           = λ κ _ → nest-line i ∷ κ i
  best i (union d₁ d₂)  = λ κ c → better c (best i d₁ κ c)
                                           (best i d₂ κ c)
  best i (nest j d)     = best (j + i) d
  best i (emb _ d)      = best i d

  -- Renders a document.

  render : ∀ {A} {g : Grammar A} {x} → Doc g x → List Char
  render d = show (best 0 (expand-groups d) (λ _ → []) 0)

  -- Some simple lemmas.

  replicate-lemma :
    ∀ i → replicate i ' ' ∈ whitespace ⋆ ∙ replicate i ' '
  replicate-lemma zero    = ⋆-[]-sem
  replicate-lemma (suc i) =
    ⋆-∷-sem (∣-left-sem tok-sem) (replicate-lemma i)

  nest-line-lemma :
    ∀ {A} {x : A} i →
    x ∈ x <$ whitespace + ∙ showE (nest-line i)
  nest-line-lemma i =
    <$-sem (+-sem (∣-right-sem tok-sem) (replicate-lemma i))

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
  best-lemma s (d₁ · d₂)     hyp =
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
  parsable d = best-lemma [] (expand-groups d)
                          (cast (P.sym $ proj₂ LM.identity _))

-- Uses wadler's-renderer to render a document using the given line
-- width.

render : ∀ {A} {g : Grammar A} {x} → ℕ → Doc g x → String
render w d = String.fromList (Renderer.render (wadler's-renderer w) d)