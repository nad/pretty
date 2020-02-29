------------------------------------------------------------------------
-- Document renderers
------------------------------------------------------------------------

module Renderer where

open import Algebra
open import Data.Bool
open import Data.Char using (Char)
open import Data.Empty
open import Data.Integer using (ℤ; +_; -[1+_]; _-_; _⊖_)
open import Data.List as List hiding ([_])
open import Data.List.NonEmpty using (_∷⁺_)
open import Data.List.Properties
open import Data.Nat
open import Data.Product
open import Data.String as String using (String)
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (module Inverse)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Tactic.MonoidSolver

private
  module LM {A : Set} = Monoid (++-monoid A)

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
               (d : Doc g x) → x ∈ g · render d

  ----------------------------------------------------------------------
  -- Some derived definitions and properties

  -- Pretty-printers are correct by definition, for any renderer,
  -- assuming that the underlying grammar is unambiguous.

  correct :
    ∀ {A} {g : Grammar A} (pretty : Pretty-printer g) →
    ∀ x → x ∈ g · render (pretty x)
  correct pretty x = parsable (pretty x)

  correct-if-locally-unambiguous :
    ∀ {A} {g : Grammar A} →
    (parse : Parser g) (pretty : Pretty-printer g) →
    ∀ x →
    Locally-unambiguous g (render (pretty x)) →
    ∃ λ p → parse (render (pretty x)) ≡ yes (x , p)
  correct-if-locally-unambiguous parse pretty x unambiguous = c
    where
    c : ∃ λ p → parse (render (pretty x)) ≡ yes (x , p)
    c with parse (render (pretty x))
    c | no  no-parse   = ⊥-elim (no-parse (x , correct pretty x))
    c | yes (y  , y∈g) with unambiguous y∈g (correct pretty x)
    c | yes (.x , x∈g) | P.refl = (x∈g , P.refl)

  correct-if-unambiguous :
    ∀ {A} {g : Grammar A} →
    Unambiguous g → (parse : Parser g) (pretty : Pretty-printer g) →
    ∀ x → ∃ λ p → parse (render (pretty x)) ≡ yes (x , p)
  correct-if-unambiguous unambiguous parse pretty x =
    correct-if-locally-unambiguous parse pretty x unambiguous

  -- If there is only one grammatically correct string, then the
  -- renderer returns this string.

  render-unique-string : ∀ {A} {g : Grammar A} {x s} →
                         (∀ {s′} → x ∈ g · s′ → s′ ≡ s) →
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
      {f : ∀ {s} → x ∈ g₁ · s → y ∈ g₂ · s} {d : Doc g₁ x} →
    render (emb f d) ≡ render d

  -- If the renderer ignores emb constructors then, for every valid
  -- string, there is a document that renders as that string. (The
  -- renderers below ignore emb.)

  every-string-possible :
    Ignores-emb →
    ∀ {A} {g : Grammar A} {x s} →
    x ∈ g · s → ∃ λ (d : Doc g x) → render d ≡ s
  every-string-possible ignores-emb {g = g} {x} {s} x∈ =
    (Pretty.embed lemma₁ text , lemma₂)
    where
    open P.≡-Reasoning

    lemma₁ : ∀ {s′} → s ∈ string s · s′ → x ∈ g · s′
    lemma₁ s∈ = cast (proj₂ (Inverse.to string-sem′ ⟨$⟩ s∈)) x∈

    lemma₂ = begin
      render (Pretty.embed lemma₁ text)  ≡⟨ ignores-emb ⟩
      render text                        ≡⟨ render-string _ ⟩
      s                                  ∎

------------------------------------------------------------------------
-- An example renderer

-- This renderer renders every occurrence of "line" as a single space
-- character.

ugly-renderer : Renderer
ugly-renderer = record
  { render   = render
  ; parsable = parsable
  }
  where

  mutual

    render : ∀ {A} {g : Grammar A} {x} → Doc g x → List Char
    render (d₁ ◇ d₂)      = render d₁ ++ render d₂
    render (text {s = s}) = s
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
               (d : Doc g x) → x ∈ g · render d
    parsable (d₁ ◇ d₂)  = >>=-sem (parsable d₁) (parsable d₂)
    parsable text       = string-sem
    parsable line       = <$-sem single-space-sem
    parsable (group d)  = parsable d
    parsable (nest _ d) = parsable d
    parsable (emb f d)  = f (parsable d)
    parsable (fill ds)  = parsable-fills ds

    parsable-fills : ∀ {A xs} {g : Grammar A} (ds : Docs g xs) →
                     xs ∈ g sep-by whitespace + · render-fills ds
    parsable-fills [ d ]    = sep-by-sem-singleton (parsable d)
    parsable-fills (d ∷ ds) =
      sep-by-sem-∷ (parsable d) single-space-sem (parsable-fills ds)

-- The "ugly renderer" ignores emb constructors.

ugly-renderer-ignores-emb : Renderer.Ignores-emb ugly-renderer
ugly-renderer-ignores-emb = P.refl

------------------------------------------------------------------------
-- A general document property, proved using ugly-renderer

-- For every document of type Doc g x there is a string that witnesses
-- that the value x is generated by the grammar g.

string-exists : ∀ {A} {g : Grammar A} {x} →
                Doc g x → ∃ λ s → x ∈ g · s
string-exists d = (render d , parsable d)
  where open Renderer ugly-renderer

------------------------------------------------------------------------
-- An example renderer, based on the one in Wadler's "A prettier
-- printer"

module Wadler's-renderer where

  -- Layouts (representations of certain strings).

  data Layout-element : Set where
    text : List Char → Layout-element
    line : ℕ         → Layout-element

  Layout : Set
  Layout = List Layout-element

  -- Conversion of layouts into strings.

  show-element : Layout-element → List Char
  show-element (text s) = s
  show-element (line i) = '\n' ∷ replicate i ' '

  show : Layout → List Char
  show = concat ∘ List.map show-element

  -- Documents with unions instead of groups, and no fills. An extra
  -- index—the nesting level—is also included, and the line
  -- combinator's type is more precise (it can't be used for single
  -- spaces, only for newline-plus-indentation).

  infixr 20 _◇_

  data DocN : ∀ {A} → ℕ → Grammar A → A → Set₁ where
    _◇_   : ∀ {i c₁ c₂ A B x y}
              {g₁ : ∞Grammar c₁ A} {g₂ : A → ∞Grammar c₂ B} →
            DocN i (♭? g₁) x → DocN i (♭? (g₂ x)) y →
            DocN i (g₁ >>= g₂) y
    text  : ∀ {i} (s : List Char) → DocN i (string s) s
    line  : (i : ℕ) →
            let s = show-element (line i) in
            DocN i (string s) s
    union : ∀ {i A} {g : Grammar A} {x} →
            DocN i g x → DocN i g x → DocN i g x
    nest  : ∀ {i A} {g : Grammar A} {x}
            (j : ℕ) → DocN (j + i) g x → DocN i g x
    emb   : ∀ {i A B} {g₁ : Grammar A} {g₂ : Grammar B} {x y} →
            (∀ {s} → x ∈ g₁ · s → y ∈ g₂ · s) →
            DocN i g₁ x → DocN i g₂ y

  -- Some derived combinators.

  infix  21 <$>_
  infixl 20 _⊛_ _⊛>_

  embed : ∀ {i A B} {g₁ : Grammar A} {g₂ : Grammar B} {x y} →
          (∀ {s} → x ∈ g₁ · s → y ∈ g₂ · s) → DocN i g₁ x → DocN i g₂ y
  embed f (emb g d) = emb (f ∘ g) d
  embed f d         = emb f d

  nil : ∀ {i A} {x : A} → DocN i (return x) x
  nil = embed lemma (text [])
    where
    lemma : ∀ {x s} → [] ∈ string [] · s → x ∈ return x · s
    lemma return-sem = return-sem

  <$>_ : ∀ {i c A B} {f : A → B} {x} {g : ∞Grammar c A} →
         DocN i (♭? g) x → DocN i (f <$> g) (f x)
  <$> d = embed <$>-sem d

  _⊛_ : ∀ {i c₁ c₂ A B f x} {g₁ : ∞Grammar c₁ (A → B)}
          {g₂ : ∞Grammar c₂ A} →
        DocN i (♭? g₁) f → DocN i (♭? g₂) x → DocN i (g₁ G.⊛ g₂) (f x)
  _⊛_ {g₁ = g₁} {g₂} d₁ d₂ = embed lemma (d₁ ◇ <$> d₂)
    where
    lemma : ∀ {x s} →
            x ∈ (g₁ >>= λ f → f <$> g₂) · s → x ∈ g₁ G.⊛ g₂ · s
    lemma (>>=-sem f∈ (<$>-sem x∈)) = ⊛-sem f∈ x∈

  _⊛>_ : ∀ {i c₁ c₂ A B x y} {g₁ : ∞Grammar c₁ A}
           {g₂ : ∞Grammar c₂ B} →
         DocN i (♭? g₁) x → DocN i (♭? g₂) y → DocN i (g₁ G.⊛> g₂) y
  _⊛>_ {g₁ = g₁} {g₂} d₁ d₂ =
    embed lemma (nil ⊛ d₁ ⊛ d₂)
    where
    lemma : ∀ {y s} →
            y ∈ return (λ _ x → x) G.⊛ g₁ G.⊛ g₂ · s →
            y ∈ g₁ G.⊛> g₂ · s
    lemma (⊛-sem (⊛-sem return-sem x∈) y∈) = ⊛>-sem x∈ y∈

  cons : ∀ {i A B} {g : Grammar A} {sep : Grammar B} {x xs} →
         DocN i g x → DocN i (tt <$ sep) tt → DocN i (g sep-by sep) xs →
         DocN i (g sep-by sep) (x ∷⁺ xs)
  cons {g = g} {sep} d₁ d₂ d₃ =
    embed lemma (<$> d₁ ⊛ (d₂ ⊛> d₃))
    where
    lemma : ∀ {ys s} →
            ys ∈ _∷⁺_ <$> g G.⊛ ((tt <$ sep) G.⊛> (g sep-by sep)) · s →
            ys ∈ g sep-by sep · s
    lemma (⊛-sem (<$>-sem x∈) (⊛>-sem (<$-sem y∈) xs∈)) =
      sep-by-sem-∷ x∈ y∈ xs∈

  -- A single space character.

  imprecise-space : ∀ {i} → DocN i (tt <$ whitespace +) tt
  imprecise-space = embed lemma (text (String.toList " "))
    where
    lemma : ∀ {s} →
            String.toList " " ∈ string′ " " · s →
            tt ∈ tt <$ whitespace + · s
    lemma s∈ =
      cast (proj₂ (Inverse.to string-sem′ ⟨$⟩ s∈))
           (<$-sem single-space-sem)

  -- A variant of line that has the same type as Pretty.line (except
  -- for the indentation index).

  imprecise-line : (i : ℕ) → DocN i (tt <$ whitespace +) tt
  imprecise-line i = embed lemma (line i)
    where
    replicate-lemma :
      ∀ i → replicate i ' ' ∈ whitespace ⋆ · replicate i ' '
    replicate-lemma zero    = ⋆-[]-sem
    replicate-lemma (suc i) =
      ⋆-∷-sem (left-sem tok-sem) (replicate-lemma i)

    lemma : ∀ {i s′} →
            let s = show-element (line i) in
            s ∈ string s · s′ → tt ∈ tt <$ whitespace + · s′
    lemma s∈ =
      cast (proj₂ (Inverse.to string-sem′ ⟨$⟩ s∈))
           (<$-sem (+-sem (right-sem tok-sem) (replicate-lemma _)))

  mutual

    -- Replaces line constructors with single spaces, removes groups.

    flatten : ∀ {i A} {g : Grammar A} {x} → Doc g x → DocN i g x
    flatten (d₁ ◇ d₂)  = flatten d₁ ◇ flatten d₂
    flatten text       = text _
    flatten line       = imprecise-space
    flatten (group d)  = flatten d
    flatten (nest _ d) = flatten d
    flatten (emb f d)  = embed f (flatten d)
    flatten (fill ds)  = flatten-fills ds

    flatten-fills : ∀ {i A} {g : Grammar A} {xs} →
                    Docs g xs → DocN i (g sep-by whitespace +) xs
    flatten-fills [ d ]    = embed sep-by-sem-singleton (flatten d)
    flatten-fills (d ∷ ds) =
      cons (flatten d) imprecise-space (flatten-fills ds)

  mutual

    -- Converts ("expands") groups to unions.

    expand : ∀ {i A} {g : Grammar A} {x} → Doc g x → DocN i g x
    expand (d₁ ◇ d₂)  = expand d₁ ◇ expand d₂
    expand text       = text _
    expand line       = imprecise-line _
    expand (group d)  = union (flatten d) (expand d)
    expand (nest j d) = nest j (expand d)
    expand (emb f d)  = embed f (expand d)
    expand (fill ds)  = expand-fills false ds

    expand-fills : Bool → -- Unconditionally flatten the first document?
                   ∀ {i A} {g : Grammar A} {xs} →
                   Docs g xs → DocN i (g sep-by whitespace +) xs
    expand-fills fl [ d ] =
      embed sep-by-sem-singleton (flatten/expand fl d)
    expand-fills fl (d ∷ ds) =
      union (cons (flatten d)           imprecise-space    (expand-fills true  ds))
            (cons (flatten/expand fl d) (imprecise-line _) (expand-fills false ds))

    flatten/expand : Bool → -- Flatten?
                     ∀ {i A} {g : Grammar A} {x} → Doc g x → DocN i g x
    flatten/expand true  d = flatten d
    flatten/expand false d = expand d

  -- Does the first line of the layout fit on a line with the given
  -- number of characters?

  fits : ℤ → Layout → Bool
  fits -[1+ w ] _            = false
  fits w        []           = true
  fits w        (text s ∷ x) = fits (w - + length s) x
  fits w        (line i ∷ x) = true

  module _ (width : ℕ) where

    -- Chooses the first layout if it fits, otherwise the second. The
    -- natural number is the current column number.

    better : ℕ → Layout → Layout → Layout
    better c x y = if fits (width ⊖ c) x then x else y

    -- If, for any starting column c, κ c is the layout for some text,
    -- then best i d κ c is the layout for the document d followed by
    -- this text, given the current indentation i and the current column
    -- number c.

    best : ∀ {i A} {g : Grammar A} {x} →
           DocN i g x → (ℕ → Layout) → (ℕ → Layout)
    best (d₁ ◇ d₂)     = best d₁ ∘ best d₂
    best (text [])     = id
    best (text s)      = λ κ c → text s ∷ κ (length s + c)
    best (line i)      = λ κ _ → line i ∷ κ i
    best (union d₁ d₂) = λ κ c → better c (best d₁ κ c)
                                          (best d₂ κ c)
    best (nest _ d)    = best d
    best (emb _ d)     = best d

    -- Renders a document.

    renderN : ∀ {A i} {g : Grammar A} {x} → DocN i g x → List Char
    renderN d = show (best d (λ _ → []) 0)

    -- Renders a document.

    render : ∀ {A} {g : Grammar A} {x} → Doc g x → List Char
    render d = renderN (expand {i = 0} d)

    -- A simple lemma.

    if-lemma :
      ∀ {A} {g : Grammar A} {x l₁ l₂} s b →
      x ∈ g · s ++ show l₁ →
      x ∈ g · s ++ show l₂ →
      x ∈ g · s ++ show (if b then l₁ else l₂)
    if-lemma _ true  ∈l₁ ∈l₂ = ∈l₁
    if-lemma _ false ∈l₁ ∈l₂ = ∈l₂

    -- The main correctness property for best.

    best-lemma :
      ∀ {c A B i} {g : Grammar A} {g′ : Grammar B} {x y κ}
        s (d : DocN i g x) →
      (∀ {s′ c′} → x ∈ g · s′ → y ∈ g′ · s ++ s′ ++ show (κ c′)) →
      y ∈ g′ · s ++ show (best d κ c)
    best-lemma     s (text [])      hyp = hyp return-sem
    best-lemma     s (text (_ ∷ _)) hyp = hyp string-sem
    best-lemma     s (line i)       hyp = hyp string-sem
    best-lemma {c} s (union d₁ d₂)  hyp = if-lemma s
                                            (fits (width ⊖ c) _)
                                            (best-lemma s d₁ hyp)
                                            (best-lemma s d₂ hyp)
    best-lemma     s (nest _ d)     hyp = best-lemma s d hyp
    best-lemma     s (emb f d)      hyp = best-lemma s d (hyp ∘ f)
    best-lemma     s (d₁ ◇ d₂)      hyp =
      best-lemma s d₁ λ {s′} f∈ →
        cast (LM.assoc s _ _)
          (best-lemma (s ++ s′) d₂ λ x∈ →
             cast lemma
               (hyp (>>=-sem f∈ x∈)))
      where
      lemma :
        ∀ {s′ s″ s‴} →
        s ++ (s′ ++ s″) ++ s‴ ≡ (s ++ s′) ++ s″ ++ s‴
      lemma = solve (++-monoid Char)

    -- A corollary.

    best-lemma′ :
      ∀ {A i} {g : Grammar A} {x}
      (d : DocN i g x) → x ∈ g · renderN d
    best-lemma′ d = best-lemma [] d (cast (P.sym $ proj₂ LM.identity _))

    -- The renderer is correct.

    parsable : ∀ {A} {g : Grammar A} {x}
               (d : Doc g x) → x ∈ g · render d
    parsable d = best-lemma′ (expand d)

    -- The renderer.

    wadler's-renderer : Renderer
    wadler's-renderer = record
      { render   = render
      ; parsable = parsable
      }

  -- The renderer ignores emb constructors.

  ignores-emb :
    ∀ {w} → Renderer.Ignores-emb (wadler's-renderer w)
  ignores-emb {d = d} with expand {i = 0} d
  ... | _ ◇ _     = P.refl
  ... | text _    = P.refl
  ... | line ._   = P.refl
  ... | union _ _ = P.refl
  ... | nest _ _  = P.refl
  ... | emb _ _   = P.refl

  -- A (heterogeneous) notion of document equivalence.

  infix 4 _≈_

  _≈_ : ∀ {A₁ i₁ g₁} {x₁ : A₁}
          {A₂ i₂ g₂} {x₂ : A₂} →
        DocN i₁ g₁ x₁ → DocN i₂ g₂ x₂ → Set
  d₁ ≈ d₂ = ∀ width → renderN width d₁ ≡ renderN width d₂

  -- Some laws satisfied by the DocN combinators.

  text-++ : ∀ {i₁ i₂} s₁ s₂ →
        text {i = i₁} (s₁ ++ s₂) ≈
        _⊛>_ {c₁ = false} {c₂ = false} (text {i = i₂} s₁) (text s₂)
  text-++ []        []        _ = P.refl
  text-++ []        (t₂ ∷ s₂) _ = P.refl
  text-++ (t₁ ∷ s₁) []        _ = lemma
    where
    lemma : ∀ {s₁} → (s₁ ++ []) ++ [] ≡ s₁ ++ []
    lemma = solve (++-monoid Char)
  text-++ (t₁ ∷ s₁) (t₂ ∷ s₂) _ = lemma (_ ∷ s₁)
    where
    lemma : ∀ s₁ {s₂} → (s₁ ++ s₂) ++ [] ≡ s₁ ++ s₂ ++ []
    lemma _ = solve (++-monoid Char)

  nest-union : ∀ {A i j g} {x : A} {d₁ d₂ : DocN (j + i) g x} →
               nest j (union d₁ d₂) ≈ union (nest j d₁) (nest j d₂)
  nest-union _ = P.refl

  union-◇ : ∀ {A B i x y c₁ c₂}
              {g₁ : ∞Grammar c₁ A} {g₂ : A → ∞Grammar c₂ B}
              {d₁ d₂ : DocN i (♭? g₁) x} {d₃ : DocN i (♭? (g₂ x)) y} →
            _◇_ {g₁ = g₁} {g₂ = g₂} (union d₁ d₂) d₃ ≈
            union (d₁ ◇ d₃) (_◇_ {g₁ = g₁} {g₂ = g₂} d₂ d₃)
  union-◇ _ = P.refl

  -- A law that is /not/ satisfied by the DocN combinators.

  ¬-◇-union :
    ¬ (∀ {A B i x y} c₁ c₂
         {g₁ : ∞Grammar c₁ A} {g₂ : A → ∞Grammar c₂ B}
       (d₁ : DocN i (♭? g₁) x) (d₂ d₃ : DocN i (♭? (g₂ x)) y) →
       _◇_ {g₁ = g₁} {g₂ = g₂} d₁ (union d₂ d₃) ≈
       union (d₁ ◇ d₂) (_◇_ {g₁ = g₁} {g₂ = g₂} d₁ d₃))
  ¬-◇-union hyp with hyp false false d₁ d₂ d₁ 0
    where
    d₁ = imprecise-line 0
    d₂ = imprecise-space

    -- The following four definitions are not part of the proof.

    left : DocN 0 _ _
    left = _◇_ {c₁ = false} {c₂ = false} d₁ (union d₂ d₁)

    right : DocN 0 _ _
    right = union (d₁ ◇ d₂) (_◇_ {c₁ = false} {c₂ = false} d₁ d₁)

    -- Note that left and right are not rendered in the same way.

    left-hand-string : renderN 0 left ≡ String.toList "\n\n"
    left-hand-string = P.refl

    right-hand-string : renderN 0 right ≡ String.toList "\n "
    right-hand-string = P.refl

  ... | ()

-- Uses Wadler's-renderer.render to render a document using the
-- given line width.

render : ∀ {A} {g : Grammar A} {x} → ℕ → Doc g x → String
render w d = String.fromList (Wadler's-renderer.render w d)
