------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

module Examples where

open import Algebra
open import Coinduction
open import Data.Bool
open import Data.Bool.Properties using (T-∧)
open import Data.Char
open import Data.List as List hiding ([_])
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Nat
open import Data.Product
open import Data.String as String
  using (String) renaming (toList to str)
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using () renaming (module Equivalence to Eq)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

private module LM {A : Set} = Monoid (List.monoid A)

open import Grammar.Infinite
open import Pretty
open import Tests

------------------------------------------------------------------------
-- Utility functions

-- Uses wadler's-renderer to render a document using the given line
-- width.

render : ∀ {A} {g : Grammar A} {x} → ℕ → Doc g x → String
render w d = String.fromList (Renderer.render (wadler's-renderer w) d)

-- Converts strings satisfying a given predicate to annotated lists.

from-string :
  {p : Char → Bool}
  (s : String)
  {ok : T (all p $ str s)} →
  List (∃ (T ∘ p))
from-string {p} s {ok} = from-string′ (str s) {ok}
  where
  from-string′ : (s : List Char) {ok : T (all p s)} → List (∃ (T ∘ p))
  from-string′ []            = []
  from-string′ (t ∷ ts) {ok} =
    let (ok₁ , ok₂) = Eq.to T-∧ ⟨$⟩ ok in
    (t , ok₁) ∷ from-string′ ts {ok₂}

------------------------------------------------------------------------
-- Bits

module Bit where

  data Bit : Set where
    [0] [1] : Bit

  bit : Grammar Bit
  bit = ♯ ([0] <$ symbol (str "0"))
      ∣ ♯ ([1] <$ symbol (str "1"))

  bit-printer : Pretty-printer bit
  bit-printer [0] = ∣-left-doc  (<$-doc symbol-doc)
  bit-printer [1] = ∣-right-doc (<$-doc symbol-doc)

  test₁ : render 4 (bit-printer [0]) ≡ "0"
  test₁ = refl

  test₂ : render 0 (bit-printer [1]) ≡ "1"
  test₂ = refl

------------------------------------------------------------------------
-- "Names"

module Name where

  -- "Name characters".

  is-name-char : Char → Bool
  is-name-char t =
    ('A' ≤?C t) ∧ (t ≤?C 'Z')
      ∨
    ('a' ≤?C t) ∧ (t ≤?C 'z')
      ∨
    ('0' ≤?C t) ∧ (t ≤?C '9')
      ∨
    (t ≟C ':')
      ∨
    (t ≟C '.')
      ∨
    (t ≟C '/')

  Name-char : Set
  Name-char = ∃ λ (t : Char) → T (is-name-char t)

  name-char : Grammar Name-char
  name-char = sat _

  name-char-printer : Pretty-printer name-char
  name-char-printer _ = sat-doc

  -- Note that if we had defined Name-char = Char, then it
  -- wouldn't have been possible to define name-char-printer.

  -- Names. Note that names are allowed to be empty.

  Name : Set
  Name = List Name-char

  name : Grammar Name
  name = ♯ name-char ⋆

  name-printer : Pretty-printer name
  name-printer = map⋆-doc name-char-printer

  -- Names possibly followed by whitespace.

  name-w : Grammar Name
  name-w = ♯ name <⊛ ♯ (♯ whitespace ⋆)

  name-w-printer : Pretty-printer name-w
  name-w-printer n = name-printer n <⊛-doc []-doc

  as : Name
  as = from-string "aaa"

  bs : Name
  bs = from-string "bbbbb"

  cs : Name
  cs = from-string "ccc"

  ds : Name
  ds = from-string "dd"

  es : Name
  es = from-string "eee"

  fs : Name
  fs = from-string "ffff"

  gs : Name
  gs = from-string "gg"

  hs : Name
  hs = from-string "hhh"

  is : Name
  is = from-string "ii"

  test : render 80 (name-w-printer as) ≡ "aaa"
  test = refl

------------------------------------------------------------------------
-- Lists of names

-- This example is based on one in Swierstra and Chitil's "Linear,
-- bounded, functional pretty-printing".

module Name-list where

  open Name

  name-list-body : Grammar (List Name)
  name-list-body =
      ♯ return []
    ∣ ♯ (List⁺.toList <$> ♯ (name-w sep-by symbol (str ",")))

  name-list : Grammar (List Name)
  name-list =
    ♯ (♯ symbol (str "[") ⊛> ♯ name-list-body) <⊛ ♯ symbol (str "]")

  name-list-printer : Pretty-printer name-list
  name-list-printer ns = symbol-doc ⊛>-doc body ns <⊛-doc symbol-doc
    where
    body : Pretty-printer name-list-body
    body []       = ∣-left-doc nil
    body (n ∷ ns) =
      ∣-right-doc
        (<$>-doc
           (<$>-doc (name-w-printer n)
              ⊛-doc
            map⋆-doc (λ n → group symbol-line-doc
                              ⊛>-doc
                            name-w-printer n)
                     ns))

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

------------------------------------------------------------------------
-- Trees

-- This example is based on one in Wadler's "A prettier printer".

module Tree where

  open Name

  data Tree : Set where
    node : Name → List Tree → Tree

  mutual

    tree : Grammar Tree
    tree = ♯ (node <$> ♯ name-w) ⊛ ♯ brackets

    brackets : Grammar (List Tree)
    brackets =
        ♯ return []
      ∣ ♯ (List⁺.toList <$>
           ♯ (♯ (♯ symbol (str "[") ⊛> ♯ trees) <⊛ ♯ symbol (str "]")))

    trees : Grammar (List⁺ Tree)
    trees = ♯ (_∷_ <$> ♯ tree) ⊛ ♯ commas-and-trees

    commas-and-trees : Grammar (List Tree)
    commas-and-trees = ♯ (♯ symbol (str ",") ⊛> ♯ tree) ⋆

  -- Wadler presents two pretty-printers for trees in his final code
  -- listing (§11.7). I've included corresponding, but not quite
  -- identical, implementations here.
  --
  -- (One of Wadler's implementations is buggy: recursive calls to
  -- showTree/showTrees should most likely have referred to
  -- showTree'/showTrees'. The code below is intended to match a
  -- corrected version of Wadler's.)

  module Printer₁ where

    mutual

      tree-printer : Pretty-printer tree
      tree-printer (node s ts) =
        group
          (<$>-doc (name-w-printer s)
             ⊛-doc
           nest (length s) (brackets-printer ts))

      brackets-printer : Pretty-printer brackets
      brackets-printer []       = ∣-left-doc nil
      brackets-printer (t ∷ ts) =
        ∣-right-doc
          (<$>-doc
             (symbol-doc
                ⊛>-doc
              nest 1 (trees-printer (t ∷ ts))
                <⊛-doc
              symbol-doc))

      trees-printer : Pretty-printer trees
      trees-printer (t ∷ ts) =
        <$>-doc (tree-printer t) ⊛-doc commas-and-trees-printer ts

      commas-and-trees-printer : Pretty-printer commas-and-trees
      commas-and-trees-printer []       = []-doc
      commas-and-trees-printer (t ∷ ts) =
        (symbol-line-doc ⊛>-doc tree-printer t)
          ⋆-∷-doc
        commas-and-trees-printer ts

  module Printer₂ where

    mutual

      tree-printer : Pretty-printer tree
      tree-printer (node s ts) =
        <$>-doc (name-w-printer s) ⊛-doc brackets-printer ts

      -- Note that this printer is not defined in exactly the same way
      -- as Wadler's: Wadler used "nest 2" once, here it is used
      -- twice. Why? His one nest spanned over two parts of the
      -- grammar (the opening bracket and the trees, respectively),
      -- but not all of the second part (not the "line" combinator).

      brackets-printer : Pretty-printer brackets
      brackets-printer []       = ∣-left-doc nil
      brackets-printer (t ∷ ts) =
        ∣-right-doc
          (<$>-doc
             (bracket 7 refl refl refl (trees-printer (t ∷ ts))))

      trees-printer : Pretty-printer trees
      trees-printer (t ∷ ts) =
        <$>-doc (tree-printer t) ⊛-doc commas-and-trees-printer ts

      commas-and-trees-printer : Pretty-printer commas-and-trees
      commas-and-trees-printer []       = []-doc
      commas-and-trees-printer (t ∷ ts) =
        (symbol-line-doc ⊛>-doc tree-printer t)
          ⋆-∷-doc
        commas-and-trees-printer ts

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

------------------------------------------------------------------------
-- Simplified XML documents

-- This example is based on (but not identical to) one in Wadler's "A
-- prettier printer".

module XML where

  open Name

  -- Text.

  is-space : Char → Bool
  is-space t = (t ≟C ' ') ∨ (t ≟C '\n')

  is-text-char : Char → Bool
  is-text-char t = is-name-char t ∨ is-space t

  Text : Set
  Text = List (∃ λ (t : Char) → T (is-text-char t))

  text-g : Grammar Text
  text-g = ♯ sat _ ⋆

  text-printer : Pretty-printer text-g
  text-printer = map⋆-doc (λ _ → sat-doc)

  mutual

    data XML : Set where
      elt : Name → List Att → List XML → XML
      txt : Text → XML

    data Att : Set where
      att : Name → Name → Att

  -- The following grammar is ambiguous: a sequence of txt elements
  -- can be parsed in several different ways.

  mutual

    -- Below I use string followed by "w-xmls" (whitespace, then
    -- xmls)—rather than symbol followed by xmls—in order to make
    -- pretty-printing easier.

    xml : Grammar XML
    xml = ♯ (♯ (♯ start-of-element >>= λ { (t , atts) →
                ♯ (elt t atts <$> ♯ (
                       ♯ ([] <$ string (str "/"))
                     ∣ ♯ (♯ (♯ (♯ string (str ">")
                             ⊛> ♯ w-xmls)
                            <⊛  ♯ symbol (str "</"))
                            <⊛  ♯ symbol (List.map proj₁ t))))}) <⊛
             ♯ symbol (str ">"))
        ∣ ♯ (♯ (txt <$> ♯ text-g) <⊛ ♯ whitespace⋆)

    start-of-element : Grammar (Name × List Att)
    start-of-element =
      ♯ (♯ (_,_ <$ symbol (str "<")) ⊛ ♯ name) ⊛ ♯ w-attrs

    -- The following definition uses "tt <$" in order to make
    -- pretty-printing easier.

    w-xmls : Grammar (List XML)
    w-xmls = ♯ (tt <$ whitespace⋆) ⊛> ♯ xmls

    xmls : Grammar (List XML)
    xmls = ♯ xml ⋆

    tag : Grammar Name
    tag = name-w

    -- The following definition uses "tt <$" in order to make
    -- pretty-printing easier.

    w-attrs : Grammar (List Att)
    w-attrs = ♯ (tt <$ whitespace⋆) ⊛> ♯ attrs

    attrs : Grammar (List Att)
    attrs = ♯ attr ⋆

    attr : Grammar Att
    attr = ♯ (♯ (♯ (♯ (att <$> ♯ name-w)
                           <⊛  ♯ symbol (str "="))
                           <⊛  ♯ string (str "\""))
                            ⊛  ♯ name)
                           <⊛  ♯ symbol (str "\"")

  mutual

    xml-printer : Pretty-printer xml
    xml-printer (elt t atts []) =
      ∣-left-doc ((start-of-element-printer (t , atts)
                     ·
                   <$>-doc (∣-left-doc (<$-doc (text _))))
                    <⊛-doc
                  symbol-doc)
    xml-printer (elt t atts xs) =
      ∣-left-doc ((start-of-element-printer (t , atts)
                     ·
                   <$>-doc (∣-right-doc (text _            ⊛>-doc
                                         w-xmls-printer xs <⊛-doc
                                         symbol-doc        <⊛-doc
                                         symbol-doc        )))
                    <⊛-doc
                  symbol-doc)
    xml-printer (txt t) =
      -- Wadler pretty-prints text items in a different way. (The
      -- grammar that I use does not allow me to remove/modify
      -- whitespace like Wadler does.)
      ∣-right-doc (<$>-doc (text-printer t) <⊛-doc []-doc)

    start-of-element-printer : Pretty-printer start-of-element
    start-of-element-printer (t , atts) =
      <$-doc symbol-doc ⊛-doc name-printer t ⊛-doc w-attrs-printer atts

    w-attrs-printer : Pretty-printer w-attrs
    w-attrs-printer []       = <$-doc []-doc ⊛>-doc []-doc
    w-attrs-printer (a ∷ as) =
      group
        (nest 2 line⋆
           ⊛>-doc
         embed ⋆-+-sem
           (final-line 4
              (nest 2 (map+-fill-doc 2 attr-printer (a ∷ as)))))

    attr-printer : Pretty-printer attr
    attr-printer (att n v) =
      <$>-doc (name-w-printer n) <⊛-doc
              symbol-doc         <⊛-doc
              text _              ⊛-doc
              name-printer v     <⊛-doc
              symbol-doc

    w-xmls-printer : Pretty-printer w-xmls
    w-xmls-printer []       = <$-doc []-doc ⊛>-doc []-doc
    w-xmls-printer (x ∷ xs) =
      group
        (nest 2 line⋆
           ⊛>-doc
         embed ⋆-+-sem
           (final-line 5 (nest 2 (fill+ 3 (to-docs x xs)))))
      where
      to-docs : ∀ x xs → Docs xml (x ∷ xs)
      to-docs x []        = [ xml-printer x ]
      to-docs x (x′ ∷ xs) = xml-printer x ∷ to-docs x′ xs

  example : XML
  example = elt (from-string "p")
                (att (from-string "color") (from-string "red") ∷
                 att (from-string "font") (from-string "Times") ∷
                 att (from-string "size") (from-string "10") ∷ [])
                (txt (from-string "Here is some") ∷
                 elt (from-string "em")
                     []
                     (txt (from-string "emphasized") ∷ []) ∷
                 txt (from-string "text.") ∷
                 txt (from-string "Here is a") ∷
                 elt (from-string "a")
                     (att (from-string "href")
                          (from-string "http://www.eg.com/") ∷ [])
                     (txt (from-string "link") ∷ []) ∷
                 txt (from-string "elsewhere.") ∷ [])

  test₁ : render 30 (xml-printer example) ≡
          "<p\n  color=\"red\" font=\"Times\"\n  size=\"10\"\n>\n  Here is some\n  <em> emphasized </em> text.\n  Here is a\n  <a\n    href=\"http://www.eg.com/\"\n  > link </a>\n  elsewhere.\n</p>"
  test₁ = refl

  test₂ : render 60 (xml-printer example) ≡
          "<p color=\"red\" font=\"Times\" size=\"10\" >\n  Here is some <em> emphasized </em> text. Here is a\n  <a href=\"http://www.eg.com/\" > link </a> elsewhere.\n</p>"
  test₂ = refl
