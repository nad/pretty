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
open import Data.List.Properties using (module List-solver)
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String as String using (String)
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

str : {p : Char → Bool}
      (s : String)
      {ok : T (all p $ String.toList s)} →
      List (∃ (T ∘ p))
str {p} s {ok} = str′ (String.toList s) {ok}
  where
  str′ : (s : List Char) {ok : T (all p s)} → List (∃ (T ∘ p))
  str′ []            = []
  str′ (t ∷ ts) {ok} =
    let (ok₁ , ok₂) = Eq.to T-∧ ⟨$⟩ ok in
    (t , ok₁) ∷ str′ ts {ok₂}

------------------------------------------------------------------------
-- Bits

module Bit where

  data Bit : Set where
    [0] [1] : Bit

  bit : Grammar Bit
  bit = ♯ ([0] <$ symbol′ "0")
      ∣ ♯ ([1] <$ symbol′ "1")

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

  test : render 80 (name-w-printer (str "aaa")) ≡ "aaa"
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
    ∣ ♯ (List⁺.toList <$> ♯ (name-w sep-by symbol′ ","))

  name-list : Grammar (List Name)
  name-list =
    ♯ (♯ symbol′ "[" ⊛> ♯ name-list-body) <⊛ ♯ symbol′ "]"

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
  names = str "aaa" ∷ str "bbbbb" ∷ str "ccc" ∷
          str "dd" ∷ str "eee" ∷ []

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
           ♯ (♯ (♯ symbol′ "[" ⊛> ♯ trees) <⊛ ♯ symbol′ "]"))

    trees : Grammar (List⁺ Tree)
    trees = ♯ (_∷_ <$> ♯ tree) ⊛ ♯ commas-and-trees

    commas-and-trees : Grammar (List Tree)
    commas-and-trees = ♯ (♯ symbol′ "," ⊛> ♯ tree) ⋆

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
  t = node (str "aaa")
        (node (str "bbbbb")
           (node (str "ccc") [] ∷
            node (str "dd") [] ∷
            []) ∷
         node (str "eee") [] ∷
         node (str "ffff")
           (node (str "gg") [] ∷
            node (str "hhh") [] ∷
            node (str "ii") [] ∷
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
                       ♯ ([] <$ string′ "/")
                     ∣ ♯ (♯ (♯ (♯ string′ ">"
                             ⊛> ♯ w-xmls)
                            <⊛  ♯ symbol′ "</")
                            <⊛  ♯ symbol (List.map proj₁ t))))}) <⊛
             ♯ symbol′ ">")
        ∣ ♯ (♯ (txt <$> ♯ text-g) <⊛ ♯ whitespace⋆)

    start-of-element : Grammar (Name × List Att)
    start-of-element =
      ♯ (♯ (_,_ <$ symbol′ "<") ⊛ ♯ name) ⊛ ♯ w-attrs

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
                           <⊛  ♯ symbol′ "=")
                           <⊛  ♯ string′ "\"")
                            ⊛  ♯ name)
                           <⊛  ♯ symbol′ "\""

  mutual

    xml-printer : Pretty-printer xml
    xml-printer (elt t atts []) =
      ∣-left-doc ((start-of-element-printer (t , atts)
                     ·
                   <$>-doc (∣-left-doc (<$-doc text)))
                    <⊛-doc
                  symbol-doc)
    xml-printer (elt t atts xs) =
      ∣-left-doc ((start-of-element-printer (t , atts)
                     ·
                   <$>-doc (∣-right-doc (text              ⊛>-doc
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
           (final-line 0 4
              (nest 2 (map+-fill-doc 2 attr-printer (a ∷ as)))))

    attr-printer : Pretty-printer attr
    attr-printer (att n v) =
      <$>-doc (name-w-printer n) <⊛-doc
              symbol-doc         <⊛-doc
              text                ⊛-doc
              name-printer v     <⊛-doc
              symbol-doc

    w-xmls-printer : Pretty-printer w-xmls
    w-xmls-printer []       = <$-doc []-doc ⊛>-doc []-doc
    w-xmls-printer (x ∷ xs) =
      group
        (nest 2 line⋆
           ⊛>-doc
         embed ⋆-+-sem
           (final-line 0 5 (nest 2 (fill+ 3 (to-docs x xs)))))
      where
      to-docs : ∀ x xs → Docs xml (x ∷ xs)
      to-docs x []        = [ xml-printer x ]
      to-docs x (x′ ∷ xs) = xml-printer x ∷ to-docs x′ xs

  example : XML
  example = elt (str "p")
                (att (str "color") (str "red") ∷
                 att (str "font") (str "Times") ∷
                 att (str "size") (str "10") ∷ [])
                (txt (str "Here is some") ∷
                 elt (str "em")
                     []
                     (txt (str "emphasized") ∷ []) ∷
                 txt (str "text.") ∷
                 txt (str "Here is a") ∷
                 elt (str "a")
                     (att (str "href") (str "http://www.eg.com/") ∷ [])
                     (txt (str "link") ∷ []) ∷
                 txt (str "elsewhere.") ∷ [])

  test₁ : render 30 (xml-printer example) ≡
          "<p\n  color=\"red\" font=\"Times\"\n  size=\"10\"\n>\n  Here is some\n  <em> emphasized </em> text.\n  Here is a\n  <a\n    href=\"http://www.eg.com/\"\n  > link </a>\n  elsewhere.\n</p>"
  test₁ = refl

  test₂ : render 60 (xml-printer example) ≡
          "<p color=\"red\" font=\"Times\" size=\"10\" >\n  Here is some <em> emphasized </em> text. Here is a\n  <a href=\"http://www.eg.com/\" > link </a> elsewhere.\n</p>"
  test₂ = refl

------------------------------------------------------------------------
-- Simple expressions

-- This example is based on one in Matsuda and Wang's "FliPpr: A
-- Prettier Invertible Printing System".

module Expression₁ where

  data E : Set where
    one : E
    sub : E → E → E

  mutual

    -- Note the use of "tt <$".

    expr : Grammar E
    expr = ♯ atom
         ∣ ♯ (♯ (sub <$> ♯ expr)
                     ⊛ ♯ (♯ (♯ (
                        ♯ (tt <$ whitespace⋆)
                     ⊛> ♯ string′ "-")
                     ⊛> ♯ whitespace⋆)
                     ⊛> ♯ atom))

    atom : Grammar E
    atom = ♯ (one <$ string′ "1")
         ∣ ♯ (♯ (♯ (♯ (♯ string′ "("
                    ⊛> ♯ whitespace⋆)
                    ⊛> ♯ expr)
                    <⊛ ♯ whitespace⋆)
                    <⊛ ♯ string′ ")")

  one-doc : Doc atom one
  one-doc = ∣-left-doc (<$-doc text)

  mutual

    ppr : Pretty-printer expr
    ppr one         = ∣-left-doc one-doc
    ppr (sub e₁ e₂) =
       ∣-right-doc
         (group (<$>-doc (ppr e₁) ⊛-doc
                 nest 2 (line⋆ ⊛>-doc text ⊛>-doc space-doc
                               ⊛>-doc pprP e₂)))

    pprP : Pretty-printer atom
    pprP one = one-doc
    pprP e   =
      ∣-right-doc
        (text ⊛>-doc []-doc ⊛>-doc ppr e <⊛-doc []-doc <⊛-doc text)

  example : E
  example = sub (sub one one) (sub one one)

  test₁ : render 80 (ppr example) ≡ "1 - 1 - (1 - 1)"
  test₁ = refl

  test₂ : render 11 (ppr example) ≡ "1 - 1\n  - (1 - 1)"
  test₂ = refl

  test₃ : render 8 (ppr example) ≡ "1 - 1\n  - (1\n    - 1)"
  test₃ = refl

-- Expression.expr does not accept final whitespace. The grammar below
-- does.

module Expression₂ where

  open Expression₁ using (E; one; sub; example)

  mutual

    expr : Grammar E
    expr = ♯ atom
         ∣ ♯ (♯ (sub <$> ♯ expr) ⊛ ♯ (♯ symbol′ "-" ⊛> ♯ atom))

    atom : Grammar E
    atom = ♯ (one <$ symbol′ "1")
         ∣ ♯ (♯ (♯ symbol′ "(" ⊛> ♯ expr) <⊛ ♯ symbol′ ")")

  one-doc : Doc atom one
  one-doc = ∣-left-doc (<$-doc symbol-doc)

  mutual

    ppr : Pretty-printer expr
    ppr one         = ∣-left-doc one-doc
    ppr (sub e₁ e₂) =
      ∣-right-doc
        (group (<$>-doc (final-line 2 6 (ppr e₁)) ⊛-doc
                nest 2 (symbol-space-doc ⊛>-doc pprP e₂)))

    pprP : Pretty-printer atom
    pprP one = one-doc
    pprP e   = ∣-right-doc (symbol-doc ⊛>-doc ppr e <⊛-doc symbol-doc)

  test₁ : render 80 (ppr example) ≡ "1 - 1 - (1 - 1)"
  test₁ = refl

  test₂ : render 11 (ppr example) ≡ "1 - 1\n  - (1 - 1)"
  test₂ = refl

  test₃ : render 8 (ppr example) ≡ "1 - 1\n  - (1\n    - 1)"
  test₃ = refl

-- A somewhat larger expression example, based on one in Matsuda and
-- Wang's "FliPpr: A Prettier Invertible Printing System".

module Expression₃ where

  open Name

  -- Expressions.

  data E : Set where
    one : E
    sub : E → E → E
    div : E → E → E
    var : Name → E

  -- Precedences.

  data Prec : Set where
    ′5 ′6 ′7 : Prec

  -- One expression grammar for each precedence level.

  expr : Prec → Grammar E
  expr ′5 = ♯ expr ′6
          ∣ ♯ (♯ (sub <$> ♯ expr ′5) ⊛ ♯ (♯ symbol′ "-" ⊛> ♯ expr ′6))
  expr ′6 = ♯ expr ′7
          ∣ ♯ (♯ (div <$> ♯ expr ′6) ⊛ ♯ (♯ symbol′ "/" ⊛> ♯ expr ′7))
  expr ′7 = ♯ (♯ (one <$ symbol′ "1")
          ∣    ♯ (var <$> ♯ name-w))
          ∣ ♯ (♯ (♯ symbol′ "(" ⊛> ♯ expr ′5) <⊛ ♯ symbol′ ")")

  -- Document for one.

  one-doc : Doc (expr ′7) one
  one-doc = ∣-left-doc (∣-left-doc (<$-doc symbol-doc))

  -- Documents for variables.

  var-doc : ∀ x → Doc (expr ′7) (var x)
  var-doc x = ∣-left-doc (∣-right-doc (<$>-doc (name-w-printer x)))

  -- Adds parentheses to a document.

  parens : ∀ {e} → Doc (expr ′5) e → Doc (expr ′7) e
  parens d = ∣-right-doc (symbol-doc ⊛>-doc d <⊛-doc symbol-doc)

  -- Adds parentheses only when necessary (when p₁ < p₂).

  parens-if[_<_] : ∀ p₁ p₂ {e} → Doc (expr p₁) e → Doc (expr p₂) e
  parens-if[ ′5 < ′5 ] = id
  parens-if[ ′5 < ′6 ] = ∣-left-doc ∘ parens
  parens-if[ ′5 < ′7 ] = parens
  parens-if[ ′6 < ′5 ] = ∣-left-doc
  parens-if[ ′6 < ′6 ] = id
  parens-if[ ′6 < ′7 ] = parens ∘ ∣-left-doc
  parens-if[ ′7 < ′5 ] = ∣-left-doc ∘ ∣-left-doc
  parens-if[ ′7 < ′6 ] = ∣-left-doc
  parens-if[ ′7 < ′7 ] = id

  mutual

    -- Pretty-printers.

    expr-printer : ∀ p → Pretty-printer (expr p)
    expr-printer p (sub e₁ e₂) = parens-if[ ′5 < p ] (sub-printer e₁ e₂)
    expr-printer p (div e₁ e₂) = parens-if[ ′6 < p ] (div-printer e₁ e₂)
    expr-printer p one         = parens-if[ ′7 < p ] one-doc
    expr-printer p (var x)     = parens-if[ ′7 < p ] (var-doc x)

    sub-printer : ∀ e₁ e₂ → Doc (expr ′5) (sub e₁ e₂)
    sub-printer e₁ e₂ =
      ∣-right-doc
        (group (<$>-doc (final-line 2 10 (expr-printer ′5 e₁)) ⊛-doc
                nest 2 (symbol-space-doc ⊛>-doc expr-printer ′6 e₂)))

    div-printer : ∀ e₁ e₂ → Doc (expr ′6) (div e₁ e₂)
    div-printer e₁ e₂ =
      ∣-right-doc
        (group (<$>-doc (final-line 2 10 (expr-printer ′6 e₁)) ⊛-doc
                nest 2 (symbol-space-doc ⊛>-doc expr-printer ′7 e₂)))

  -- Unit tests.

  example : E
  example = sub (div (var (str "x")) one) (sub one (var (str "y")))

  test₁ : render 80 (expr-printer ′5 example) ≡ "x / 1 - (1 - y)"
  test₁ = refl

  test₂ : render 11 (expr-printer ′5 example) ≡ "x / 1\n  - (1 - y)"
  test₂ = refl

  test₃ : render 8 (expr-printer ′5 example) ≡ "x / 1\n  - (1\n    - y)"
  test₃ = refl

  test₄ : render 11 (expr-printer ′6 example) ≡ "(x / 1\n  - (1\n    - y))"
  test₄ = refl

  test₅ : render 12 (expr-printer ′6 example) ≡ "(x / 1\n  - (1 - y))"
  test₅ = refl
