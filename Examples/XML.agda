------------------------------------------------------------------------
-- Simplified XML documents
------------------------------------------------------------------------

-- This example is based on (but not identical to) one in Wadler's "A
-- prettier printer".

module Examples.XML where

open import Coinduction
open import Data.Bool
open import Data.Char
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty using (_∷_)
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Examples.Name
open import Grammar.Infinite
open import Pretty
open import Utilities

-- Text.

is-space : Char → Bool
is-space t = (t ≟C ' ') ∨ (t ≟C '\n')

is-text-char : Char → Bool
is-text-char t = is-name-char t ∨ is-space t

Text : Set
Text = List (∃ λ (t : Char) → T (is-text-char t))

text-g : Grammar Text
text-g = sat _ ⋆

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
  xml = (start-of-element >>= λ { (t , atts) →
         elt t atts <$> (
             [] <$ string′ "/"
           ∣     string′ ">"
              ⊛> w-xmls
             <⊛  symbol′ "</"
             <⊛  symbol (List.map proj₁ t))}) <⊛
        symbol′ ">"
      ∣ txt <$> text-g <⊛ whitespace ⋆

  start-of-element : Grammar (Name × List Att)
  start-of-element = _,_ <$ symbol′ "<" ⊛ name ⊛ w-attrs

  -- The following definition uses "tt <$" in order to make
  -- pretty-printing easier.

  w-xmls : Grammar (List XML)
  w-xmls = (tt <$ whitespace ⋆) ⊛> xmls

  xmls : Grammar (List XML)
  xmls = ♯ xml ⋆

  tag : Grammar Name
  tag = name-w

  -- The following definition uses "tt <$" in order to make
  -- pretty-printing easier.

  w-attrs : Grammar (List Att)
  w-attrs = (tt <$ whitespace ⋆) ⊛> attrs

  attrs : Grammar (List Att)
  attrs = attr ⋆

  attr : Grammar Att
  attr = att <$> name-w
             <⊛  symbol′ "="
             <⊛  string′ "\""
              ⊛  name
             <⊛  symbol′ "\""

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
