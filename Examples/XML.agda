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
open import Data.List.NonEmpty as List⁺ using (_∷_)
open import Data.Product
import Data.String as String
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Examples.Identifier
open import Grammar.Infinite as Grammar using (Grammar)
open import Pretty using (Pretty-printer)
open import Renderer
open import Utilities

-- Text.

is-text-char : Char → Bool
is-text-char t =
  ('A' ≤?C t) ∧ (t ≤?C 'Z')
    ∨
  ('a' ≤?C t) ∧ (t ≤?C 'z')
    ∨
  ('0' ≤?C t) ∧ (t ≤?C '9')
    ∨
  List.any (_==_ t) (String.toList ":./ \n")

Text : Set
Text = List (∃ λ (t : Char) → T (is-text-char t))

text-g : Grammar Text
text-g = sat _ ⋆
  where open Grammar

text-printer : Pretty-printer text-g
text-printer = map⋆ (sat is-text-char)
  where open Pretty

mutual

  data XML : Set where
    elt : Identifier → List Att → List XML → XML
    txt : Text → XML

  data Att : Set where
    att : Identifier → Text → Att

module _ where

  open Grammar

  mutual

    -- The following grammar is ambiguous: a sequence of txt elements can
    -- be parsed in several different ways.

    xml : Grammar XML
    xml = (start-of-element >>= λ { (t , atts) →
           elt t atts <$> (
               [] <$ string′ "/"
             ∣     string′ ">"
                ⊛> xmls
               <⊛  symbol′ "</"
               <⊛  symbol (List.map proj₁ (List⁺.toList t)))}) <⊛
          symbol′ ">"
        ∣ txt <$> text-g <⊛ whitespace ⋆

    start-of-element : Grammar (Identifier × List Att)
    start-of-element = _,_ <$ symbol′ "<" ⊛ identifier ⊛ attrs

    xmls : Grammar (List XML)
    xmls = whitespace ⋆ ⊛> ♯ xml ⋆

    attrs : Grammar (List Att)
    attrs = [] <$ whitespace ⋆
          ∣ List⁺.toList <$> (whitespace + ⊛> attr +)

    attr : Grammar Att
    attr = att <$> identifier
               <⊛  whitespace ⋆
               <⊛  symbol′ "="
               <⊛  string′ "\""
                ⊛  text-g
               <⊛  symbol′ "\""

open Pretty

mutual

  xml-printer : Pretty-printer xml
  xml-printer (elt t atts []) =
    left ((start-of-element-printer (t , atts) ◇
           <$> left (<$ text))
          <⊛ symbol)
  xml-printer (elt t atts xs) =
    left ((start-of-element-printer (t , atts) ◇
           <$> right (text ⊛> xmls-printer xs <⊛ symbol <⊛ symbol))
          <⊛ symbol)
  xml-printer (txt t) =
    -- Wadler pretty-prints text items in a different way. (The
    -- grammar that I use does not allow me to modify the amount of
    -- whitespace in the same way as Wadler.)
    right (<$> text-printer t <⊛ nil-⋆)

  start-of-element-printer : Pretty-printer start-of-element
  start-of-element-printer (t , atts) =
    <$ symbol ⊛ identifier-printer t ⊛ attrs-printer atts

  attrs-printer : Pretty-printer attrs
  attrs-printer []       = left (<$ nil-⋆)
  attrs-printer (a ∷ as) =
    right (<$> group (nest 2 line
                        tt-⊛>
                      final-line 4
                        (nest 2 (map+-fill 2 attr-printer (a ∷ as))) 0))

  attr-printer : Pretty-printer attr
  attr-printer (att n v) =
    <$> identifier-printer n
    <⊛  nil-⋆
    <⊛  symbol
    <⊛  text
     ⊛  text-printer v
    <⊛  symbol

  -- The following definition uses "fill+ 3 (to-docs x xs)" (along
  -- with the auxiliary definition of to-docs) rather than
  -- "map+-fill 3 xml-printer (x ∷ xs)" because the latter piece of
  -- code makes the termination checker complain.

  xmls-printer : Pretty-printer xmls
  xmls-printer []       = nil-⋆ ⊛> nil-⋆
  xmls-printer (x ∷ xs) =
    group (nest 2 line⋆
             tt-⊛>
           final-line-+⋆ 5 (nest 2 (fill+ 3 (to-docs x xs))) 0)
    where
    to-docs : ∀ x xs → Docs xml (x ∷ xs)
    to-docs x []        = [ xml-printer x ]
    to-docs x (x′ ∷ xs) = xml-printer x ∷ to-docs x′ xs

example : XML
example = elt (str⁺ "p")
              (att (str⁺ "color") (str "red") ∷
               att (str⁺ "font") (str "Times") ∷
               att (str⁺ "size") (str "10") ∷ [])
              (txt (str "Here is some") ∷
               elt (str⁺ "em")
                   []
                   (txt (str "emphasized") ∷ []) ∷
               txt (str "text.") ∷
               txt (str "Here is a") ∷
               elt (str⁺ "a")
                   (att (str⁺ "href") (str "http://www.eg.com/") ∷ [])
                   (txt (str "link") ∷ []) ∷
               txt (str "elsewhere.") ∷ [])

test₁ : render 30 (xml-printer example) ≡
        "<p\n  color=\"red\" font=\"Times\"\n  size=\"10\"\n>\n  Here is some\n  <em> emphasized </em> text.\n  Here is a\n  <a\n    href=\"http://www.eg.com/\"\n  > link </a>\n  elsewhere.\n</p>"
test₁ = refl

test₂ : render 60 (xml-printer example) ≡
        "<p color=\"red\" font=\"Times\" size=\"10\" >\n  Here is some <em> emphasized </em> text. Here is a\n  <a href=\"http://www.eg.com/\" > link </a> elsewhere.\n</p>"
test₂ = refl
