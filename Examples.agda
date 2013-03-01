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
open import Data.List.Properties using (module List-solver)
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

open import Grammar
open import Pretty
open import Tests

------------------------------------------------------------------------
-- Some boring lemmas

private

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

  ++-lemma₃ : {A : Set} (a b c d : List A) →
              ((a ++ b) ++ c) ++ d ≡ a ++ b ++ c ++ d
  ++-lemma₃ = solve 4 (λ a b c d → ((a ⊕ b) ⊕ c) ⊕ d ⊜ a ⊕ b ⊕ c ⊕ d)
                      refl
    where open List-solver

------------------------------------------------------------------------
-- Utility functions

-- Uses wadler's-renderer to render a document using the given line
-- width.

render : ∀ {A} {g : G A} {x} → ℕ → Doc g x → String
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
-- Examples

module Bit where

  -- Bits.

  data Bit : Set where
    [0] [1] : Bit

  bit : G Bit
  bit = ♯ ([0] <$ symbol (str "0"))
      ∣ ♯ ([1] <$ symbol (str "1"))

  -- The first case below is defined using primitive combinators, the
  -- second one using derived ones.

  bit-printer : Pretty-printer bit
  bit-printer [0] = embed ∣-left ((text (str "0") ·
                                   (embed ∣-left nil · nil)) ·
                                  nil)
  bit-printer [1] = ∣-right-doc (<$-doc symbol-doc)

  test₁ : render 4 (bit-printer [0]) ≡ "0"
  test₁ = refl

  test₂ : render 0 (bit-printer [1]) ≡ "1"
  test₂ = refl

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

  name-char : G Name-char
  name-char = sat _

  name-char-printer : Pretty-printer name-char
  name-char-printer _ = sat-doc

  -- Note that if we had defined Name-char = Char, then it
  -- wouldn't have been possible to define name-char-printer.

  -- Names. Note that names are allowed to be empty.

  Name : Set
  Name = List Name-char

  name : G Name
  name = name-char ⋆

  name-printer : Pretty-printer name
  name-printer = map-doc name-char-printer

  -- Names possibly followed by whitespace.

  name-w : G Name
  name-w = ♯ name                 >>= λ n →
           ♯ (n <$ whitespace ⋆)

  name-w-printer : Pretty-printer name-w
  name-w-printer n = name-printer n · []-doc · nil

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

module Name-list where

  open Name

  -- Lists of names. This example is based on one in Swierstra and
  -- Chitil's "Linear, bounded, functional pretty-printing".

  comma-and-name : G Name
  comma-and-name = ♯ symbol (str ",")  >>= λ _ →
                   ♯ name-w

  name-list-body : G (List Name)
  name-list-body = ♯ return []
                 ∣ ♯ (♯ name-w              >>= λ n  → ♯ (
                      ♯ (comma-and-name ⋆)  >>= λ ns →
                      ♯ return (n ∷ ns)     ))

  name-list : G (List Name)
  name-list = ♯ symbol (str "[")  >>= λ _  → ♯ (
              ♯ name-list-body    >>= λ ns → ♯ (
              ♯ symbol (str "]")  >>= λ _  →
              ♯ return ns         ))

  comma-and-name-printer : Pretty-printer comma-and-name
  comma-and-name-printer n = group symbol-line-doc · name-w-printer n

  name-list-printer : Pretty-printer name-list
  name-list-printer ns = symbol-doc · body ns · symbol-doc · nil
    where
    body : Pretty-printer name-list-body
    body []       = ∣-left-doc nil
    body (n ∷ ns) = ∣-right-doc
      (name-w-printer n · map-doc comma-and-name-printer ns · nil)

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
    tree = ♯ name-w              >>= λ n  → ♯ (
           ♯ brackets            >>= λ ts →
           ♯ return (node n ts)  )

    brackets : G (List Tree)
    brackets = ♯ return []
             ∣ ♯ (♯ symbol (str "[")  >>= λ _  → ♯ (
                  ♯ trees             >>= λ ts → ♯ (
                  ♯ symbol (str "]")  >>= λ _  →
                  ♯ return ts         )))

    trees : G (List Tree)
    trees = ♯ tree              >>= λ t  → ♯ (
            ♯ commas-and-trees  >>= λ ts →
            ♯ return (t ∷ ts)   )

    commas-and-trees : G (List Tree)
    commas-and-trees = ♯ return []
                     ∣ ♯ (♯ symbol (str ",") >>= λ _ →
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
        (name-w-printer s · nest (length s) (brackets-printer ts) · nil)

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

    name-w-lemma : ∀ {n x s₁ s₂} →
                   n ∈ name-w ∙ s₁ → x ∈ whitespace + ∙ s₂ →
                   n ∈ name-w ∙ s₁ ++ s₂
    name-w-lemma (_>>=_ {s₁ = s} n∈ (_>>=_ {s₁ = s′} w⋆ return)) w+ =
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
           (name-w-lemma name w+ >>= (∣-left return >>= return))
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
        name-w-printer s · brackets-printer ts · nil

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

module XML where

  open Name

  -- Simplified XML documents. This example is based on (but not
  -- identical to) one in Wadler's "A prettier printer".

  -- Text.

  is-space : Char → Bool
  is-space t = (t ≟C ' ') ∨ (t ≟C '\n')

  is-text-char : Char → Bool
  is-text-char t = is-name-char t ∨ is-space t

  Text : Set
  Text = List (∃ λ (t : Char) → T (is-text-char t))

  text-g : G Text
  text-g = sat _ ⋆

  text-printer : Pretty-printer text-g
  text-printer = map-doc (λ _ → sat-doc)

  mutual

    data XML : Set where
      elt : Name → List Att → List XML → XML
      txt : Text → XML

    data Att : Set where
      att : Name → Name → Att

  -- The following grammar is ambiguous: a sequence of txt elements
  -- can be parsed in several different ways.

  mutual

    xml : G XML
    xml = ♯ (♯ start-of-element                  >>= λ { (t , atts) → ♯
               ( ♯ (♯ symbol (str "/>")          >>= λ _            →
                    ♯ return (elt t atts [])     )
               ∣ ♯ (♯ string (str ">")           >>= λ _            → ♯ (
                    ♯ w-xmls                     >>= λ xs           → ♯ (
                    ♯ symbol (str "</")          >>= λ _            → ♯ (
                    ♯ symbol (List.map proj₁ t)  >>= λ _            → ♯ (
                    ♯ symbol (str ">")           >>= λ _            →
                    ♯ return (elt t atts xs)     )))))
               )})
        ∣ ♯ (♯ text-g                            >>= λ t            →
             ♯ return (txt t)                    )

    start-of-element : G (Name × List Att)
    start-of-element =
      ♯ symbol (str "<")   >>= λ _    → ♯ (
      ♯ name               >>= λ t    → ♯ (
      ♯ w-attrs            >>= λ atts →
      ♯ return (t , atts)  ))

    w-xmls : G (List XML)
    w-xmls = ♯ (whitespace ⋆)  >>= λ _ →
             ♯ xmls

    xmls : G (List XML)
    xmls = ♯ return []
         ∣ ♯ (♯ xml              >>= λ x  → ♯ (
              ♯ xmls             >>= λ xs →
              ♯ return (x ∷ xs)  ))

    tag : G Name
    tag = name-w

    w-attrs : G (List Att)
    w-attrs = ♯ (whitespace ⋆)  >>= λ _ →
              ♯ attrs

    attrs : G (List Att)
    attrs = ♯ return []
          ∣ ♯ (♯ attr             >>= λ a  → ♯ (
               ♯ attrs            >>= λ as →
               ♯ return (a ∷ as)  ))

    attr : G Att
    attr = ♯ name-w             >>= λ n → ♯ (
           ♯ symbol (str "=")   >>= λ _ → ♯ (
           ♯ string (str "\"")  >>= λ _ → ♯ (
           ♯ name               >>= λ v → ♯ (
           ♯ symbol (str "\"")  >>= λ _ →
           ♯ return (att n v)   ))))

  mutual

    xml-printer : Pretty-printer xml
    xml-printer (elt t atts []) =
      ∣-left-doc (start-of-element-printer (t , atts) ·
                  ∣-left-doc (symbol-doc · nil))
    xml-printer (elt t atts xs) =
      ∣-left-doc (start-of-element-printer (t , atts) ·
                  ∣-right-doc (text _ ·
                               xmls-printer xs ·
                               symbol-doc ·
                               symbol-doc ·
                               symbol-doc ·
                               nil))
    xml-printer (txt t) =
      -- Wadler pretty-prints text items in a different way. (The
      -- grammar that I use does not allow me to remove/modify
      -- whitespace like Wadler does.)
      ∣-right-doc (text-printer t · nil)

    start-of-element-printer : Pretty-printer start-of-element
    start-of-element-printer (t , atts) =
      symbol-doc · name-printer t · attrs-printer atts · nil

    attrs-printer : Pretty-printer w-attrs
    attrs-printer []       = []-doc · ∣-left-doc nil
    attrs-printer (a ∷ as) =
      group (embed lemma
        (nest 2 line · nest 2 (fill (to-docs a as)) · line))
      where
      to-docs : ∀ a as → Docs attr (a ∷ as)
      to-docs a []        = [ attr-printer a ]
      to-docs a (a′ ∷ as) = attr-printer a ∷ to-docs a′ as

      -- TODO: Do something about this boring lemma.

      postulate
        lemma : ∀ {s} →
                a ∷ as ∈ (tt <$ whitespace +         >>
                          (attr sep-by whitespace +  ≫= λ ys →
                           ys <$ whitespace +)) ∙ s →
                a ∷ as ∈ w-attrs ∙ s
        -- lemma (w+₁ >>= return >>= (as >>= (w+₂ >>= return))) = {!!}

    attr-printer : Pretty-printer attr
    attr-printer (att n v) =
      name-w-printer n ·
      symbol-doc ·
      text _ ·
      name-printer v ·
      symbol-doc ·
      nil

    xmls-printer : Pretty-printer w-xmls
    xmls-printer []       = []-doc · ∣-left-doc nil
    xmls-printer (x ∷ xs) =
      group (embed lemma
        (nest 2 line · nest 2 (fill (to-docs x xs)) · line))
      where
      to-docs : ∀ x xs → Docs xml (x ∷ xs)
      to-docs x []        = [ xml-printer x ]
      to-docs x (x′ ∷ xs) = xml-printer x ∷ to-docs x′ xs

      -- TODO: Do something about this boring lemma.

      postulate
        lemma : ∀ {s} →
                x ∷ xs ∈ (tt <$ whitespace +        >>
                          (xml sep-by whitespace +  ≫= λ ys →
                           ys <$ whitespace +)) ∙ s →
                x ∷ xs ∈ w-xmls ∙ s
        -- lemma (w+₁ >>= return >>= (xs >>= (w+₂ >>= return))) = {!!}

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
