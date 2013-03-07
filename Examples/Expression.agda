------------------------------------------------------------------------
-- Simple expressions
------------------------------------------------------------------------

module Examples.Expression where

open import Coinduction
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Examples.Name
open import Grammar.Infinite
open import Pretty
open import Utilities

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
