------------------------------------------------------------------------
-- Simple expressions
------------------------------------------------------------------------

-- Several examples based on Matsuda and Wang's "FliPpr: A Prettier
-- Invertible Printing System".

module Examples.Expression where

open import Coinduction
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Examples.Name
import Grammar.Infinite as Grammar
import Pretty
open import Renderer
open import Utilities

-- Very simple expressions.

module Expression₁ where

  data Expr : Set where
    one : Expr
    sub : Expr → Expr → Expr

  module _ where

    open Grammar

    mutual

      expr : Grammar Expr
      expr = atom
           ∣ sub <$> ♯ expr
                  <⊛ whitespace ⋆
                  <⊛ string′ "-"
                  <⊛ whitespace ⋆
                  ⊛  atom

      atom : Grammar Expr
      atom = one <$ string′ "1"
           ∣    string′ "("
             ⊛> whitespace ⋆
             ⊛> ♯ expr
             <⊛ whitespace ⋆
             <⊛ string′ ")"

  open Pretty

  one-doc : Doc atom one
  one-doc = left (<$ text)

  mutual

    ppr : Pretty-printer expr
    ppr one         = left one-doc
    ppr (sub e₁ e₂) =
      right (group (<$> ppr e₁ <⊛-tt
                    nest 2 line⋆ <⊛ text <⊛ space ⊛ nest 2 (pprP e₂)))

    pprP : Pretty-printer atom
    pprP one = one-doc
    pprP e   = right (text ⊛> ⋆-[] ⊛> ppr e <⊛ ⋆-[] <⊛ text)

  example : Expr
  example = sub (sub one one) (sub one one)

  test₁ : render 80 (ppr example) ≡ "1 - 1 - (1 - 1)"
  test₁ = refl

  test₂ : render 11 (ppr example) ≡ "1 - 1\n  - (1 - 1)"
  test₂ = refl

  test₃ : render 8 (ppr example) ≡ "1 - 1\n  - (1\n    - 1)"
  test₃ = refl

-- Expression₁.expr does not accept final whitespace. The grammar
-- below does.

module Expression₂ where

  open Expression₁ using (Expr; one; sub; example)

  module _ where

    open Grammar

    mutual

      expr : Grammar Expr
      expr = atom
           ∣ sub <$> ♯ expr <⊛ symbol′ "-" ⊛ atom

      atom : Grammar Expr
      atom = one <$ symbol′ "1"
           ∣ symbol′ "(" ⊛> ♯ expr <⊛ symbol′ ")"

  open Pretty

  one-doc : Doc atom one
  one-doc = left (<$ symbol)

  mutual

    ppr : Pretty-printer expr
    ppr one         = left one-doc
    ppr (sub e₁ e₂) =
      right (group (<$> final-line 2 6 (ppr e₁) <⊛
                    symbol-space ⊛ nest 2 (pprP e₂)))

    pprP : Pretty-printer atom
    pprP one = one-doc
    pprP e   = right (symbol ⊛> ppr e <⊛ symbol)

  test₁ : render 80 (ppr example) ≡ "1 - 1 - (1 - 1)"
  test₁ = refl

  test₂ : render 11 (ppr example) ≡ "1 - 1\n  - (1 - 1)"
  test₂ = refl

  test₃ : render 8 (ppr example) ≡ "1 - 1\n  - (1\n    - 1)"
  test₃ = refl

-- A somewhat larger expression example.

module Expression₃ where

  -- Expressions.

  data Expr : Set where
    one : Expr
    sub : Expr → Expr → Expr
    div : Expr → Expr → Expr
    var : Name → Expr

  -- Precedences.

  data Prec : Set where
    ′5 ′6 ′7 : Prec

  module _ where

    open Grammar

    -- One expression grammar for each precedence level.

    expr : Prec → Grammar Expr
    expr ′5 = ♯ expr ′6
            ∣ sub <$> ♯ expr ′5 <⊛ symbol′ "-" ⊛ ♯ expr ′6
    expr ′6 = ♯ expr ′7
            ∣ div <$> ♯ expr ′6 <⊛ symbol′ "/" ⊛ ♯ expr ′7
    expr ′7 = one <$ symbol′ "1"
            ∣ var <$> name-w
            ∣ symbol′ "(" ⊛> ♯ expr ′5 <⊛ symbol′ ")"

  open Pretty

  -- Document for one.

  one-doc : Doc (expr ′7) one
  one-doc = left (left (<$ symbol))

  -- Documents for variables.

  var-doc : ∀ x → Doc (expr ′7) (var x)
  var-doc x = left (right (<$> name-w-printer x))

  -- Adds parentheses to a document.

  parens : ∀ {e} → Doc (expr ′5) e → Doc (expr ′7) e
  parens d = right (symbol ⊛> d <⊛ symbol)

  -- Adds parentheses only when necessary (when p₁ < p₂).

  parens-if[_<_] : ∀ p₁ p₂ {e} → Doc (expr p₁) e → Doc (expr p₂) e
  parens-if[ ′5 < ′5 ] = id
  parens-if[ ′5 < ′6 ] = left ∘ parens
  parens-if[ ′5 < ′7 ] = parens
  parens-if[ ′6 < ′5 ] = left
  parens-if[ ′6 < ′6 ] = id
  parens-if[ ′6 < ′7 ] = parens ∘ left
  parens-if[ ′7 < ′5 ] = left ∘ left
  parens-if[ ′7 < ′6 ] = left
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
      right (group (<$> final-line 2 10 (expr-printer ′5 e₁) <⊛
                    symbol-space ⊛ nest 2 (expr-printer ′6 e₂)))

    div-printer : ∀ e₁ e₂ → Doc (expr ′6) (div e₁ e₂)
    div-printer e₁ e₂ =
      right (group (<$> final-line 2 10 (expr-printer ′6 e₁) <⊛
                    symbol-space ⊛ nest 2 (expr-printer ′7 e₂)))

  -- Unit tests.

  example : Expr
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
