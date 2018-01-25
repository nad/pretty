------------------------------------------------------------------------
-- Simple expressions
------------------------------------------------------------------------

-- Several examples based on Matsuda and Wang's "FliPpr: A Prettier
-- Invertible Printing System".

module Examples.Expression where

open import Algebra
open import Coinduction
open import Data.List
open import Data.List.Properties
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

private
  module LM {A : Set} = Monoid (++-monoid A)

open import Examples.Identifier
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
      expr = term
           ∣ sub <$> ♯ expr
                  <⊛ whitespace ⋆
                  <⊛ string′ "-"
                  <⊛ whitespace ⋆
                  ⊛  term

      term : Grammar Expr
      term = one <$ string′ "1"
           ∣    string′ "("
             ⊛> whitespace ⋆
             ⊛> ♯ expr
             <⊛ whitespace ⋆
             <⊛ string′ ")"

  open Pretty

  one-doc : Doc term one
  one-doc = left (<$ text)

  mutual

    expr-printer : Pretty-printer expr
    expr-printer one         = left one-doc
    expr-printer (sub e₁ e₂) =
      group (right (<$> expr-printer e₁ <⊛-tt
                    nest 2 line⋆ <⊛ text <⊛ space ⊛
                    nest 2 (term-printer e₂)))

    term-printer : Pretty-printer term
    term-printer one = one-doc
    term-printer e   =
      right (text ⊛> nil-⋆ ⊛> expr-printer e <⊛ nil-⋆ <⊛ text)

  example : Expr
  example = sub (sub one one) (sub one one)

  test₁ : render 80 (expr-printer example) ≡ "1 - 1 - (1 - 1)"
  test₁ = refl

  test₂ : render 11 (expr-printer example) ≡ "1 - 1\n  - (1 - 1)"
  test₂ = refl

  test₃ : render 8 (expr-printer example) ≡ "1 - 1\n  - (1\n    - 1)"
  test₃ = refl

-- Expression₁.expr does not accept final whitespace. The grammar
-- below does.

module Expression₂ where

  open Expression₁ using (Expr; one; sub; example)

  module _ where

    open Grammar

    mutual

      expr : Grammar Expr
      expr = term
           ∣ sub <$> ♯ expr <⊛ symbol′ "-" ⊛ term

      term : Grammar Expr
      term = one <$ symbol′ "1"
           ∣ symbol′ "(" ⊛> ♯ expr <⊛ symbol′ ")"

    private

      -- A manual proof of Trailing-whitespace expr (included for
      -- illustrative purposes; not used below).

      Trailing-whitespace″ : ∀ {A} → Grammar A → Set₁
      Trailing-whitespace″ g =
        ∀ {x s s₁ s₂} →
        x ∈ g · s₁ → s ∈ whitespace ⋆ · s₂ → x ∈ g · s₁ ++ s₂

      tw′-whitespace : Trailing-whitespace′ (whitespace ⋆)
      tw′-whitespace ⋆-[]-sem                                  w = _ , w
      tw′-whitespace (⋆-+-sem (⊛-sem {s₁ = s₁} (<$>-sem p) q)) w
        with tw′-whitespace q w
      ... | _ , r = _ , cast (P.sym $ LM.assoc s₁ _ _)
                             (⋆-+-sem (⊛-sem (<$>-sem p) r))

      tw″-symbol : ∀ {s} → Trailing-whitespace″ (symbol s)
      tw″-symbol (<⊛-sem {s₁ = s₁} p q) w =
        cast (P.sym $ LM.assoc s₁ _ _)
             (<⊛-sem p (proj₂ (tw′-whitespace q w)))

      tw″-term : Trailing-whitespace″ term
      tw″-term (left-sem (<$-sem p)) w =
        left-sem (<$-sem (tw″-symbol p w))
      tw″-term (right-sem (<⊛-sem {s₁ = s₁} p q)) w =
        cast (P.sym $ LM.assoc s₁ _ _)
             (right-sem (<⊛-sem p (tw″-symbol q w)))

      tw″-expr : Trailing-whitespace″ expr
      tw″-expr (left-sem p) w =
        left-sem (tw″-term p w)
      tw″-expr (right-sem (⊛-sem {s₁ = s₁} p q)) w =
        cast (P.sym $ LM.assoc s₁ _ _)
             (right-sem (⊛-sem p (tw″-term q w)))

      tw-expr : Trailing-whitespace expr
      tw-expr (<⊛-sem p w) = tw″-expr p w

  open Pretty

  one-doc : Doc term one
  one-doc = left (<$ symbol)

  mutual

    expr-printer : Pretty-printer expr
    expr-printer one         = left one-doc
    expr-printer (sub e₁ e₂) =
      group (right (<$> final-line 6 (expr-printer e₁) 2 <⊛
                    symbol-space ⊛ nest 2 (term-printer e₂)))

    term-printer : Pretty-printer term
    term-printer one = one-doc
    term-printer e   = right (symbol ⊛> expr-printer e <⊛ symbol)

  test₁ : render 80 (expr-printer example) ≡ "1 - 1 - (1 - 1)"
  test₁ = refl

  test₂ : render 11 (expr-printer example) ≡ "1 - 1\n  - (1 - 1)"
  test₂ = refl

  test₃ : render 8 (expr-printer example) ≡ "1 - 1\n  - (1\n    - 1)"
  test₃ = refl

-- A somewhat larger expression example.

module Expression₃ where

  -- Expressions.

  data Expr : Set where
    one : Expr
    sub : Expr → Expr → Expr
    div : Expr → Expr → Expr
    var : Identifier → Expr

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
            ∣ var <$> identifier-w
            ∣ symbol′ "(" ⊛> ♯ expr ′5 <⊛ symbol′ ")"

  open Pretty

  -- Document for one.

  one-doc : Doc (expr ′7) one
  one-doc = left (left (<$ symbol))

  -- Documents for variables.

  var-doc : ∀ x → Doc (expr ′7) (var x)
  var-doc x = left (right (<$> identifier-w-printer x))

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
      group (right (<$> final-line 10 (expr-printer ′5 e₁) 2 <⊛
                    symbol-space ⊛ nest 2 (expr-printer ′6 e₂)))

    div-printer : ∀ e₁ e₂ → Doc (expr ′6) (div e₁ e₂)
    div-printer e₁ e₂ =
      group (right (<$> final-line 10 (expr-printer ′6 e₁) 2 <⊛
                    symbol-space ⊛ nest 2 (expr-printer ′7 e₂)))

  -- Unit tests.

  example : Expr
  example = sub (div (var (str⁺ "x")) one) (sub one (var (str⁺ "y")))

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
