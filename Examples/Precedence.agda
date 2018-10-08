------------------------------------------------------------------------
-- A general grammar and pretty-printer for binary operators of
-- various (not necessarily linearly ordered) precedences
------------------------------------------------------------------------

-- The code below uses a variant of the operator grammars described by
-- Ulf Norell and me in "Parsing Mixfix Operators". For simplicity the
-- code only handles binary infix operators.

module Examples.Precedence where

open import Codata.Musical.Notation
open import Data.Bool using (Bool; T)
import Data.Bool.Properties as Bool-prop
open import Data.Char using (Char)
open import Data.Char.Unsafe as Char using (_==_)
open import Data.Fin using (Fin; zero; suc; #_)
import Data.Fin.Dec as Fin-dec
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List as List
open import Data.List.Any as Any
open import Data.List.Membership.Propositional
open import Data.List.NonEmpty as List⁺
import Data.List.Relation.Pointwise as Pointwise
open import Data.Nat using (ℕ)
open import Data.Product as Prod
import Data.String as String
open import Data.Unit
import Data.Vec as Vec
open import Data.Vec.Membership.Propositional.Properties
open import Function using (id; _∘_; _∘′_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Nullary.Product

open import Examples.Identifier
open import Grammar.Infinite as Grammar using (Grammar-for)
open import Pretty using (Pretty-printer-for)
open import Renderer
open import Utilities

------------------------------------------------------------------------
-- Binary operators

-- Associativities.

data Associativity : Set where
  -   -- Non-associative.
   ⇾  -- Right associative.
   ⇽  -- Left associative.
     : Associativity

-- Operator names.

is-operator-char : Char → Bool
is-operator-char t =
  List.any (_==_ t) (String.toList "+-*/.:^<>=!&|")

Operator-name : Set
Operator-name = List⁺ (∃ (T ∘ is-operator-char))

-- Operators (parametrised by their associativity).

record Operator (assoc : Associativity) : Set where
  constructor ⟪_⟫
  field name : Operator-name

-- Equality of operators can be decided.

_≟O_ : ∀ {assoc} → Decidable (_≡_ {A = Operator assoc})
⟪ n₁ ∷ ns₁ ⟫ ≟O ⟪ n₂ ∷ ns₂ ⟫ =
  Decidable.map′
    (P.cong ⟪_⟫ ∘ uncurry (P.cong₂ _∷_))
    (< P.cong List⁺.head , P.cong List⁺.tail > ∘′ P.cong Operator.name)
    ((n₁ ≟OC n₂)
       ×-dec
     Pointwise.decidable-≡ _≟OC_ ns₁ ns₂)
  where
  _≟OC_ : Decidable (_≡_ {A = ∃ (T ∘ is-operator-char)})
  (c₁ , _) ≟OC (c₂ , _) =
    Decidable.map′ lemma (P.cong proj₁) (c₁ Char.≟ c₂)
    where
    lemma : {p₁ p₂ : ∃ (T ∘ is-operator-char)} →
            proj₁ p₁ ≡ proj₁ p₂ → p₁ ≡ p₂
    lemma {p₁ = _ , _} {p₂ = ._ , _} P.refl =
      P.cong -,_ (Bool-prop.T-irrelevance _ _)

-- A grammar for a given operator name.

operator-name : Grammar-for Operator-name
operator-name n = list⁺ (tok-sat _) n
  where open Grammar

-- A pretty-printer for operator names.

operator-name-printer : Pretty-printer-for operator-name
operator-name-printer n = list⁺ tok-sat n
  where open Pretty

-- A grammar for a given operator.

operator : ∀ {assoc} → Grammar-for (Operator assoc)
operator op =
  Prod.map ⟪_⟫ (P.cong ⟪_⟫) <$> operator-name (Operator.name op)
  where open Grammar

-- A pretty-printer for operators.

operator-printer : ∀ {assoc} →
                   Pretty-printer-for (operator {assoc = assoc})
operator-printer op = <$> operator-name-printer (Operator.name op)
  where open Pretty

------------------------------------------------------------------------
-- Precedence graphs

-- Precedence graphs are represented by the number of precedence
-- levels, plus functions mapping node identifiers (precedences) to
-- node contents and successor precedences.

record Precedence-graph : Set where
  field

    -- The number of precedence levels.

    levels : ℕ

  -- Precedence levels.

  Precedence : Set
  Precedence = Fin levels

  field

    -- The precedence level's operators.

    ops : Precedence → (assoc : Associativity) → List (Operator assoc)

    -- The immediate successors of the precedence level.

    ↑ : Precedence → List Precedence

  -- All precedence levels.

  all-precedences : List Precedence
  all-precedences = Vec.toList (Vec.allFin levels)

  -- Every precedence level is a member of all-precedences.

  ∈-all-precedences : ∀ {p} → p ∈ all-precedences
  ∈-all-precedences {p} = ∈-toList⁺ (∈-allFin⁺ p)

  -- A membership test for precedences.

  _∈?_ : ∀ (p : Precedence) ps → Dec (p ∈ ps)
  p ∈? ps = Any.any (_≟F_ p) ps

------------------------------------------------------------------------
-- Expressions

-- The code is parametrised by a precedence graph.

module Expr (g : Precedence-graph) where

  open Precedence-graph g

  -- Operators with a given precedence and associativity.

  Op : Precedence → Associativity → Set
  Op p assoc = ∃ λ op → op ∈ ops p assoc

  mutual

    -- Expressions.

    data Expr : Set where
      var : Identifier → Expr
      app : ∀ {p} → ∃ (App p) → Expr

    -- Binary operator applications where the operator has a given
    -- precedence and associativity.

    App : Precedence → Associativity → Set
    App p assoc = Expr × Op p assoc × Expr

  -- The following function can be convenient to use when constructing
  -- examples.

  _⟨_⟩_ :
    ∀ {assoc} → Expr → (op : Operator assoc) →
    {member : True (Fin-dec.any? λ p →
                      Any.any (_≟O_ op) (ops p assoc))} →
    Expr → Expr
  _⟨_⟩_ e₁ op {member} e₂ =
    app (_ , e₁ , (op , proj₂ (toWitness member)) , e₂)

  module _ where

    open Grammar

    mutual

      -- Expression grammar.

      expr : Grammar Expr
      expr = whitespace ⋆ ⊛> precs all-precedences <⊛ whitespace ⋆

      -- Grammar for a given list of precedence levels.

      precs : List Precedence → Grammar Expr
      precs ps = string′ "(" ⊛> ♯ expr <⊛ string′ ")"
               ∣ var <$> identifier
               ∣ precs′ ps

      precs′ : List Precedence → Grammar Expr
      precs′ []       = fail
      precs′ (p ∷ ps) = app <$> ♯ prec p
                      ∣ precs′ ps

      -- Grammar for a given precedence level.

      prec : (p : Precedence) → Grammar (∃ (App p))
      prec p = -,_ <$> non-assoc p
             ∣ -,_ <$> right⁺ p
             ∣ -,_ <$> left⁺ p

      -- Grammar for higher precedence levels.

      higher : Precedence → Grammar Expr
      higher p = precs (↑ p)

      -- Non-associative operators.

      non-assoc : (p : Precedence) → Grammar (App p -)
      non-assoc p = (λ e₁ op e₂ → e₁ , op , e₂) <$>
        higher p ⊛ operators (ops p -) ⊛ higher p

      -- Right-associative operators.

      right⁺ : (p : Precedence) → Grammar (App p ⇾)
      right⁺ p = (λ e₁ op e₂ → e₁ , op , e₂) <$>
        higher p ⊛ operators (ops p ⇾) ⊛ right⁺↑ p

      right⁺↑ : Precedence → Grammar Expr
      right⁺↑ p = (app ∘ -,_) <$> ♯ right⁺ p
                ∣ higher p

      -- Left-associative operators.

      left⁺ : (p : Precedence) → Grammar (App p ⇽)
      left⁺ p = (λ e₁ op e₂ → e₁ , op , e₂) <$>
        left⁺↑ p ⊛ operators (ops p ⇽) ⊛ higher p

      left⁺↑ : Precedence → Grammar Expr
      left⁺↑ p = (app ∘ -,_) <$> ♯ left⁺ p
               ∣ higher p

      -- An operator from a given list of operators.

      operators : ∀ {assoc} (os : List (Operator assoc)) →
                  Grammar (∃ λ op → op ∈ os)
      operators []         = fail
      operators (op ∷ ops) =    whitespace ⋆
                             ⊛> (Prod.map id here <$> operator op)
                             <⊛ whitespace ⋆
                           ∣ Prod.map id there <$> operators ops

  open Pretty

  mutual

    -- Pretty-printer. The produced layout could probably be improved,
    -- I have not tried very hard to make it pretty.

    expr-printer : Pretty-printer expr
    expr-printer e = nil-⋆ ⊛> precs-printer e <⊛ nil-⋆

    precs-printer : ∀ {ps} → Pretty-printer (precs ps)
    precs-printer e = group (precs-printer′ e)
      where
      precs-printer′ : ∀ {ps} → Pretty-printer (precs ps)
      precs-printer′ (var x) = left (right (<$> identifier-printer x))
      precs-printer′ {ps} (app {p = p} e)
        with p ∈? ps
      ... | yes p∈ps = right (precs′-printer p∈ps e)
      ... | no  _    =
        -- Incorrect precedence level: insert parentheses.
        left (left (text ⊛> nest 1 d <⊛ text))
        where
        d = nil-⋆                                       ⊛>
            right (precs′-printer ∈-all-precedences e) <⊛
            nil-⋆

    precs′-printer :
      ∀ {p ps} → p ∈ ps → (e : ∃ (App p)) → Doc (precs′ ps) (app e)
    precs′-printer (here P.refl) e = left  (<$> prec-printer e)
    precs′-printer (there p∈ps)  e = right (precs′-printer p∈ps e)

    prec-printer : ∀ {p} → Pretty-printer (prec p)
    prec-printer (- , e) = left (left (<$> non-assoc-printer e))
    prec-printer (⇾ , e) = left (right (<$> right⁺-printer e))
    prec-printer (⇽ , e) = right (<$> left⁺-printer e)

    non-assoc-printer : ∀ {p} → Pretty-printer (non-assoc p)
    non-assoc-printer (e₁ , op , e₂) =
      <$> higher-printer e₁ ⊛ operators-printer op ⊛ higher-printer e₂

    right⁺-printer : ∀ {p} → Pretty-printer (right⁺ p)
    right⁺-printer (e₁ , op , e₂) =
      <$> higher-printer e₁ ⊛ operators-printer op ⊛ right⁺↑-printer e₂

    right⁺↑-printer : ∀ {p} → Pretty-printer (right⁺↑ p)
    right⁺↑-printer {p₁} (app {p = p₂} (⇾ , e))
      with p₁ ≟F p₂ | higher-printer (app (⇾ , e))
    right⁺↑-printer (app (⇾ , e)) | yes P.refl | _ =
      -- Matching precedence and associativity.
      left (<$> right⁺-printer e)
    right⁺↑-printer (app (⇾ , e)) | no _ | d = right d
    right⁺↑-printer e = right (higher-printer e)

    left⁺-printer : ∀ {p} → Pretty-printer (left⁺ p)
    left⁺-printer (e₁ , op , e₂) =
      <$> left⁺↑-printer e₁ ⊛ operators-printer op ⊛ higher-printer e₂

    left⁺↑-printer : ∀ {p} → Pretty-printer (left⁺↑ p)
    left⁺↑-printer {p₁} (app {p = p₂} (⇽ , e))
      with p₁ ≟F p₂ | higher-printer (app (⇽ , e))
    left⁺↑-printer (app (⇽ , e)) | yes P.refl | _ =
      -- Matching precedence and associativity.
      left (<$> left⁺-printer e)
    left⁺↑-printer (app (⇽ , e)) | no _ | d = right d
    left⁺↑-printer e = right (higher-printer e)

    higher-printer : ∀ {p} → Pretty-printer (higher p)
    higher-printer e = nest 2 (precs-printer e)

    operators-printer : ∀ {assoc} {os : List (Operator assoc)} →
                        Pretty-printer (operators os)
    operators-printer {os = []}     (_  , ())
    operators-printer {os = ._ ∷ _} (op , here P.refl) =
      left (line⋆ tt-⊛> <$> operator-printer op <⊛ space)
    operators-printer {os =  _ ∷ _} (_  , there op∈os) =
      right (<$> operators-printer (_ , op∈os))

------------------------------------------------------------------------
-- An example

-- Some operators.

add : Operator ⇽
add = ⟪ str⁺ "+" ⟫

sub : Operator ⇽
sub = ⟪ str⁺ "-" ⟫

mul : Operator ⇽
mul = ⟪ str⁺ "*" ⟫

div : Operator ⇽
div = ⟪ str⁺ "/" ⟫

cons : Operator ⇾
cons = ⟪ str⁺ "<:" ⟫

snoc : Operator ⇽
snoc = ⟪ str⁺ ":>" ⟫

-- A precedence graph.

g : Precedence-graph
g = record { ops = ops; ↑ = ↑ }
  where
  ops : Fin 3 → (assoc : Associativity) → List (Operator assoc)
  ops zero             ⇽ = snoc ∷ []
  ops zero             ⇾ = cons ∷ []
  ops (suc zero)       ⇽ = add ∷ sub ∷ []
  ops (suc (suc zero)) ⇽ = mul ∷ div ∷ []
  ops _                _ = []

  ↑ : Fin 3 → List (Fin 3)
  ↑ zero          = # 1 ∷ # 2 ∷ []
  ↑ (suc zero)    = # 2 ∷ []
  ↑ (suc (suc p)) = []

open Precedence-graph g
open Expr g

-- An expression.

example : Expr
example =
  (((var (str⁺ "y") ⟨ add ⟩ var (str⁺ "k"))
      ⟨ cons ⟩
    (((var (str⁺ "i") ⟨ add ⟩ var (str⁺ "foo"))
        ⟨ add ⟩
      ((var (str⁺ "a")
          ⟨ div ⟩
        (var (str⁺ "b") ⟨ sub ⟩ var (str⁺ "c")))
         ⟨ mul ⟩
       var (str⁺ "c")))
       ⟨ cons ⟩
     (var (str⁺ "xs"))))
     ⟨ snoc ⟩
   (var (str⁺ "x")))
    ⟨ snoc ⟩
  (var (str⁺ "z") ⟨ mul ⟩ var (str⁺ "z"))

-- Some unit tests.

test₁ : render 80 (expr-printer example) ≡
        "(y + k <: i + foo + a / (b - c) * c <: xs) :> x :> z * z"
test₁ = P.refl

test₂ : render 50 (expr-printer example) ≡
        "(y + k <: i + foo + a / (b - c) * c <: xs)\n:> x\n:> z * z"
test₂ = P.refl

test₃ : render 40 (expr-printer example) ≡
        "(y + k\n   <: i + foo + a / (b - c) * c\n   <: xs)\n:> x\n:> z * z"
test₃ = P.refl

test₄ : render 30 (expr-printer example) ≡
        "(y + k\n   <: i\n     + foo\n     + a / (b - c) * c\n   <: xs)\n:> x\n:> z * z"
test₄ = P.refl

test₅ : render 20 (expr-printer example) ≡
        "(y + k\n   <: i\n     + foo\n     + a\n       / (b - c)\n       * c\n   <: xs)\n:> x\n:> z * z"
test₅ = P.refl

test₆ : render 6 (expr-printer example) ≡
        "(y + k\n   <: i\n     + foo\n     + a\n       / (b\n          - c)\n       * c\n   <: xs)\n:> x\n:> z\n  * z"
test₆ = P.refl

-- The rendering of "y + k" in the following test may seem strange: if
-- no newline had been inserted before +, then the total width of this
-- subexpression would have been smaller.
--
-- Wadler's pretty-printing algorithm is not always optimal for texts
-- that do not fit in the allotted width, if by "optimal" we mean
-- "with as little overflow as possible". To see what I mean, try
-- running the following Haskell code, where the functions are
-- implemented as in Wadler's paper:
--
--   pretty 1 (group (nest 20 (line <> text "x")))
--
-- The result is "\n                    x", which can be seen as much
-- worse than the alternative result " x". However, note that Wadler
-- uses a lexicographic definition of "better", in which
-- "\n                    x" is better than " x", because the first
-- line of "\n                    x" fits, but the first line of " x"
-- doesn't.

test₇ : render 5 (expr-printer example) ≡
        "(y\n     + k\n   <: i\n     + foo\n     + a\n       / (b\n          - c)\n       * c\n   <: xs)\n:> x\n:> z\n  * z"
test₇ = P.refl
