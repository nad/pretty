------------------------------------------------------------------------
-- A general grammar and pretty-printer for binary operators of
-- various (not necessarily linearly ordered) precedences
------------------------------------------------------------------------

-- The code below uses a variant of the operator grammars described by
-- Ulf Norell and me in "Parsing Mixfix Operators". For simplicity the
-- code only handles binary infix operators.

module Examples.Precedence where

open import Coinduction
open import Data.Bool using (Bool; T)
import Data.Bool.Properties as Bool-prop
open import Data.Char as Char using (Char)
open import Data.Fin using (Fin; zero; suc; #_)
import Data.Fin.Dec as Fin-dec
open import Data.Fin.Props using () renaming (_≟_ to _≟F_)
open import Data.List as List
open import Data.List.Any as Any; open Any.Membership-≡
open import Data.List.NonEmpty
open import Data.Nat using (ℕ)
open import Data.Product as Prod
import Data.String as String
open import Data.Unit
open import Data.Vec as Vec using (allFin)
open import Data.Vec.Properties
open import Function using (id; _∘_; _∘′_)
open import Relation.Binary
import Relation.Binary.List.Pointwise as Pointwise
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product

open import Examples.Name as Name hiding (name)
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

-- We can decide if two associativities are equal.

_≟A_ : Decidable (_≡_ {A = Associativity})
- ≟A - = yes P.refl
- ≟A ⇾ = no (λ ())
- ≟A ⇽ = no (λ ())
⇾ ≟A - = no (λ ())
⇾ ≟A ⇾ = yes P.refl
⇾ ≟A ⇽ = no (λ ())
⇽ ≟A - = no (λ ())
⇽ ≟A ⇾ = no (λ ())
⇽ ≟A ⇽ = yes P.refl

-- Operator names.

is-operator-char : Char → Bool
is-operator-char t =
  List.any (_≟C_ t) (String.toList "+-*/.:^<>=!&|")

Operator-name : Set
Operator-name = List⁺ (∃ (T ∘ is-operator-char))

-- Operators (parametrised by their associativity).

record Operator (assoc : Associativity) : Set where
  constructor ⟪_⟫
  field name : Operator-name

-- Equality of operators can be decided.

_≟O_ : ∀ {assoc} → Decidable (_≡_ {A = Operator assoc})
⟪ n₁ ∷ ns₁ ⟫ ≟O ⟪ n₂ ∷ ns₂ ⟫ =
  Dec.map′
    (P.cong ⟪_⟫ ∘ uncurry (P.cong₂ _,_))
    (< P.cong proj₁ , P.cong proj₂ > ∘′ P.cong Operator.name)
    ((n₁ ≟OC n₂)
       ×-dec
     Dec.map′ Pointwise.Rel≡⇒≡ Pointwise.≡⇒Rel≡
       (Pointwise.decidable _≟OC_ ns₁ ns₂))
  where
  _≟OC_ : Decidable (_≡_ {A = ∃ (T ∘ is-operator-char)})
  (c₁ , _) ≟OC (c₂ , _) =
    Dec.map′ lemma (P.cong proj₁) (c₁ Char.≟ c₂)
    where
    lemma : {p₁ p₂ : ∃ (T ∘ is-operator-char)} →
            proj₁ p₁ ≡ proj₁ p₂ → p₁ ≡ p₂
    lemma P.refl = P.cong ,_ (Bool-prop.proof-irrelevance _ _)

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
  any-precedence : List Precedence
  any-precedence = Vec.toList (allFin levels)

  -- A membership test for precedences.

  _∈?_ : ∀ (p : Precedence) ps → Dec (p ∈ ps)
  p ∈? ps = Any.any (_≟F_ p) ps

------------------------------------------------------------------------
-- Expressions

-- The code is parametrised by a precedence graph.

module Expr (g : Precedence-graph) where

  open Precedence-graph g

  -- Simple expressions.

  data E : Set where
    var : Name → E
    app : ∀ {assoc p} → E → (∃ λ op → op ∈ ops p assoc) → E → E

  -- The following function can be convenient to use when constructing
  -- examples.

  app′ :
    ∀ {assoc} → E → (op : Operator assoc) →
    {member : True (Fin-dec.any? λ p →
                      Any.any (_≟O_ op) (ops p assoc))} →
    E → E
  app′ e₁ op {member} e₂ = app e₁ (op , proj₂ (toWitness member)) e₂

  mutual

    -- A representation of operator parse trees.

    infix 8 _⟨_⟩_ _⟨_⟩⇾_ _⟨_⟩⇽_
    infix 6 _∙_

    -- Expr ps contains expressions where the outermost operator has
    -- one of the precedences in ps, parenthesised expressions, and
    -- variables.

    data Expr (ps : List Precedence) : Set where
      _∙_   : ∀ {p assoc} → p ∈ ps → Expr-in p assoc → Expr ps
      paren : Expr any-precedence → Expr ps
      var   : Name                → Expr ps

    -- Expr-in p assoc contains expressions where the outermost
    -- operator has precedence p (is /in/ precedence level p) and the
    -- associativity assoc.

    data Expr-in (p : Precedence) : Associativity → Set where
      _⟨_⟩_  : Expr (↑ p) → Inner (ops p -) → Expr (↑ p) → Expr-in p -
      _⟨_⟩⇾_ : Expr (↑ p) → Inner (ops p ⇾) → Outer p ⇾  → Expr-in p ⇾
      _⟨_⟩⇽_ : Outer p ⇽  → Inner (ops p ⇽) → Expr (↑ p) → Expr-in p ⇽

    -- Outer p assoc contains expressions where the head operator
    --   ⑴ has precedence p and associativity assoc, or
    --   ⑵ binds strictly tighter than p.

    data Outer (p : Precedence) (assoc : Associativity) : Set where
      similar : Expr-in p assoc → Outer p assoc
      tighter : Expr (↑ p)      → Outer p assoc

    -- Operators. The operators have to be members of the list.

    Inner : ∀ {assoc} → List (Operator assoc) → Set
    Inner ops = ∃ λ op → op ∈ ops

  -- Weakening.

  weaken : ∀ {p ps} → Expr ps → Expr (p ∷ ps)
  weaken (p∈ps ∙ e) = there p∈ps ∙ e
  weaken (paren e)  = paren e
  weaken (var x)    = var x

  mutual

    -- Conversion of parse trees to simple expressions.

    forget : ∀ {ps} → Expr ps → E
    forget (_ ∙ e)   = forget-in e
    forget (paren e) = forget e
    forget (var x)   = var x

    forget-in : ∀ {p assoc} → Expr-in p assoc → E
    forget-in (e₁ ⟨ op ⟩  e₂) = app (forget     e₁) op (forget     e₂)
    forget-in (e₁ ⟨ op ⟩⇾ e₂) = app (forget     e₁) op (forget-out e₂)
    forget-in (e₁ ⟨ op ⟩⇽ e₂) = app (forget-out e₁) op (forget     e₂)

    forget-out : ∀ {p assoc} → Outer p assoc → E
    forget-out (similar e) = forget-in e
    forget-out (tighter e) = forget e

  mutual

    -- Conversion of simple expressions to parse trees.

    recall : ∀ {ps} → E → Expr ps
    recall (var x)        = var x
    recall (app e₁ op e₂) = recall-app e₁ op e₂

    recall-app : ∀ {p ps assoc} →
                 E → (∃ λ op → op ∈ ops p assoc) → E → Expr ps
    recall-app {p} {ps} e₁ op e₂ with p ∈? ps
    ... | yes p∈ps = p∈ps ∙ recall-in _ e₁ op e₂
    ... | no  p∉ps = paren (∈⇒List-∈ (∈-allFin p) ∙
                            recall-in _ e₁ op e₂)

    recall-in : ∀ {p} assoc →
                E → (∃ λ op → op ∈ ops p assoc) → E → Expr-in p assoc
    recall-in - e₁ op e₂ = recall     e₁ ⟨ op ⟩  recall     e₂
    recall-in ⇾ e₁ op e₂ = recall     e₁ ⟨ op ⟩⇾ recall-out e₂
    recall-in ⇽ e₁ op e₂ = recall-out e₁ ⟨ op ⟩⇽ recall     e₂

    recall-out : ∀ {p assoc} → E → Outer p assoc
    recall-out {p₁} {a₁} (app {assoc = a₂} {p = p₂} e₁ op e₂) with p₁ ≟F p₂ | a₁ ≟A a₂
    recall-out (app e₁ op e₂) | yes P.refl | yes P.refl = similar (recall-in _ e₁ op e₂)
    recall-out (app e₁ op e₂) | _          | _          = tighter (recall-app  e₁ op e₂)
    recall-out e = tighter (recall e)

  module _ where

    open Grammar

    mutual

      -- Expression grammar.

      expr : Grammar (Expr any-precedence)
      expr = whitespace ⋆ ⊛> precs any-precedence <⊛ whitespace ⋆

      -- Grammar for a given list of precedence levels.

      precs : (ps : List Precedence) → Grammar (Expr ps)
      precs ps = paren <$ string′ "(" ⊛ ♯ expr <⊛ string′ ")"
               ∣ var <$> Name.name
               ∣ precs′ ps

      precs′ : (ps : List Precedence) → Grammar (Expr ps)
      precs′ []       = fail
      precs′ (p ∷ ps) =
          (λ { (_ , e) → here P.refl ∙ e }) <$> ♯ prec p
        ∣ weaken                            <$> precs′ ps

      -- Grammar for a given precedence level.

      prec : (p : Precedence) → Grammar (∃ (Expr-in p))
      prec p = ,_ <$> non-assoc p
             ∣ ,_ <$> right⁺ p
             ∣ ,_ <$> left⁺ p

      -- Operators of higher precedence (including parenthesised
      -- expressions and variables).

      higher : (p : Precedence) → Grammar (Expr (↑ p))
      higher p = precs (↑ p)

      -- Non-associative operators.

      non-assoc : (p : Precedence) → Grammar (Expr-in p -)
      non-assoc p = _⟨_⟩_ <$> precs (↑ p)
                           ⊛  operators (ops p -)
                           ⊛  precs (↑ p)

      -- Right-associative operators.

      right⁺ : (p : Precedence) → Grammar (Expr-in p ⇾)
      right⁺ p = _⟨_⟩⇾_ <$> precs (↑ p)
                         ⊛  operators (ops p ⇾)
                         ⊛  right⁺↑ p

      right⁺↑ : (p : Precedence) → Grammar (Outer p ⇾)
      right⁺↑ p = similar <$> ♯ right⁺ p
                ∣ tighter <$> precs (↑ p)

      -- Left-associative operators.

      left⁺ : (p : Precedence) → Grammar (Expr-in p ⇽)
      left⁺ p = _⟨_⟩⇽_ <$> left⁺↑ p
                        ⊛  operators (ops p ⇽)
                        ⊛  precs (↑ p)

      left⁺↑ : (p : Precedence) → Grammar (Outer p ⇽)
      left⁺↑ p = similar <$> ♯ left⁺ p
               ∣ tighter <$> precs (↑ p)

      -- An operator from a given list of operators.

      operators : ∀ {assoc} (os : List (Operator assoc)) →
                  Grammar (∃ λ op → op ∈ os)
      operators []         = fail
      operators (op ∷ ops) =    (tt <$ whitespace ⋆)
                             ⊛> (Prod.map id here <$> operator op)
                             <⊛ (tt <$ whitespace ⋆)
                           ∣ Prod.map id there <$> operators ops

  open Pretty

  mutual

    -- Pretty-printer. The produced layout could probably be improved,
    -- I have not tried very hard to make it pretty.

    expr-printer : Pretty-printer expr
    expr-printer e = ⋆-[] ⊛> precs-printer e <⊛ ⋆-[]

    precs-printer : ∀ {ps} → Pretty-printer (precs ps)
    precs-printer e = group (precs-printer′ e)
      where
      precs-printer′ : ∀ {ps} → Pretty-printer (precs ps)
      precs-printer′ (p∈ps ∙ e) = right (precs′-printer p∈ps e)
      precs-printer′ (paren e)  = left (left
                                    (<$ text ⊛ nest 1 (expr-printer e)
                                            <⊛ text))
      precs-printer′ (var x)    = left (right (<$> name-printer x))

    precs′-printer :
       ∀ {assoc p ps}
       (p∈ : p ∈ ps) (e : Expr-in p assoc) → Doc (precs′ ps) (p∈ ∙ e)
    precs′-printer (here P.refl) e = left (<$> prec-printer _ e)
    precs′-printer (there p∈ps)  e = right (<$> precs′-printer p∈ps e)

    prec-printer : ∀ {p} assoc (e : Expr-in p assoc) →
                   Doc (prec p) (assoc , e)
    prec-printer - e = left (left (<$> non-assoc-printer e))
    prec-printer ⇾ e = left (right (<$> right⁺-printer e))
    prec-printer ⇽ e = right (<$> left⁺-printer e)

    non-assoc-printer : ∀ {p} → Pretty-printer (non-assoc p)
    non-assoc-printer (e₁ ⟨ op ⟩ e₂) =
      <$> ↑-printer e₁ ⊛ operators-printer op ⊛ ↑-printer e₂

    right⁺-printer : ∀ {p} → Pretty-printer (right⁺ p)
    right⁺-printer (e₁ ⟨ op ⟩⇾ e₂) =
      <$> ↑-printer e₁ ⊛ operators-printer op ⊛ right⁺↑-printer e₂

    right⁺↑-printer : ∀ {p} → Pretty-printer (right⁺↑ p)
    right⁺↑-printer (similar e) = left  (<$> right⁺-printer e)
    right⁺↑-printer (tighter e) = right (<$> ↑-printer e)

    left⁺-printer : ∀ {p} → Pretty-printer (left⁺ p)
    left⁺-printer (e₁ ⟨ op ⟩⇽ e₂) =
      <$> left⁺↑-printer e₁ ⊛ operators-printer op ⊛ ↑-printer e₂

    left⁺↑-printer : ∀ {p} → Pretty-printer (left⁺↑ p)
    left⁺↑-printer (similar e) = left  (<$> left⁺-printer e)
    left⁺↑-printer (tighter e) = right (<$> ↑-printer e)

    ↑-printer : ∀ {p} → Pretty-printer (precs (↑ p))
    ↑-printer e = nest 2 (precs-printer e)

    operators-printer : ∀ {assoc} {os : List (Operator assoc)} →
                        Pretty-printer (operators os)
    operators-printer {os = []}     (_  , ())
    operators-printer {os = ._ ∷ _} (op , here P.refl) =
      left (line⋆ ⊛> <$> operator-printer op <⊛ <$ space)
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

example : Expr any-precedence
example = recall
  (app′ (app′ (app′ (app′ (var (str "y")) add (var (str "k")))
                    cons
                    (app′ (app′ (app′ (var (str "i"))
                                      add
                                      (var (str "0.5")))
                                add
                                (app′ (app′ (var (str "2"))
                                            div
                                            (app′ (var (str "0"))
                                                  sub
                                                  (var (str "1"))))
                                      mul
                                      (var (str "1"))))
                          cons
                          (var (str "xs"))))
              snoc
              (var (str "x")))
        snoc
        (app′ (var (str "z")) mul (var (str "z"))))

-- Some unit tests.

test₁ : render 80 (expr-printer example) ≡
        "(y + k <: i + 0.5 + 2 / (0 - 1) * 1 <: xs) :> x :> z * z"
test₁ = P.refl

test₂ : render 50 (expr-printer example) ≡
        "(y + k <: i + 0.5 + 2 / (0 - 1) * 1 <: xs)\n:> x\n:> z * z"
test₂ = P.refl

test₃ : render 40 (expr-printer example) ≡
        "(y + k\n   <: i + 0.5 + 2 / (0 - 1) * 1\n   <: xs)\n:> x\n:> z * z"
test₃ = P.refl

test₄ : render 30 (expr-printer example) ≡
        "(y + k\n   <: i\n     + 0.5\n     + 2 / (0 - 1) * 1\n   <: xs)\n:> x\n:> z * z"
test₄ = P.refl

test₅ : render 20 (expr-printer example) ≡
        "(y + k\n   <: i\n     + 0.5\n     + 2\n       / (0 - 1)\n       * 1\n   <: xs)\n:> x\n:> z * z"
test₅ = P.refl

test₆ : render 6 (expr-printer example) ≡
        "(y + k\n   <: i\n     + 0.5\n     + 2\n       / (0\n          - 1)\n       * 1\n   <: xs)\n:> x\n:> z\n  * z"
test₆ = P.refl

-- Note the strange rendering of "y + k" in the following test. If no
-- newline had been inserted before +, then the total width of this
-- subexpression would have been smaller.
--
-- Wadler's pretty-printing algorithm is not always optimal for texts
-- that do not fit in the allotted width, if by "optimal" we mean
-- "with as little overflow as possible". (I don't claim that Wadler
-- tried to minimise unavoidable overflow.) To see what I mean, try
-- running the following Haskell code, where the functions are
-- implemented as in Wadler's paper:
--
--   pretty 1 (group (nest 20 (line <> text "x")))
--
-- The result is "\n                    x", which is much worse than
-- the alternative result " x".

test₇ : render 5 (expr-printer example) ≡
        "(y\n     + k\n   <: i\n     + 0.5\n     + 2\n       / (0\n          - 1)\n       * 1\n   <: xs)\n:> x\n:> z\n  * z"
test₇ = P.refl
