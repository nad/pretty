------------------------------------------------------------------------
-- Trees
------------------------------------------------------------------------

-- This example is based on one in Wadler's "A prettier printer".

module Examples.Tree where

open import Coinduction
open import Data.List as List
open import Data.List.NonEmpty as List⁺
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Examples.Name
import Grammar.Infinite
import Pretty
open import Renderer
open import Utilities

data Tree : Set where
  node : Name → List Tree → Tree

module _ where

  open Grammar.Infinite

  mutual

    tree : Grammar Tree
    tree = node <$> name-w ⊛ brackets

    brackets : Grammar (List Tree)
    brackets = return []
             ∣ List⁺.toList <$> (symbol′ "[" ⊛> ♯ trees <⊛ symbol′ "]")

    trees : Grammar (List⁺ Tree)
    trees = _∷_ <$> tree ⊛ commas-and-trees

    commas-and-trees : Grammar (List Tree)
    commas-and-trees = (symbol′ "," ⊛> tree) ⋆

open Pretty

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
      group (<$> name-w-printer s ⊛
             nest (List.length s) (brackets-printer ts))

    brackets-printer : Pretty-printer brackets
    brackets-printer []       = left nil
    brackets-printer (t ∷ ts) =
      right (<$> (symbol ⊛> nest 1 (trees-printer (t ∷ ts)) <⊛ symbol))

    trees-printer : Pretty-printer trees
    trees-printer (t ∷ ts) =
      <$> tree-printer t ⊛ commas-and-trees-printer ts

    commas-and-trees-printer : Pretty-printer commas-and-trees
    commas-and-trees-printer []       = nil-⋆
    commas-and-trees-printer (t ∷ ts) =
      cons-⋆ (symbol-line ⊛> tree-printer t)
             (commas-and-trees-printer ts)

module Printer₂ where

  mutual

    tree-printer : Pretty-printer tree
    tree-printer (node s ts) =
      <$> name-w-printer s ⊛ brackets-printer ts

    -- Note that this printer is not defined in exactly the same way
    -- as Wadler's: Wadler used "nest 2" once, here it is used twice
    -- (in the bracket combinator). Why? His one nest spanned over two
    -- parts of the grammar (the opening bracket and the trees,
    -- respectively), but not all of the second part (not the "line"
    -- combinator).

    brackets-printer : Pretty-printer brackets
    brackets-printer []       = left nil
    brackets-printer (t ∷ ts) =
      right (<$> bracket 7 (trees-printer (t ∷ ts)))

    trees-printer : Pretty-printer trees
    trees-printer (t ∷ ts) =
      <$> tree-printer t ⊛ commas-and-trees-printer ts

    commas-and-trees-printer : Pretty-printer commas-and-trees
    commas-and-trees-printer []       = nil-⋆
    commas-and-trees-printer (t ∷ ts) =
      cons-⋆ (symbol-line ⊛> tree-printer t)
             (commas-and-trees-printer ts)

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
