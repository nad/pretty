------------------------------------------------------------------------
-- A README directed towards readers of the paper
-- "Correct-by-Construction Pretty-Printing"
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

module README.Correct-by-Construction-Pretty-Printing where

------------------------------------------------------------------------
-- 2: Grammars

-- The basic grammar data type, including its semantics. Only a small
-- number of derived combinators is defined directly for this data
-- type.

import Grammar.Infinite.Basic

-- The extended grammar data type mentioned in Section 4.3, along with
-- a semantics and lots of derived combinators. This type is proved to
-- be no more expressive than the previous one.

import Grammar.Infinite

------------------------------------------------------------------------
-- 3: Pretty-Printers

import Pretty

------------------------------------------------------------------------
-- 4: Examples

-- Reusable document combinators introduced in this section.

import Pretty

-- The symbol combinator and the heuristic procedure
-- trailing-whitespace.

import Grammar.Infinite

-- 4.1: Boolean literals.

import Examples.Bool

-- 4.2: Expressions, and 4.3: Expressions, Take Two.

import Examples.Expression

-- 4.4: Identifiers.

import Examples.Identifier

-- 4.5: Other Examples.

-- Another expression example based on one in Matsuda and Wang's
-- "FliPpr: A Prettier Invertible Printing System".

import Examples.Expression

-- An example based on one in Swierstra and Chitil's "Linear, bounded,
-- functional pretty-printing".

import Examples.Identifier-list

-- Two examples, both based on examples in Wadler's "A prettier
-- printer".

import Examples.Tree
import Examples.XML

-- A general grammar and pretty-printer for binary operators of
-- various (not necessarily linearly ordered) precedences.

import Examples.Precedence

------------------------------------------------------------------------
-- 5: Renderers

import Renderer

-- Unambiguous and Parser.

import Grammar.Infinite

-- The fill combinator.

import Pretty
