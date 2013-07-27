------------------------------------------------------------------------
-- Correct-by-construction pretty-printing
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- A pretty-printing library that guarantees that pretty-printers are
-- correct (on the assumption that grammars are unambiguous).

module README where

-- Various utility functions.

import Utilities

-- Grammars.

import Grammar.Infinite.Basic
import Grammar.Infinite

-- Pretty-printing (documents and document combinators).

import Pretty

-- Document renderers.

import Renderer

-- Examples.

import Examples.Bool
import Examples.Expression
import Examples.Identifier
import Examples.Identifier-list
import Examples.Precedence
import Examples.Tree
import Examples.XML

-- A README directed towards readers of the paper
-- "Correct-by-Construction Pretty-Printing".

import README.Correct-by-Construction-Pretty-Printing
