------------------------------------------------------------------------
-- Correct-by-construction pretty-printing
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- A pretty-printing library that guarantees that pretty-printers are
-- correct (on the assumption that grammars are unambiguous).

{-# OPTIONS --guardedness #-}

module README where

-- Various utility functions.

import Utilities

-- Infinite grammars.

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

-- Abstract grammars. (Not used by the pretty-printer.)

import Grammar.Abstract

-- Grammars defined as functions from non-terminals to productions.
-- (Not used by the pretty-printer.)

import Grammar.Non-terminal

-- A README directed towards readers of the paper
-- "Correct-by-Construction Pretty-Printing".

import README.Correct-by-Construction-Pretty-Printing
