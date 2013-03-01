------------------------------------------------------------------------
-- Correct-by-construction pretty-printing
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- A parsing/pretty-printing library which guarantees that
-- pretty-printers are correct (on the assumption that grammars are
-- unambiguous).
--
-- I don't start from the pretty-printer, but treat pretty-printer
-- documents as a kind of decorated parse trees.

module README where

-- Some boolean-valued operators (equality, less than, …).

import Tests

-- Grammars.

import Grammar

-- Pretty-printing.

import Pretty

-- Examples.

import Examples
