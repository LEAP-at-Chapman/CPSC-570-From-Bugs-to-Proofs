{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- ============================================================================
-- Homework 02 — Functors, monads, IO, and small effects
-- ============================================================================
--
-- Submit this file with your definitions filled in (replace every `error "TODO"`).
-- You may add imports at the top. Do not change type signatures.
--
-- Prerequisites:
--   • tutorial-01-pure-types.hs
--   • tutorial-02-io-effects.hs
--
-- Big idea:
--   Haskell lets us write ordinary pure functions, then compose computations
--   that carry a little "extra context":
--
--     Maybe a        -- may fail / may be absent
--     [a]            -- may have many possible answers
--     Either e a     -- may fail with an explanation
--     IO a           -- may interact with the outside world
--
-- Constraints (honor the spirit of each problem):
--   Problem 1 — must use `fmap` or `<$>` on `Maybe` at least once; do not
--               pattern-match on `Maybe`.
--   Problem 2 — must use `fmap` or `<$>` on lists; do not use explicit
--               recursion.
--   Problem 3 — must use `do` notation or `(>>=)` for `Maybe`.
--   Problem 4 — must use list monad `do` notation. You may use `guard`.
--   Problem 5 — must return informative `Left` values for failed logins.
--   Problem 6 — keep pure text processing in `cleanLine`; use IO only for
--               reading and printing.
--   Problem 7 — use recursion in IO to keep asking until the user gives a
--               non-empty line.
--
-- Quick checks in GHCi (after `:load hw-effects.hs`):
--
--   cleanLine "  hello   haskell  "       ==>  "HELLO HASKELL"
--   cleanMaybeName (Just "  ada  lovelace ") ==>  Just "ADA LOVELACE"
--   cleanMaybeName Nothing                ==>  Nothing
--
--   tagAll "fruit" ["apple", "pear"]      ==>  ["fruit: apple","fruit: pear"]
--   tagAll "fruit" []                     ==>  []
--
--   firstKnownEmail 1 sampleNames sampleEmails ==>  Just "ada@example.com"
--   firstKnownEmail 3 sampleNames sampleEmails ==>  Nothing
--
--   pairsThatSum 5 [1,2,3,4]              ==>  [(1,4),(2,3),(3,2),(4,1)]
--   pairsThatSum 9 [1,2,3,4]              ==>  []
--
--   login "ada" "lambda" samplePasswords  ==>  Right "Welcome, ada!"
--   login "ada" "wrong" samplePasswords   ==>  Left BadPassword
--   login "grace" "x" samplePasswords     ==>  Left MissingUser
--
-- Try the IO exercises in GHCi:
--
--   runCleanerOnce
--   askNonEmpty "Course name? "
--
-- ============================================================================

module HwEffects where

import Control.Monad (guard)
import Data.Char (toUpper)

-- ----------------------------------------------------------------------------
-- Sample data for the Maybe / Either problems
-- ----------------------------------------------------------------------------

sampleNames :: [(Int, String)]
sampleNames =
  [ (1, "ada")
  , (2, "alan")
  ]

sampleEmails :: [(String, String)]
sampleEmails =
  [ ("ada", "ada@example.com")
  , ("alan", "alan@example.com")
  ]

samplePasswords :: [(String, String)]
samplePasswords =
  [ ("ada", "lambda")
  , ("alan", "turing")
  ]

-- ----------------------------------------------------------------------------
-- Problem 1 — Functor over Maybe
-- ----------------------------------------------------------------------------
--
-- `words` splits on whitespace and drops extra spaces.
-- `unwords` joins words back together with one space between them.
--
-- Implement `cleanLine` first as a pure helper:
--
--   cleanLine "  hello   haskell  " == "HELLO HASKELL"
--
-- Then implement `cleanMaybeName` by applying `cleanLine` inside `Maybe` using
-- `fmap` or `<$>`.

cleanLine :: String -> String
cleanLine = error "TODO: Problem 1 — cleanLine"

cleanMaybeName :: Maybe String -> Maybe String
cleanMaybeName = error "TODO: Problem 1 — cleanMaybeName"

-- ----------------------------------------------------------------------------
-- Problem 2 — Functor over lists
-- ----------------------------------------------------------------------------
--
-- Add a label to every item in a list.
--
--   tagAll "fruit" ["apple", "pear"] == ["fruit: apple", "fruit: pear"]
--
-- Use `fmap` or `<$>` on the list. Do not write explicit recursion.

tagAll :: String -> [String] -> [String]
tagAll = error "TODO: Problem 2 — tagAll"

-- ----------------------------------------------------------------------------
-- Problem 3 — Maybe as a small failure effect
-- ----------------------------------------------------------------------------
--
-- `lookup` already returns `Maybe`:
--
--   lookup 1 sampleNames       == Just "ada"
--   lookup "ada" sampleEmails  == Just "ada@example.com"
--
-- Implement `firstKnownEmail` so it:
--
--   1. looks up the user's name from an integer id
--   2. uses that name to look up the user's email
--   3. returns `Nothing` if either lookup fails
--
-- Use `do` notation or `(>>=)` for `Maybe`.

firstKnownEmail :: Int -> [(Int, String)] -> [(String, String)] -> Maybe String
firstKnownEmail = error "TODO: Problem 3 — firstKnownEmail"

-- ----------------------------------------------------------------------------
-- Problem 4 — lists as nondeterminism
-- ----------------------------------------------------------------------------
--
-- A list can represent "many possible answers." In list-monad `do` notation,
-- each line draws from all possible choices.
--
-- Return all ordered pairs `(x, y)` where both values come from the input list
-- and add up to the target.
--
--   pairsThatSum 5 [1,2,3,4] == [(1,4),(2,3),(3,2),(4,1)]
--
-- Use list `do` notation. You may use `guard` from Control.Monad to keep only
-- pairs whose sum matches the target.

pairsThatSum :: Int -> [Int] -> [(Int, Int)]
pairsThatSum = error "TODO: Problem 4 — pairsThatSum"

-- ----------------------------------------------------------------------------
-- Problem 5 — Either as an error-reporting effect
-- ----------------------------------------------------------------------------
--
-- `Maybe` can say "something failed"; `Either` can explain what failed.

data LoginError
  = MissingUser
  | BadPassword
  deriving (Eq, Show)

-- Given a username, password attempt, and password table:
--
--   • return `Left MissingUser` if the username is not in the table
--   • return `Left BadPassword` if the username exists but the password differs
--   • return `Right ("Welcome, " ++ username ++ "!")` if login succeeds

login :: String -> String -> [(String, String)] -> Either LoginError String
login = error "TODO: Problem 5 — login"

-- ----------------------------------------------------------------------------
-- Problem 6 — IO shell around a pure core
-- ----------------------------------------------------------------------------
--
-- Read one line from the user, clean it with `cleanLine`, and print the result.
--
-- Keep `cleanLine` pure. This function should only be responsible for the
-- outside-world part: prompt, read, print.

runCleanerOnce :: IO ()
runCleanerOnce = error "TODO: Problem 6 — runCleanerOnce"

-- ----------------------------------------------------------------------------
-- Problem 7 — recursive IO
-- ----------------------------------------------------------------------------
--
-- Ask the user a question until they type a non-empty answer.
--
-- Example interaction:
--
--   Course name?
--
--   Please enter a non-empty answer.
--   Course name?
--   CPSC 570
--
-- The result should be the non-empty string, cleaned with `cleanLine`.

askNonEmpty :: String -> IO String
askNonEmpty = error "TODO: Problem 7 — askNonEmpty"

