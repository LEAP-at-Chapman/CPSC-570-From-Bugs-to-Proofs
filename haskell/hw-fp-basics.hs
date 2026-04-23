{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- ============================================================================
-- Homework — recursion, pattern matching, higher-order functions, Functor
-- ============================================================================
--
-- Submit this file with your definitions filled in (replace every `error "TODO"`).
-- You may add imports at the top. Do not change type signatures unless the
-- instructor says otherwise.
--
-- Constraints (honor the spirit of each problem):
--   Problem 1 — use pattern matching and recursion only (no `filter`, `map`,
--               list comprehensions, or library recursion schemes).
--   Problem 2 — recursion only (same restrictions as Problem 1).
--   Problem 3 — must use `filter` and `length` from the Prelude (or your own
--               `myFilter` / `myLength` from class, but not a single hand-rolled
--               loop that counts without `filter`).
--   Problem 4 — must use `fmap` or `<$>` on `Maybe` at least once; do not
--               pattern-match on `Maybe` for this function.
--   Problem 5 — merge sort: use recursion and pattern matching for `merge` and
--               `mergeSort`. You may use `splitAt` and `length`. Do not use `sort`,
--               `sortBy`,`insert`, `unfoldr`, or other ready-made sorting utilities.
--
-- Quick checks in GHCi (after `:load hw-fp-basics.hs`):
--
--   skip1 [1,2,3,4,5]              ==>  [1,3,5]
--   skip1 "abcdef"                ==>  "ace"
--   mySum [3,1,4]                 ==>  8
--   mySum []                      ==>  0
--   countPasses [even,(>10),odd] 14   ==>  2
--        (on 14, `even` and `(>10)` are True; `odd` is False — so two pass)
--   shoutInside (Just "hi")       ==>  Just "HI"
--   shoutInside Nothing           ==>  Nothing
--   mergeSort [3,1,4,1,5]         ==>  [1,1,3,4,5]
--   mergeSort "cba"               ==>  "abc"
--
-- ============================================================================

module HwFpBasics where

-- You will likely want: import Data.Char (toUpper)

-- ----------------------------------------------------------------------------
-- Problem 1 — pattern matching & recursion
-- ----------------------------------------------------------------------------
--
-- Keep the first element, drop the second, keep the third, drop the fourth, …
-- Empty list stays empty.

skip1 :: [a] -> [a]
skip1 = error "TODO: Problem 1 — skip1"

-- ----------------------------------------------------------------------------
-- Problem 2 — recursion
-- ----------------------------------------------------------------------------
--
-- Sum all integers in the list. Define it recursively; do not use `sum`,
-- `foldr`, `foldl`, or list comprehensions.

mySum :: [Int] -> Int
mySum = error "TODO: Problem 2 — mySum"

-- ----------------------------------------------------------------------------
-- Problem 3 — higher-order functions
-- ----------------------------------------------------------------------------
--
-- Given a list of predicates and a value `x`, return how many predicates
-- return `True` when applied to `x`. Use `filter` and `length`.

countPasses :: [Int -> Bool] -> Int -> Int
countPasses = error "TODO: Problem 3 — countPasses"

-- ----------------------------------------------------------------------------
-- Problem 4 — Functor
-- ----------------------------------------------------------------------------
--
-- If the argument is `Nothing`, return `Nothing`. If it is `Just s`, return
-- `Just` with the same string in upper case (use `toUpper` from `Data.Char` on
-- every character). Implement using `fmap` or `<$>` on `Maybe` only (no
-- explicit `case` / pattern match on `Maybe`).

shoutInside :: Maybe String -> Maybe String
shoutInside = error "TODO: Problem 4 — shoutInside"

-- ----------------------------------------------------------------------------
-- Problem 5 — merge sort (recursion + pattern matching)
-- ----------------------------------------------------------------------------
--
-- `merge` combines two lists that are already sorted (non-decreasing) into one
-- sorted list. When the heads are equal, take from the *first* list first
-- (so `merge [1,3] [1,2]` is `[1,1,2,3]`).
--
-- `mergeSort` sorts any finite list. Base cases: empty list and singleton list.
-- Otherwise split roughly in half, `mergeSort` each half, then `merge`.

merge :: Ord a => [a] -> [a] -> [a]
merge = error "TODO: Problem 5 — merge"

mergeSort :: Ord a => [a] -> [a]
mergeSort = error "TODO: Problem 5 — mergeSort"
