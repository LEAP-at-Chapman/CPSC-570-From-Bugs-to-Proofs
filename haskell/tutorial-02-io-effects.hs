{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- ============================================================================
-- Tutorial 02 — Side effects: IO and the "effectful shell" (first exposure)
-- ============================================================================
--
-- Prerequisite: tutorial-01-pure-types.hs (values, types, purity).
--
-- Cross-reference: LYAH "Input and Output" (chapter 9) expands on everything here
-- (files, `print`, `openFile`, randomness, etc.):
-- https://learnyouahaskell.github.io/input-and-output.html
-- Table of contents: https://learnyouahaskell.github.io/chapters.html
--
-- How to use this file:
--   • Read the comments for the mental model of IO.
--   • `runhaskell tutorial-02-io-effects.hs` runs main.
--   • In GHCi: `:load tutorial-02-io-effects.hs` then type `main` at the prompt.
--
-- ============================================================================

module Main (main) where

import Control.Monad (guard)
import Data.Char (toUpper)

-- ----------------------------------------------------------------------------
-- 1. The question Tutorial 01 left open
-- ----------------------------------------------------------------------------
--
-- Pure code is wonderful for reasoning, but programs must eventually:
--   • print to the screen
--   • read input, files, or the network
--   • get the current time, random numbers, etc.
--
-- All of these *depend on when* they run and *what the world looks like* — they
-- are *side effects* (or "effects" for short).
--
-- Haskell's answer: effects are values of type (IO a).

-- ----------------------------------------------------------------------------
-- 2. What (IO a) means (the model to teach first)
-- ----------------------------------------------------------------------------
--
-- Read (IO a) as: "a description of an action that, when executed by the
-- runtime, may do effectful things and then produce a value of type a."
--
-- Important:
--   • A value of type (IO a) is a first-class value — you can pass it around,
--     build it with functions, store it in a list (rare but legal).
--   • Evaluating a Haskell expression that mentions an IO value does not
--     magically run the world: the runtime runs main's chain of IO actions.
--
-- So Haskell stays referentially transparent at the level of values: the IO
-- recipe is a value; executing the recipe is what the system does when you
-- run the program.

-- ----------------------------------------------------------------------------
-- 3. main — the program's entry point
-- ----------------------------------------------------------------------------
--
-- The runtime looks for  main :: IO ().
--   • IO      — "this is an action description"
--   • ()      — "unit": no useful result, like void in C/Java; used for actions
--               that only have side effects (printing) and no meaningful return value

main :: IO ()
main = putStrLn "Hello — this string was sent to stdout when main ran."

-- ----------------------------------------------------------------------------
-- 4. Combining IO actions: do notation (sequencing)
-- ----------------------------------------------------------------------------
--
-- do blocks glue several IO steps in order. Each line that is an IO
-- action runs (conceptually) after the previous one finishes.

greet :: IO ()
greet = do
  putStrLn "What is your name?"
  -- getLine has type IO String: an action that returns a String when run.
  name <- getLine
  -- name is now a plain String (the result of that action), usable in the rest.
  putStrLn ("Hello, " ++ name ++ "!")

-- The <- arrow reads "run this action and bind its result to a name".
-- Without <-, a line like putStrLn "hi" is just an action you must sequence;
-- its result type is IO (), which we usually ignore.

-- ----------------------------------------------------------------------------
-- 5. return / pure — lifting a pure value into IO
-- ----------------------------------------------------------------------------
--
-- Historically `return` in do notation embeds a pure value in IO.
-- In modern Haskell, `pure` is preferred in new code; for IO they do the same.
--
--   pure 42 :: IO Int   — an action that does nothing effectful and yields 42

giveAnswer :: IO Int
giveAnswer = pure 42

reportAnswer :: IO ()
reportAnswer = do
  n <- giveAnswer
  putStrLn ("The answer is: " ++ show n)

-- ----------------------------------------------------------------------------
-- 6. One function returning IO (still not "running" until composed into main)
-- ----------------------------------------------------------------------------

askTwice :: IO (String, String)
askTwice = do
  putStrLn "First line:"
  a <- getLine
  putStrLn "Second line:"
  b <- getLine
  pure (a, b)

-- ----------------------------------------------------------------------------
-- LYAH — "Input and Output" (chapter 9): composing small IO programs
-- https://learnyouahaskell.github.io/input-and-output.html
-- ----------------------------------------------------------------------------
--
-- LYAH stresses that `do` is just sequencing; pure helpers stay pure.
-- `putStr` prints without a newline (LYAH contrasts it with `putStrLn`).
-- `print` is `putStrLn . show` — handy for anything with a `Show` instance.

reverseWords :: String -> String
reverseWords = unwords . map reverse . words

-- Read one line; print each word with letters reversed (LYAH walks through this
-- style of program piece by piece).

reverseLineOnce :: IO ()
reverseLineOnce = do
  line <- getLine
  putStrLn (reverseWords line)

-- Same spirit as LYAH's "forever / map toUpper" examples: loop until blank line.

shoutUntilBlank :: IO ()
shoutUntilBlank = do
  putStr "Type something (empty line to stop): "
  l <- getLine
  if null l
    then putStrLn "Bye!"
    else do
      putStrLn (map toUpper l)
      shoutUntilBlank

-- ----------------------------------------------------------------------------
-- 7. `guard` — keeping only successful effectful choices
-- ----------------------------------------------------------------------------
--
-- `guard` is a small helper for "continue only if this condition is true."
-- For lists, `guard False` means "no answers from this path"; `guard True`
-- means "keep going."
--
-- This is especially useful in list `do` notation, where a list means "many
-- possible answers":

smallEvenSquares :: [Int] -> [Int]
smallEvenSquares xs = do
  n <- xs
  guard (even n)
  let square = n * n
  guard (square < 50)
  pure square

-- Try in GHCi:
--
--   smallEvenSquares [1..10]
--     == [4,16,36]
--
-- Read it as:
--   • choose an n from xs
--   • abandon this choice unless n is even
--   • compute its square
--   • abandon this choice unless the square is less than 50
--   • return the surviving square
--
-- In IO, `guard` exists too, but it is less useful for beginners because failed
-- IO guards use the MonadFail machinery. For now, use `if ... then ... else ...`
-- when branching in IO, and use `guard` mainly for Maybe/list problems.

-- ----------------------------------------------------------------------------
-- 8. Broader context
-- ----------------------------------------------------------------------------
--
-- Under the hood, IO is a monad: >>= ("bind") sequences actions and allows
-- the next step to depend on the previous result. do is syntactic sugar for
-- >>= and >>.
--
-- Typeclass hierarchy (Functor → Applicative → Monad) makes IO composable with
-- the same tools as other "effect" types (Maybe, lists, etc.). That is usually
-- a second or third week topic — not required to use do and main on day one.
--
-- Also deferred: IORef, ST, exceptions, concurrency, and lazy I/O — all real,
-- but not needed for the first mental model. LYAH chapter 9 covers files,
-- bytestrings, exceptions, and the rest if you are interested.

-- ----------------------------------------------------------------------------
-- 9. Various options for main
-- ----------------------------------------------------------------------------
--
-- Uncomment ONE of the following lines as the definition of main
--
--   main = greet
--   main = reportAnswer
--   main = askTwice >>= \(a, b) -> putStrLn ("You said: " ++ a ++ " and " ++ b)
--   main = reverseLineOnce        -- type a sentence; words print reversed
--   main = shoutUntilBlank        -- LYAH-style loop until empty line
