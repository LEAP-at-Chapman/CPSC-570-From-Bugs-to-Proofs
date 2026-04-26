{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- ============================================================================
-- Tutorial 01 — Pure Haskell: types, data, and reasoning (first exposure)
-- ============================================================================
--
-- Cross-reference: *Learn You a Haskell for Great Good!* (LYAH), online at
-- https://learnyouahaskell.github.io/chapters.html
-- Sections below cite the matching LYAH chapter so students can read deeper.
--
-- In GHCi: `:load tutorial-01-pure-types.hs` then `:t someName` for inferred types.
--
-- LoVe (Logical Verification) demos 1–4 mirrored in Haskell:
--   `tutorial-love-demos-01-04.hs` (Lean files under `lean/.../LoVe/`).
--
-- ============================================================================

module Main (main) where

-- ----------------------------------------------------------------------------
-- 1. Values and types
-- ----------------------------------------------------------------------------
--
-- Every expression has a type. We can write types explicitly with `::`
-- (read as "has type").
--
--   42        :: Int          -- integer
--   3.14      :: Double       -- floating-point
--   True      :: Bool         -- boolean
--   'a'       :: Char         -- single character (note single quotes)
--   "hello"   :: String       -- string (list of Char; double quotes)
--
-- If you omit the type, Haskell infers it. In GHCi, `:t expression` shows
-- the inferred type.

anInt :: Int
anInt = 42

aBool :: Bool
aBool = True

-- ----------------------------------------------------------------------------
-- 2. Functions: the type is a contract
-- ----------------------------------------------------------------------------
--
-- A function type looks like  inputType -> outputType.
-- Multi-argument functions are really "functions returning functions" (currying):
--
--   add :: Int -> Int -> Int
--
-- means: given an Int, return a function that takes another Int and returns Int.
-- So `add 3` is a function still waiting for one more Int.

add :: Int -> Int -> Int
add x y = x + y

-- Partial application: `addThree = add 3` fixes the first argument.

addThree :: Int -> Int
addThree = add 3

-- ----------------------------------------------------------------------------
-- LYAH — "Starting Out" (chapter 2)
-- https://learnyouahaskell.github.io/starting-out.html
-- ----------------------------------------------------------------------------
--
-- Baby's first functions (LYAH style): same ideas as `doubleMe` / `doubleUs`.

doubleMe :: Int -> Int
doubleMe x = x + x

doubleUs :: Int -> Int -> Int
doubleUs x y = doubleMe x + doubleMe y

-- Texas ranges: `[1..5]` is `[1,2,3,4,5]`; `[2,4..20]` steps by 2.
-- List comprehensions: "take x from this list, such that …"

evensUpTo20 :: [Int]
evensUpTo20 = [x | x <- [1..20], x `mod` 2 == 0]

doubledLargeEnough :: [Int]
doubledLargeEnough = [x * 2 | x <- [1..10], x * 2 > 12]

-- ----------------------------------------------------------------------------
-- 3. Defining your own types with `data` ("algebraic data types")
-- ----------------------------------------------------------------------------
--
-- A type is a set of choices. `data` introduces a new type and its constructors
-- (ways to build a value of that type).
--
-- Example: a small closed set of colors. Each constructor is a *tag* with no
-- extra data inside.

data PrimaryColor = Red | Green | Blue
  deriving (Eq, Show)
-- `deriving (Eq, Show)` asks the compiler to generate equality and string
-- printing for free — fine for teaching; later you learn to write instances by hand.

-- Pattern matching: we *inspect* which constructor we have and branch.

describeColor :: PrimaryColor -> String
describeColor c = case c of
  Red   -> "warm"
  Green -> "vegetal"
  Blue  -> "cool"

-- ----------------------------------------------------------------------------
-- 4. Constructors can carry data ("sum" + "product" types)
-- ----------------------------------------------------------------------------
--
-- "Sum": several alternatives (This OR That).
-- "Product": one alternative carries several fields together (This AND those).

-- Either you know someone's age, or you don't.

data AgeInfo = KnownAge Int | AgeUnknown
  deriving (Eq, Show)

canVote :: AgeInfo -> Bool
canVote (KnownAge n) = n >= 18
canVote AgeUnknown   = False

-- ----------------------------------------------------------------------------
-- 4b. Natural numbers as an inductive type (Peano / unary style)
-- ----------------------------------------------------------------------------
--
-- Besides the built-in `Int` and `Integer`, we can define counting numbers with
-- two constructors only: "zero" and "successor of …". This is the same idea as
-- `inductive Nat` in Lean (see `tutorial-love-demos-01-04.hs` / LoVe Demo 2).
--
--   Z           — zero
--   S n         — one more than n
--
-- So the number 3 is `S (S (S Z))`. There is no built-in decimal syntax for
-- this type — you build values with constructors, or write conversion helpers.

data Peano = Z | S Peano
  deriving (Eq, Show)

-- Addition: recurse on the *right* summand (mirrors the usual Lean textbook def).

peanoAdd :: Peano -> Peano -> Peano
peanoAdd m Z = m
peanoAdd m (S n) = S (peanoAdd m n)

-- Multiplication: repeated addition on the right.

peanoMul :: Peano -> Peano -> Peano
peanoMul _ Z = Z
peanoMul m (S n) = peanoAdd m (peanoMul m n)

-- Handy for GHCi: how many `S` wrappers around `Z`?

peanoToInt :: Peano -> Int
peanoToInt Z = 0
peanoToInt (S n) = 1 + peanoToInt n

-- Example values (three = 3, five = 5 in Peano form):

threeP, fiveP :: Peano
threeP = S (S (S Z))
fiveP = S (S (S (S (S Z))))

-- ----------------------------------------------------------------------------
-- 5. Maybe and Either — modeling absence and failure in the type
-- ----------------------------------------------------------------------------
--
-- These are in the standard library; every Haskell programmer uses them daily.
--
--   Maybe a     = Nothing OR Just a            — "optional value"
--   Either e a  = Left e OR Right a            — "error e or success a"
--
-- Putting failure in the type forces callers to *handle* both cases.

safeDivide :: Int -> Int -> Maybe Double
safeDivide _ 0 = Nothing           -- division by zero: no sensible number
safeDivide x y = Just (fromIntegral x / fromIntegral y)

-- Either String Double could carry an error message in the Left case.

safeDivideVerbose :: Int -> Int -> Either String Double
safeDivideVerbose _ 0 = Left "division by zero"
safeDivideVerbose x y = Right (fromIntegral x / fromIntegral y)

-- ----------------------------------------------------------------------------
-- 6. Typeclasses — shared vocabulary for "things you can do"
-- ----------------------------------------------------------------------------
--
-- A typeclass is like an interface: types that support the same operations
-- can instance the class. You use typeclasses through constraints:
--
--   showIt :: Show a => a -> String
--
-- reads: "for any type a that has Show, we can turn a value into a String."

showIt :: Show a => a -> String
showIt x = show x

-- Common classes for beginners:
--
--   Eq     — equality (==, /=)
--   Ord    — ordering (<, >, compare, …)
--   Show   — convert to string for display (show)
--   Num    — numeric literals and +, *, etc. (several numeric types)
--
-- Do not confuse typeclasses with OOP "classes"; they are closer to Rust traits
-- or Java interfaces, but resolved at compile time (with some runtime support).

-- ----------------------------------------------------------------------------
-- LYAH — "Types and typeclasses" (chapter 3)
-- https://learnyouahaskell.github.io/types-and-typeclasses.html
-- ----------------------------------------------------------------------------
--
-- "Believe the type": `read` is polymorphic; without a use site GHC may not know
-- which type to parse into — in source we fix it with a type annotation.

fiveFromString :: Int
fiveFromString = read "5"

-- "Type variables": a function can be polymorphic in tuple components.
-- Compare LYAH's discussion of `fst` and type variables `a`, `b`.

firstOfPair :: (a, b) -> a
firstOfPair (x, _) = x

-- ----------------------------------------------------------------------------
-- 7. Purity and referential transparency (the heart of "functional Haskell")
-- ----------------------------------------------------------------------------
--
-- A pure function: same inputs always produce the same output, and it does not
-- secretly read globals, mutate memory, print, or talk to the network.
--
-- Why care?
--   • Easier to test and reason about.
--   • The type Int -> Int tells you a lot: no hidden dependencies on the world.
--
-- So where do printing, files, and random numbers live? Not "inside" arbitrary
-- pure functions — they live in IO, which Tutorial 02 explains.

pureIncrement :: Int -> Int
pureIncrement n = n + 1

-- ----------------------------------------------------------------------------
-- 8. Lists and recursion (tiny taste — lists are the bread and butter of teaching)
-- ----------------------------------------------------------------------------

sumInts :: [Int] -> Int
sumInts []       = 0           -- base case: empty list
sumInts (x : xs) = x + sumInts xs   -- head x, tail xs

-- ----------------------------------------------------------------------------
-- LYAH — "Syntax in functions" (chapter 4)
-- https://learnyouahaskell.github.io/syntax-in-functions.html
-- ----------------------------------------------------------------------------
--
-- Pattern matching (`lucky`), recursion (`factorial`), guards (`letterGrade`),
-- `where` (`initials`), `let` (`cylinder`), and `case` (`describeList`).

lucky :: Int -> String
lucky 7 = "LUCKY NUMBER SEVEN!"
lucky _ = "Sorry, you're out of luck, pal!"

factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- LYAH uses `error` for the empty case to mirror the book; production code
-- often returns `Maybe a` instead.

headLYAH :: [a] -> a
headLYAH []    = error "Whoops! No head for empty lists!"
headLYAH (x:_) = x

letterGrade :: Double -> String
letterGrade pct
  | pct < 0 || pct > 100 = "out of range"
  | pct >= 90            = "A"
  | pct >= 80            = "B"
  | pct >= 70            = "C"
  | pct >= 60            = "D"
  | otherwise            = "F"

cylinder :: Double -> Double -> Double
cylinder r h =
  let sideArea = 2 * pi * r * h
      topArea  = pi * r ^ 2
  in sideArea + 2 * topArea

initials :: String -> String -> String
initials firstname lastname = [f] ++ ". " ++ [l] ++ "."
  where
    (f:_) = firstname
    (l:_) = lastname

describeList :: Show a => [a] -> String
describeList xs =
  "The list is "
    ++ case xs of
      []      -> "empty."
      (x:[])  -> "a singleton list whose element is " ++ show x
      (_:_:_) -> "a longer list."

-- ----------------------------------------------------------------------------
-- LYAH — "Recursion" (chapter 5)
-- https://learnyouahaskell.github.io/recursion.html
-- ----------------------------------------------------------------------------

maximumLYAH :: Ord a => [a] -> a
maximumLYAH []    = error "maximum of empty list"
maximumLYAH [x]   = x
maximumLYAH (x:xs) = max x (maximumLYAH xs)

quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (x:xs) =
  let smaller = quicksort [a | a <- xs, a <= x]
      bigger  = quicksort [a | a <- xs, a > x]
  in smaller ++ [x] ++ bigger

-- ----------------------------------------------------------------------------
-- LYAH — "Higher order functions" (chapter 6)
-- https://learnyouahaskell.github.io/higher-order-functions.html
-- ----------------------------------------------------------------------------
--
-- These functions take *other functions* as arguments (or return them). On
-- lists, they are the bread and butter of functional style. For lists,
-- `map` is exactly `fmap` from the `Functor []` instance — same idea as in the
-- Functor section below, specialised to lists.
--
-- **map** — apply a function to every element; the list stays the same length.

lengthsOfWords :: [String] -> [Int]
lengthsOfWords = map length

sumOfMappedIncrements :: [Int] -> Int
sumOfMappedIncrements xs = sum (map (+ 1) xs)

-- **filter** — keep only elements for which the predicate is True.

onlyPositives :: [Int] -> [Int]
onlyPositives = filter (> 0)

-- **foldr** — reduce a list with a binary operator and a starting value, from
-- the right.  `foldr f z [a,b,c]  ==  f a (f b (f c z))`.  (LYAH also covers
-- folds with `foldl` / strict `foldl'`; `sum` and `product` are predefined folds.)

sumWithFoldr :: [Int] -> Int
sumWithFoldr = foldr (+) 0

productWithFoldr :: [Int] -> Int
productWithFoldr = foldr (*) 1

-- **concatMap** (sometimes written `>>=` for lists) — map each element to a
-- *list*, then concatenate.  Generalises "map then squash".

stutterEach :: [a] -> [a]
stutterEach = concatMap (\x -> [x, x])

-- **zipWith** — walk two lists in parallel, combining elements with a binary
-- function. Stops when the shorter list ends.

pairwiseSums :: [Int] -> [Int] -> [Int]
pairwiseSums = zipWith (+)

-- **takeWhile** / **dropWhile** — split by a predicate without manual recursion.

positivePrefix :: [Int] -> [Int]
positivePrefix = takeWhile (> 0)

-- **scanl** — like `foldl`, but return the accumulator at every step (running
-- totals, etc.).  First element is the initial seed.

runningSums :: [Int] -> [Int]
runningSums = scanl (+) 0

-- **Function composition** — `(.)` pipes output to input: `(f . g) x == f (g x)`.
-- Low precedence application operator **$** is useful to drop parentheses:
-- `sum (map (*2) xs)` can be written `sum $ map (*2) xs`.

doubleThenNegateAll :: [Int] -> [Int]
doubleThenNegateAll = map negate . map (* 2)

sumOfDoubled :: [Int] -> Int
sumOfDoubled = sum . map (* 2)

-- **iterate** + **take** — build infinite lists lazily, then cut them (LYAH style).

powersOfTwoUpTo :: Int -> [Int]
powersOfTwoUpTo n = take n (iterate (* 2) 1)

-- **replicate** — list of the same value repeated n times.

threeZeros :: [Int]
threeZeros = replicate 3 0

-- ----------------------------------------------------------------------------
-- LYAH — "Making our own types and typeclasses" (chapter 8)
-- https://learnyouahaskell.github.io/making-our-own-types-and-typeclasses.html
-- ----------------------------------------------------------------------------
--
-- LYAH builds `Shape` with `Point` for positions; `Circle` holds a centre
-- point and radius, `Rectangle` holds two corner points.

data Point = Point Float Float
  deriving (Show)

data Shape = Circle Point Float | Rectangle Point Point
  deriving (Show)

surface :: Shape -> Float
surface (Circle _ r) = pi * r ^ 2
surface (Rectangle (Point x1 y1) (Point x2 y2)) =
  abs (x2 - x1) * abs (y2 - y1)

aCircle :: Shape
aCircle = Circle (Point 10 20) 5

aRect :: Shape
aRect = Rectangle (Point 50 230) (Point 60 90)


-- ----------------------------------------------------------------------------
-- Functor and Applicative
-- ----------------------------------------------------------------------------
--
-- These typeclasses generalize "mapping" and "applying" when values sit inside
-- a *context* (`Maybe` for partiality, `[]` for nondeterminism, `IO` for side
-- effects in Tutorial 02). Deeper tour: LYAH ch. 11
-- https://learnyouahaskell.github.io/functors-applicative-functors-and-monoids.html
--
-- **Functor** — you can transform the inner value without changing the shape of
-- the context. The class has one essential operation:
--
--   fmap :: Functor f => (a -> b) -> f a -> f b
--
-- Laws (intuition): mapping `id` does nothing; mapping (f . g) equals mapping g
-- then mapping f. For lists, `fmap` is `map`.

doubleInsideMaybe :: Maybe Int -> Maybe Int
doubleInsideMaybe = fmap (* 2)

negateInsideList :: [Int] -> [Int]
negateInsideList = fmap negate

-- The infix synonym for `fmap` is `<$>` (mnemonic: "functor apply").

incrementInsideJust :: Maybe Int
incrementInsideJust = (+ 1) <$> Just 41

-- **Applicative** — when the function itself is inside the context, not just
-- the argument, `fmap` alone is not enough. Applicative adds:
--
--   pure  :: Applicative f => a -> f a
--   (<*>) :: Applicative f => f (a -> b) -> f a -> f b
--
-- Read `pure` as "put a plain value into the context with no extra effect".
-- Read `<*>` as "apply" (left-to-right): combine two wrapped values using a
-- wrapped function. (Historical name: "tie fighter".)

productInsideMaybes :: Maybe Int
productInsideMaybes = pure (*) <*> Just 3 <*> Just 5

-- This name is a *finished value* (`Maybe Int`), not a function. In GHCi use
-- `productInsideMaybes` alone — not `productInsideMaybes 0` (that would try to
-- apply a `Maybe Int` like a function and GHC complains).

productOfJusts :: Int -> Int -> Maybe Int
productOfJusts x y = pure (*) <*> Just x <*> Just y

-- If any operand is `Nothing`, the whole chain is `Nothing` — the `Maybe`
-- applicative short-circuits on failure.

productWithMissing :: Maybe Int
productWithMissing = pure (*) <*> Nothing <*> Just 5

-- List instance: `<*>` combines every function with every value (Cartesian
-- product style). This is where list comprehensions and "nondeterministic"
-- readings of lists come from.

allPairSums :: [Int]
allPairSums = pure (+) <*> [1, 2] <*> [10, 20]

-- `liftA2` bundles a binary pure function and lifts it into the applicative
-- (same idea as `pure g <*> xa <*> yb`, but easier to read for two arguments).

sumMaybes :: Maybe Int -> Maybe Int -> Maybe Int
sumMaybes = liftA2 (+)

justEight :: Maybe Int
justEight = sumMaybes (Just 3) (Just 5)

nothingFromSum :: Maybe Int
nothingFromSum = sumMaybes Nothing (Just 5)

-- Building a pair inside `Maybe`: `fmap` / `<$>` lifts the first argument to
-- `Maybe (b -> (a, b))`, then `<*>` supplies the second.

justPair :: Maybe (Int, Char)
justPair = (,) <$> Just 7 <*> Just 'z'

-- Bridge to Tutorial 02: `IO` is also a `Functor` and an `Applicative`, so
-- expressions like `length <$> getLine` make sense once you know `IO` — they
-- describe "read a line, then apply `length` to the result when the action runs".


-- ----------------------------------------------------------------------------
-- Entry point (keeps this file a valid Main module for runhaskell / GHCi)
-- ----------------------------------------------------------------------------
--
-- We use a trivial IO action here so the file compiles. The meaning of IO
-- is the subject of Tutorial 02.

main :: IO ()
main = putStrLn "Tutorial 01: read the comments; try :t in GHCi on the bindings above."
