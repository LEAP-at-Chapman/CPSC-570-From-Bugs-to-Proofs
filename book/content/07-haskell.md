# Effectful Programming in Haskell

```{note}
**Chapter roles (Spring 2026)**  
Author: Kaye Galang · Reviewer: Anela Quiroz  
See [Chapter assignments](0-chapter-assignments.md).
```

This chapter introduces **Haskell** with emphasis on types that track effects
(for example monads and `IO`) and equational reasoning. We will see how
Haskell's strict separation between pure and effectful code is not merely a
stylistic choice — it is what makes large-scale equational reasoning and
machine-assisted verification practical.

## A Brief History of Haskell

Haskell was born out of a recognition in the late 1980s that the functional
programming research community had fragmented across a dozen incompatible lazy
languages. In 1987, at the Conference on Functional Programming Languages and
Computer Architecture (FPCA), a committee was formed to design a single,
open standard for a lazy, purely functional language. The first version of the
language, **Haskell 1.0**, was published in 1990, named after the logician
Haskell Curry, whose work on combinatory logic underlies much of functional
programming theory.

The language evolved through several revisions over the following decade.
**Haskell 98** became the first stable, widely-adopted standard and is still
the baseline that many textbooks target. **Haskell 2010** followed, cleaning
up a handful of inconsistencies and adding several widely-used extensions to
the standard.

The **Glasgow Haskell Compiler (GHC)**, developed at the University of Glasgow
and now maintained by the open-source community, has been the dominant
implementation since the early 1990s and is the vehicle through which most
language innovation happens. GHC extensions — opt-in language features enabled
with a pragma — have driven research in type-level programming, generic
programming, and verified software that would have been impossible within the
original standard.

Today Haskell continues to evolve. The GHC release cadence is roughly twice a
year, and the [GHC Proposals](https://github.com/ghc-proposals/ghc-proposals)
process provides a transparent, community-driven path for new language features.

## Goals

- Relate pure functional programming to verification.
- Use a concise example to illustrate effects and monads.
- Explore the `Maybe` and `Either` monads as a further aspect.
- Link to GHC documentation, *Learn You a Haskell*, and modern Haskell tooling.

---

## 1  Pure Functions and Equational Reasoning

A **pure function** has two properties:

1. Its output depends only on its inputs — no hidden state, no globals.
2. It has no **side effects**: it does not read from a file, print to the
   terminal, modify a mutable variable, or throw an exception that alters
   program state.

In mathematics, you can freely substitute equals for equals:
if $f(x) = x + 1$ and $x = 3$, then $f(x) = f(3) = 4$.
This is called **equational reasoning** and it is completely safe because
$f$ does nothing except compute a value.

In an imperative language this substitution is *not* always safe:

```python
# Python — side-effecting function; substitution can break meaning
count = 0
def increment():
    global count
    count += 1
    return count

x = increment()   # x = 1, count = 1
y = increment()   # y = 2, count = 2
# x ≠ y even though both are "increment()"
```

Haskell makes purity the *default*. Every top-level definition in Haskell
is a pure expression unless its type explicitly says otherwise. This
default unlocks three verification superpowers:

| Benefit | Explanation |
|---|---|
| **Referential transparency** | Any sub-expression may be replaced by its value without changing program meaning. |
| **Equational proofs** | You can prove properties of code by algebraic substitution, exactly like a math proof. |
| **Testing** | Pure functions are trivially unit-tested: same input always yields same output. |

---

## 2  A First Look at Haskell

### 2.1  Running Haskell

The standard compiler is **GHC** (Glasgow Haskell Compiler). The modern way
to install it is through [GHCup](https://www.haskell.org/ghcup/), a toolchain
manager analogous to `rustup`:

```bash
# Install GHCup, GHC, Cabal, and Stack in one step
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

For a quick scratchpad, use **GHCi**, the interactive REPL:

```bash
ghci
```

```
GHCi, version 9.8.2: https://www.haskell.org/ghc/  :? for help
ghci> 2 + 2
4
ghci> :type "hello"
"hello" :: String
```

### 2.2  Types and Type Signatures

Every Haskell expression has a type, inferred automatically by GHC. You can
annotate types explicitly with `::`:

```haskell
-- | Double an integer.
double :: Int -> Int
double n = n * 2

-- | Add two integers.
add :: Int -> Int -> Int
add x y = x + y
```

```{note}
The `->` in a type is *right-associative*, so `Int -> Int -> Int` is the
same as `Int -> (Int -> Int)`. This means `add` is a function that takes one
`Int` and returns *another function* waiting for the second `Int`.
This is called **currying** and it underlies Haskell's elegant
partial-application style.
```

You can verify types in GHCi:

```
ghci> :type double
double :: Int -> Int
ghci> :type add 3
add 3 :: Int -> Int
```

### 2.3  Pattern Matching and Recursion

Haskell encourages defining functions by *cases* using pattern matching:

```haskell
-- | Factorial, defined by pattern matching.
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)
```

GHC checks that patterns are *exhaustive* — covering every possible input —
which prevents a whole class of runtime crashes common in other languages.

---

## 3  The Problem of Effects

Pure functions are great for reasoning, but real programs must interact
with the world: read files, accept user input, write to a database, send
network requests. These are **effects** — observable interactions with
state or the environment beyond the function's return value.

Haskell's answer is to make effects *visible in the type*. A function that
can perform I/O is given a return type wrapped in `IO`:

```haskell
-- Pure — type says nothing about the outside world
square :: Int -> Int
square x = x * x

-- Effectful — the IO wrapper tells the reader (and GHC) this touches the world
greet :: IO ()
greet = putStrLn "Hello, world!"
```

The type `IO ()` is read: "an I/O action that produces a value of type `()`
(unit, like `void` in C)". The type `IO String` would be an action that
produces a `String` after performing some I/O.

```{warning}
You cannot accidentally call a pure function in a way that causes I/O,
nor can you extract a value from `IO` and use it in a pure context without
acknowledging the boundary. GHC *enforces* this at compile time.
```

This boundary is the key insight: **purity is the default; effects are
opt-in, and opting in is visible in every type signature along the call
chain**.

---

## 4  Monads — Sequencing Effectful Computations

### 4.1  Motivation

Suppose you want to chain two I/O actions: first read a line of input,
then print a personalised greeting. In pure code you can just compose
functions. With `IO` values you need a way to *sequence* them —
"do this action, then, using whatever it produced, do the next action."

This sequencing pattern is captured by the `Monad` type class. The two
essential operations are:

```{note}
**Monads and category theory.** The word *monad* comes from category theory,
where a monad is a particular kind of endofunctor equipped with two natural
transformations satisfying coherence laws. The connection between this abstract
structure and *notions of computation* — partiality, state, exceptions, I/O —
was made precise by Eugenio Moggi in a landmark 1991 paper, *Notions of
Computation and Monads* {cite}`moggi1991`. Philip Wadler subsequently showed
how Moggi's categorical monads could be used directly as a programming
pattern in Haskell. You do not need to know category theory to use monads
effectively, but the categorical origin explains why the three monad laws
(Section 4.3) feel like abstract algebra — they are.
```

| Operation | Type | Meaning |
|---|---|---|
| `return` (or `pure`) | `a -> m a` | Wrap a pure value inside the monad. |
| `>>=` ("bind") | `m a -> (a -> m b) -> m b` | Run an action; pass its result to a function that produces the next action. |

For `IO` specifically:

```haskell
-- Manually sequenced with >>=
greetUser :: IO ()
greetUser =
  putStr "Enter your name: " >>= \_ ->
  getLine >>= \name ->
  putStrLn ("Hello, " ++ name ++ "!")
```

### 4.2  do-Notation

Writing `>>=` chains by hand gets unwieldy. Haskell provides **do-notation**
as syntactic sugar that looks like imperative code but desugars to `>>=`:

```haskell
-- Same function, written with do-notation
greetUser :: IO ()
greetUser = do
  putStr "Enter your name: "
  name <- getLine                       -- bind: extract the String from IO String
  putStrLn ("Hello, " ++ name ++ "!")
```

The `<-` arrow in do-notation corresponds exactly to the `\name ->` lambda
in the bind chain. Crucially, this is still pure Haskell — the do-block
*builds a description of a computation* that the runtime will execute.
Nothing is executed until `main` (the program entry point) runs it.

```haskell
main :: IO ()
main = greetUser
```

### 4.3  The Monad Laws

Every instance of `Monad` must satisfy three algebraic laws, which are
the formal basis for equational reasoning about monadic code:

```
-- Left identity:  return a >>= f   ≡   f a
-- Right identity: m >>= return     ≡   m
-- Associativity:  (m >>= f) >>= g  ≡   m >>= (\x -> f x >>= g)
```

These laws guarantee that `>>=` behaves like sequential composition: you
can refactor a chain of monadic actions — extracting sub-chains into named
helpers, or inlining them — without changing the program's meaning. This
is equational reasoning applied to effectful code.

---

## 5  Verified Error Handling: `Maybe` and `Either`

One of Haskell's most practically valuable monads is `Maybe`, which
encodes *optional* values without null pointers.

### 5.1  The `Maybe` Type

```haskell
data Maybe a = Nothing | Just a
```

A value of type `Maybe Int` is either `Nothing` (absence of a value) or
`Just 42` (a present value). There is no `null` — the type itself forces
you to handle both cases.

```haskell
-- | Safe integer division: returns Nothing on divide-by-zero.
safeDiv :: Int -> Int -> Maybe Int
safeDiv _ 0 = Nothing
safeDiv x y = Just (x `div` y)
```

```
ghci> safeDiv 10 2
Just 5
ghci> safeDiv 10 0
Nothing
```

### 5.2  Chaining with the `Maybe` Monad

The `Maybe` monad propagates `Nothing` automatically through a chain of
computations — the monadic equivalent of short-circuit evaluation:

```haskell
-- | Look up a value, double it, then halve it — failing safely at any step.
compute :: Int -> Int -> Int -> Maybe Int
compute x y z = do
  a <- safeDiv x y   -- Nothing if y = 0
  b <- safeDiv a z   -- Nothing if z = 0
  return (a + b)
```

```
ghci> compute 100 5 2
Just 30
ghci> compute 100 0 2
Nothing
ghci> compute 100 5 0
Nothing
```

Without `Maybe`, each division would need its own `if` check. With the
monad, the failure plumbing is handled automatically — and, crucially,
it is *impossible* to forget. A pure `Int -> Int -> Int` function *cannot*
represent failure; you must choose a richer type.

### 5.3  `Either` for Structured Errors

`Maybe` discards the reason for failure. `Either` preserves it:

```haskell
data Either e a = Left e | Right a
```

By convention, `Left` carries an error value and `Right` carries a success
value. (Remember it as: "right is right.")

```haskell
data DivError = DivideByZero | NegativeInput deriving (Show)

safeDiv' :: Int -> Int -> Either DivError Int
safeDiv' _ 0 = Left DivideByZero
safeDiv' x y
  | x < 0 || y < 0 = Left NegativeInput
  | otherwise       = Right (x `div` y)
```

```
ghci> safeDiv' 10 2
Right 5
ghci> safeDiv' 10 0
Left DivideByZero
ghci> safeDiv' (-4) 2
Left NegativeInput
```

The `Either DivError` monad sequences these checks exactly like `Maybe`
does, but a caller receiving a `Left` always knows *why* the computation
failed — this information is encoded in the type and cannot be lost.

```{tip}
In production Haskell, libraries like
[`transformers`](https://hackage.haskell.org/package/transformers) and
[`mtl`](https://hackage.haskell.org/package/mtl) let you stack multiple
monadic effects (e.g., I/O *and* error-handling) using **monad transformer
stacks**, generalising the pattern seen with `IO`, `Maybe`, and `Either`.
```

---

## 6  Equational Reasoning in Practice

Let us verify a small property of our `safeDiv` function using equational
reasoning — the same style used in formal verification tools like
[Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/) and
[Agda](https://agda.readthedocs.io/).

**Claim:** `safeDiv x 1 = Just x` for all `Int` `x`.

**Proof:**

```
safeDiv x 1
  = Just (x `div` 1)    -- by the second equation of safeDiv (1 ≠ 0)
  = Just x              -- by the arithmetic law  x `div` 1 = x
```

Each step substitutes equals for equals. This works because `safeDiv` is
**pure**: there is no hidden state that could make the second call behave
differently from the first, so the substitution is always valid.

Compare this to proving a property of an imperative function that mutates
a counter — you would need to reason about the entire machine state at
every step, an exponentially harder task.

---

## 7  Putting It Together — A Small Complete Program

Below is a self-contained program that exercises `IO`, do-notation,
`Maybe`, and pattern matching together:

```haskell
module Main where

import Text.Read (readMaybe)

-- | Safe division, as defined earlier.
safeDiv :: Int -> Int -> Maybe Int
safeDiv _ 0 = Nothing
safeDiv x y = Just (x `div` y)

-- | Prompt the user for an Int, retrying on bad input.
readInt :: String -> IO Int
readInt prompt = do
  putStr prompt
  line <- getLine
  case readMaybe line of
    Just n  -> return n
    Nothing -> do
      putStrLn "Not a valid integer. Please try again."
      readInt prompt

main :: IO ()
main = do
  x <- readInt "Numerator:   "
  y <- readInt "Denominator: "
  case safeDiv x y of
    Nothing -> putStrLn "Error: division by zero."
    Just q  -> putStrLn ("Result: " ++ show q)
```

Notice the separation of concerns enforced by the type system:

- `safeDiv` is **pure** (`Maybe Int`, no `IO`) — it can be reasoned about
  and tested without any runtime.
- `readInt` is **effectful** (`IO Int`) — it interacts with the terminal.
- `main` is the single point that connects them.

This separation is not a convention — GHC will reject any attempt to call
`putStrLn` from inside `safeDiv` or to embed a pure function's result in
an `IO` context without an explicit `return`.

---

## 8  Haskell in Industry

Haskell's reputation as an "academic" language understates its real-world
footprint. A wide range of industries have deployed Haskell in production,
often precisely because its type system and purity guarantees reduce the cost
of correctness in high-stakes domains. A few representative examples:

**Finance and trading.** Standard Chartered has a large group using Haskell
across its wholesale banking business. Barclays Capital's quantitative
analytics team embedded a functional DSL in Haskell to specify exotic equity
derivatives. Credit Suisse, Deutsche Bank, and several algorithmic trading
firms including Tsuru Capital and Starling Software have used Haskell for
pricing, risk modelling, and automated trading systems.

**Defence and security.** Galois, Inc. has used Haskell for over a decade to
build high-assurance software for US government clients in cryptography and
information assurance. BAE Systems used Haskell extensively in their SAFE
project to build compilers, simulators, and EDSLs. MITRE has applied it to
cryptographic protocol analysis.

**Hardware design.** Bluespec used Haskell as the implementation language for
chip design tooling that borrowed ideas from term-rewriting systems. Intel
Research built a Haskell compiler as part of research on multicore parallelism.

**Infrastructure and tooling.** Microsoft's production serialisation system,
Bond, is implemented in Haskell and is used broadly in high-scale internal
services. Facebook built lex-pass, a tool for programmatically manipulating
PHP codebases, in Haskell. NVIDIA uses Haskell for in-house tooling.

**Startups and web.** Hasura's BaaS platform, Betterteam's recruitment
backend, and several RSS readers and e-commerce platforms are built entirely or
substantially in Haskell. Serokell is a software company that specialises in
Haskell for blockchain platforms, DSLs, and high-volume APIs.

A continuously maintained list of companies using Haskell commercially is
available at the [Haskell in Industry](https://wiki.haskell.org/Haskell_in_industry)
wiki page.

---

## 9  Modern Haskell Tooling

| Tool | Purpose | Install |
|---|---|---|
| [GHCup](https://www.haskell.org/ghcup/) | Toolchain manager (GHC, Cabal, Stack, HLS) | `curl … | sh` |
| [GHCi](https://downloads.haskell.org/ghc/latest/docs/users_guide/ghci.html) | Interactive REPL, bundled with GHC | ships with GHC |
| [Cabal](https://cabal.readthedocs.io/) | Build tool and package manager | via GHCup |
| [Stack](https://docs.haskellstack.org/) | Reproducible build tool with curated Stackage snapshots | via GHCup |
| [HLS](https://haskell-language-server.readthedocs.io/) | Haskell Language Server (IDE integration) | via GHCup |
| [Hackage](https://hackage.haskell.org/) | Central package repository | browser / Cabal |
| [Hoogle](https://hoogle.haskell.org/) | Search by type signature or name | browser |

```{tip}
**Hoogle** is uniquely powerful: you can search for a function by its type
signature. For example, searching `(a -> b) -> [a] -> [b]` immediately
surfaces `map`. This workflow — think about what type a function should
have, then search for it — reflects how experienced Haskell programmers
navigate the ecosystem.
```

---

## 10  Beyond `mtl`: Extensible Effects

Monad transformer stacks (`transformers` / `mtl`) are the traditional solution
for combining effects, but they come with known drawbacks: the order of
transformers in a stack matters, and adding a new effect type requires touching
every layer. A newer family of libraries addresses this with **extensible
effect** systems, where effects are described as an open, row-polymorphic set
that can be extended without rebuilding the stack:

| Library | Key idea | Hackage |
|---|---|---|
| [`effectful`](https://hackage.haskell.org/package/effectful) | Fast, ST-based carrier; designed for drop-in `mtl` migration | `effectful` |
| [`cleff`](https://hackage.haskell.org/package/cleff) | Lightweight, polysemy-inspired; good for learning | `cleff` |
| [`fused-effects`](https://hackage.haskell.org/package/fused-effects) | Algebraic effects via type-class fusion; zero-cost abstraction goal | `fused-effects` |

All three allow you to write code that is polymorphic over the effect set —
a function that only needs logging and state does not need to mention I/O in
its type — and each provides a way to interpret effects at the call site rather
than fixing the interpreter globally. The design space is active and evolving;
`effectful` is currently the most widely recommended starting point for new
production code.

---

## 11  Summary

| Concept | Key Idea |
|---|---|
| **Pure function** | Output depends only on inputs; no side effects. |
| **Equational reasoning** | Pure code can be proven correct by algebraic substitution. |
| **`IO` type** | Marks effectful computations; enforced at compile time by GHC. |
| **Monad** | Abstraction for sequencing computations, especially effectful ones. |
| **do-notation** | Syntactic sugar over `>>=`; desugars to pure functional code. |
| **`Maybe` / `Either`** | Monads for safe, composable error handling without null or exceptions. |

Haskell's design forces a clear boundary between pure logic and effectful
interaction. This boundary is what makes equational reasoning — and
ultimately formal verification — tractable: the pure core of a program can
be proved correct in isolation, and the effectful shell can be kept thin
and auditable.

---

## References and Further Reading

- Lipovača, M. *[Learn You a Haskell for Great Good!](http://learnyouahaskell.com/)* — a
  friendly, illustrated introduction to Haskell. Freely available online.
- GHC Team. *[GHC User's Guide](https://downloads.haskell.org/ghc/latest/docs/users_guide/)* — authoritative reference for the compiler and language extensions.
- GHC Team. *[GHCi Reference](https://downloads.haskell.org/ghc/latest/docs/users_guide/ghci.html)* — interactive environment documentation.
- Marlow, S. *[Parallel and Concurrent Programming in Haskell](https://simonmar.github.io/pages/pcph.html)* — extends the monad story to concurrency.
- Moggi, E. (1991). *[Notions of Computation and Monads](https://www.cs.cmu.edu/~crary/819-f09/Moggi91.pdf)*. Information and Computation, 93(1), 55–92. — the categorical paper that established monads as a model for computational effects.
- Vazou, N. et al. *[Refinement Types for Haskell (Liquid Haskell)](https://ucsd-progsys.github.io/liquidhaskell/)* — connects the purity of Haskell to machine-checked proofs.
- Hackage. *[`transformers` package](https://hackage.haskell.org/package/transformers)*, *[`mtl` package](https://hackage.haskell.org/package/mtl)*, *[`effectful` package](https://hackage.haskell.org/package/effectful)*, *[`cleff` package](https://hackage.haskell.org/package/cleff)*, *[`fused-effects` package](https://hackage.haskell.org/package/fused-effects)* — effect libraries ranging from classic transformer stacks to modern extensible effect systems.
- HaskellWiki. *[Haskell in Industry](https://wiki.haskell.org/Haskell_in_industry)* — a community-maintained list of companies using Haskell commercially.