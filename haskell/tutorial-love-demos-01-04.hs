{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- ============================================================================
-- Haskell mirror — LoVe (Logical Verification) demos 1–4
-- ============================================================================
--
-- This file restates *programs* from the Lean 4 LoVe course in Haskell so you
-- can compare syntax and typing with the Hitchhiker / LoVe track in this repo:
--
--   lean/logical_verification_2025/lean/LoVe/LoVe01_TypesAndTerms_Demo.lean
--   lean/logical_verification_2025/lean/LoVe/LoVe02_ProgramsAndTheorems_Demo.lean
--   lean/logical_verification_2025/lean/LoVe/LoVe03_BackwardProofs_Demo.lean
--   lean/logical_verification_2025/lean/LoVe/LoVe04_ForwardProofs_Demo.lean
--
-- Demos 3–4 are mostly *proof tactics*; here they appear as the corresponding
-- functional programs (Curry–Howard), plus comments pointing at the Lean files.
--
-- LoVe is © Anne Baanen, Alexander Bentkamp, Jasmin Blanchette, Xavier Généreux,
-- Johannes Hölzl, and Jannis Limperg — see `LICENSE.txt` under `lean/.../LoVe/`.
--
-- ============================================================================

module Main (main) where

-- ----------------------------------------------------------------------------
-- LoVe Demo 1 — types, terms, currying (see LoVe01_TypesAndTerms_Demo.lean)
-- ----------------------------------------------------------------------------
--
-- Polymorphic combinators also appear in LoVe Exercise 1 (same chapter).

i :: a -> a
i x = x

k :: a -> b -> a
k x _ = x

c :: (a -> b -> c) -> b -> a -> c
c f y x = f x y

projFst :: a -> a -> a
projFst x _ = x

projSnd :: a -> a -> a
projSnd _ y = y

-- LoVe Exercise 1 `someNonsense`: the fourth argument supplies the `b` needed
-- by `f x : b -> c`.

someNonsense :: (a -> b -> c) -> a -> (a -> c) -> b -> c
someNonsense f x _g y = f x y

-- End of LoVe01_Demo: `someFunOfType` inhabitant exercise.

someFunOfType :: (a -> b -> c) -> ((b -> a) -> b) -> a -> c
someFunOfType f g a = f a (g (\_ -> a))

-- ----------------------------------------------------------------------------
-- LoVe Demo 2 — inductive types and programs (LoVe02_ProgramsAndTheorems_Demo)
-- ----------------------------------------------------------------------------

data Nat = Zero | Succ Nat
  deriving (Eq, Show)

addNat :: Nat -> Nat -> Nat
addNat m Zero = m
addNat m (Succ n) = Succ (addNat m n)

mulNat :: Nat -> Nat -> Nat
mulNat _ Zero = Zero
mulNat m (Succ n) = addNat m (mulNat m n)

powerNat :: Nat -> Nat -> Nat
powerNat _ Zero = Succ Zero
powerNat m (Succ n) = mulNat m (powerNat m n)

fibNat :: Nat -> Nat
fibNat Zero = Zero
fibNat (Succ Zero) = Succ Zero
fibNat (Succ (Succ n)) = addNat (fibNat (Succ n)) (fibNat n)

iter :: a -> (a -> a) -> Nat -> a
iter z _ Zero = z
iter z f (Succ n) = f (iter z f n)

powerIter :: Nat -> Nat -> Nat
powerIter m n = iter (Succ Zero) (mulNat m) n

appendList :: [a] -> [a] -> [a]
appendList [] ys = ys
appendList (x : xs) ys = x : appendList xs ys

reverseList :: [a] -> [a]
reverseList [] = []
reverseList (x : xs) = appendList (reverseList xs) [x]

-- Arithmetic expressions and `eval` (ℤ rendered as `Integer` here).

data AExp
  = Num Integer
  | Var String
  | Add AExp AExp
  | Sub AExp AExp
  | Mul AExp AExp
  | Div AExp AExp
  deriving (Show)

evalA :: (String -> Integer) -> AExp -> Integer
evalA _ (Num n) = n
evalA env (Var x) = env x
evalA env (Add e1 e2) = evalA env e1 + evalA env e2
evalA env (Sub e1 e2) = evalA env e1 - evalA env e2
evalA env (Mul e1 e2) = evalA env e1 * evalA env e2
evalA env (Div e1 e2) = evalA env e1 `div` evalA env e2

loveDemoEnv :: String -> Integer
loveDemoEnv "x" = 3
loveDemoEnv "y" = 17
loveDemoEnv _ = 201

-- LoVe02 uses `sorry` for theorems about `add`, `mul`, `reverse` — in Haskell
-- we do not prove them here; see the Lean file for `theorem add_comm …`.

-- ----------------------------------------------------------------------------
-- LoVe Exercise 2 — Q1 predecessor (unary Nat version of `pred`)
-- ----------------------------------------------------------------------------

predNat :: Nat -> Nat
predNat Zero = Zero
predNat (Succ n) = n

-- ----------------------------------------------------------------------------
-- LoVe Exercise 2 — Q2 expression simplification (extends the Lean template)
-- ----------------------------------------------------------------------------

simplifyAExp :: AExp -> AExp
simplifyAExp (Add (Num 0) e2) = simplifyAExp e2
simplifyAExp (Add e1 (Num 0)) = simplifyAExp e1
simplifyAExp (Sub e1 (Num 0)) = simplifyAExp e1
simplifyAExp (Mul (Num 0) _) = Num 0
simplifyAExp (Mul _ (Num 0)) = Num 0
simplifyAExp (Mul (Num 1) e2) = simplifyAExp e2
simplifyAExp (Mul e1 (Num 1)) = simplifyAExp e1
simplifyAExp (Div e1 (Num 1)) = simplifyAExp e1
simplifyAExp (Num n) = Num n
simplifyAExp (Var x) = Var x
simplifyAExp (Add e1 e2) = Add (simplifyAExp e1) (simplifyAExp e2)
simplifyAExp (Sub e1 e2) = Sub (simplifyAExp e1) (simplifyAExp e2)
simplifyAExp (Mul e1 e2) = Mul (simplifyAExp e1) (simplifyAExp e2)
simplifyAExp (Div e1 e2) = Div (simplifyAExp e1) (simplifyAExp e2)

-- ----------------------------------------------------------------------------
-- LoVe Demo 3 — backward proofs as programs (LoVe03_BackwardProofs_Demo.lean)
-- ----------------------------------------------------------------------------
--
-- Propositions-as-types: `a → b → a` is inhabited by `const`, `a ∧ b → b ∧ a`
-- by swapping a pair, composition is `(.)`.

double :: Integer -> Integer
double n = n + n

propFst :: a -> b -> a
propFst ha _hb = ha

propComp :: (a -> b) -> (b -> c) -> a -> c
propComp ab bc = bc . ab

andSwap :: (a, b) -> (b, a)
andSwap (x, y) = (y, x)

-- ----------------------------------------------------------------------------
-- LoVe Demo 4 — forward style / structured reasoning (LoVe04_ForwardProofs_Demo)
-- ----------------------------------------------------------------------------

modusPonens :: (a -> b) -> a -> b
modusPonens hab ha = hab ha

-- `∃n, double n = n` — witness `n = 0` (same as `Nat_exists_double_iden`).

existsDoubleIdentity :: (Integer, Bool)
existsDoubleIdentity = (0, double 0 == 0)

-- `beast_666` / `Forall.one_point` are proof exercises in Lean; in Haskell the
-- analogue is rewriting under equality, which is not built into this file.

-- ----------------------------------------------------------------------------
-- Problems (pencil / separate file — from LoVe exercise sheets 1–2, 3–4)
-- ----------------------------------------------------------------------------
--
-- **LoVe Exercise 1 (Types and Terms)** — `LoVe01_TypesAndTerms_ExerciseSheet.lean`
--   1. Re-derive `C`, `projFst`, `projSnd`, `someNonsense` without peeking above.
--   2. Draw the typing derivation for your `C` (paper or comment).
--
-- **LoVe Exercise 2 (Programs)** — `LoVe02_ProgramsAndTheorems_ExerciseSheet.lean`
--   3. Extend `simplifyAExp` with more algebraic laws (e.g. `0 * e`, `e - e`,
--      at your own risk for division). State informally what “correct” means
--      (same as `eval loveDemoEnv` for all envs?).
--   4. Re-implement `map` on lists and state functor laws in English.
--
-- **LoVe Demos 3–4 (Proofs)** — backward vs forward tactics have no direct
--   Haskell runtime counterpart; pick one short theorem from each demo file
--   and reproduce it in Lean, then relate the proof term to a Haskell function
--   type (e.g. `And_swap` ↔ `andSwap`).
--
-- ----------------------------------------------------------------------------

main :: IO ()
main =
  putStrLn
    ( unlines
        [ "LoVe mirror loaded. Try in GHCi:",
          "  evalA loveDemoEnv (Mul (Var \"x\") (Num 2))",
          "  simplifyAExp (Add (Num 0) (Mul (Num 1) (Var \"x\")))",
          "  fibNat (Succ (Succ (Succ Zero)))"
        ]
    )
