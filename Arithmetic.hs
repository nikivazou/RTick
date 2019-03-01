
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
-- Martin A.T. Handley, Niki Vazou, and Graham Hutton.
--

{-@ LIQUID "--reflection" @-}

module Arithmetic where

import RTick
import ProofCombinators

--
-- A number of arithmetic operations, proofs, and axioms.
--

-------------------------------------------------------------------------------
-- | Evens and odds:
-------------------------------------------------------------------------------

{-@ type Even = { n:Int | n mod 2 == 0 } @-}
{-@ type Odd  = { n:Int | n mod 2 == 1 } @-}

-- Addition: ------------------------------------------------------------------

--
-- @m:Even ==> (m + 1):Odd@.
--
{-@ evenPlus1 :: m:Even -> { n:Odd | m + 1 == n } @-}
evenPlus1 :: Int -> Int
evenPlus1 m = m + 1

--
-- @m:Odd ==> (m + 1):Even@.
--
{-@ oddPlus1 :: m:Odd -> { n:Even | m + 1 == n } @-}
oddPlus1 :: Int -> Int
oddPlus1 m = m + 1

-- Subtraction: ---------------------------------------------------------------

--
-- @m:Even ==> (m - 1):Odd@.
--
{-@ evenMinus1 :: m:Even -> { n:Odd | m - 1 == n } @-}
evenMinus1 :: Int -> Int
evenMinus1 m = m - 1

--
-- @m:Odd ==> (m - 1):Even@.
--
{-@ oddMinus1 :: m:Odd -> { n:Even | m - 1 == n } @-}
oddMinus1 :: Int -> Int
oddMinus1 m = m - 1

-- Multiplication: ------------------------------------------------------------

--
-- @Even * Even == Even@.
--
{-@ evenTimesEven :: m:Even -> n:Even -> { o:Even | m * n == o } @-}
evenTimesEven :: Int -> Int -> Int
evenTimesEven m n = m * n
  ? timesModCong m n (m * n) ()

--
-- @Even * Odd == Even@.
--
{-@ evenTimesOdd :: m:Even -> n:Odd -> { o:Even | m * n == o } @-}
evenTimesOdd :: Int -> Int -> Int
evenTimesOdd m n = m * n
  ? timesModCong m n (m * n) ()

--
-- @Odd * Even == Even@.
--
{-@ oddTimesEven :: m:Odd -> n:Even -> { o:Even | m * n == o } @-}
oddTimesEven :: Int -> Int -> Int
oddTimesEven m n = m * n
  ? timesModCong m n (m * n) ()

--
-- @Odd * Odd == Odd@.
--
{-@ oddTimesOdd :: m:Odd -> n:Odd -> { o:Odd | m * n == o } @-}
oddTimesOdd :: Int -> Int -> Int
oddTimesOdd m n = m * n
  ? timesModCong m n (m * n) ()

--
-- @2 * m == n:Even@.
--
{-@ times2Even :: m:Int-> { n:Even | 2 * m == n } @-}
times2Even :: Int -> Int
times2Even m = 2 * m

-- Dividing by 2: -------------------------------------------------------------

--
-- @`div` 2@ doesn't truncate if @n:Even@.
--
{-@ evenDiv2 :: n:Even -> { n == 2 * (n / 2) } @-}
evenDiv2 :: Int -> Proof
evenDiv2 _ = ()

--
-- @`div` 2@ doesn't truncate if @n:Even@.
--
{-@ evenSubDiv2 :: n:Even -> { n / 2 == n - (n / 2) } @-}
evenSubDiv2 :: Int -> Proof
evenSubDiv2 _ = ()

--
-- @(n + 1) `div` 2@ truncates if @n:Even@.
--
{-@ roundUpDiv2 :: n:Even -> { n / 2 == (n + 1) / 2 } @-}
roundUpDiv2 :: Int -> Proof
roundUpDiv2 _ = ()

--
-- @n `div` 2@ truncates if @n:Odd@.
--
{-@ roundDownDiv2 :: n:Odd -> { n / 2 == (n - 1) / 2 } @-}
roundDownDiv2 :: Int -> Proof
roundDownDiv2 _ = ()

-- Distributing when dividing by 2: -------------------------------------------

--
-- (+ 1) distributes over @(m:Even `div` 2) + (n:Even `div` 2)@ and
-- @(m:Odd `div` 2) + (n:Odd `div` 2)@ due to truncation. This is a
-- special case where @m == n * n@.
--
{-@ distrPlus1Div2 :: n:Int
    -> { (((n * n) + 1) / 2) + (n / 2) == ((n * n) / 2) + ((n + 1) / 2) }
@-}
distrPlus1Div2 :: Int ->  Proof
distrPlus1Div2 n | n `mod` 2 == 0
  =   (((n * n) + 1) `div` 2) + (n `div` 2)
   ? toProof (evenTimesEven n n)
   ? toProof (evenPlus1 (n * n))
   ? roundDownDiv2 ((n * n) + 1)
  ==. ((n * n) `div` 2) + (n `div` 2)
   ? roundUpDiv2 n
  ==. ((n * n) `div` 2) + ((n + 1) `div` 2)
  *** QED
distrPlus1Div2 n | n `mod` 2 == 1
  =   (((n * n) + 1) `div` 2) + (n `div` 2)
   ? toProof (oddTimesOdd n n)
   ? toProof (oddPlus1 (n * n))
   ? roundUpDiv2 ((n * n) + 1)
  ==. (((n * n) + 2) `div` 2) + (n `div` 2)
   -- { arithmetic }
  ==. ((n * n) `div` 2) + (2 `div` 2) + (n `div` 2)
   -- { arithmetic }
  ==. ((n * n) `div` 2) + ((n + 1) `div` 2)
  *** QED

-------------------------------------------------------------------------------
-- | Powers of 2:
-------------------------------------------------------------------------------

{-@ measure p2 :: Nat -> Bool @-}

--
-- Given @2^k@, assume @2^(k + 1)@.
--
{-@ assume nextP2 :: { m:Nat | p2 m }
    -> { n:Nat | 2 * m == n && m == n / 2 && p2 n }
@-}
nextP2 :: Int -> Int
nextP2 m = 2 * m

--
-- Given @2^k@ where @k > 0@, assume @2^(k - 1)@.
--
{-@ assume prevP2 :: { m:Nat | m > 1 && p2 m }
    -> { n:Nat | m / 2 == n && m == 2 * n && p2 n }
@-}
prevP2 :: Int -> Int
prevP2 m = m `div` 2

--
-- Given @2^k@ where @k > 0@, assume @2^k@ is 'Even''.
--
{-@ p2Even :: { m:Nat | m > 1 && p2 m } -> { n:Even | m == n } @-}
p2Even :: Int -> Int
p2Even m = m
  ? toProof (prevP2 m)

--
-- 2^x
--
{-@ reflect twoToPower @-}
{-@ twoToPower :: Nat -> Nat @-}
twoToPower :: Int -> Int
twoToPower 0 = 1
twoToPower n = 2 * twoToPower (n - 1)

-------------------------------------------------------------------------------
-- | Binary logarithm:
-------------------------------------------------------------------------------

{-@ measure log2 :: a -> a @-}

--
-- Assume @log2@ rounded to the nearest integer.
--
{-@ assume log2 :: m:Int -> { n:Int | n == log2 m } @-}
log2 :: Int -> Int
log2 x = round (logBase 2 (fromIntegral x))

--
-- Assume @log2 1 == 0@.
--
{-@ assume log2One :: { log2 1 == 0 } @-}
log2One :: Proof
log2One  = ()

--
-- Assume @log2 2 == 1@.
--
{-@ assume log2Two :: { log2 2 == 1 } @-}
log2Two :: Proof
log2Two  = ()

--
-- Given @n > 0@, assume @log2 n >= 0@.
--
{-@ assume log2Nat :: { n:Int | n > 0 } -> { log2 n >= 0 } @-}
log2Nat :: Int -> Proof
log2Nat _ = ()

--
-- Given @n > 1@, assume @log2 n > 0@.
--
{-@ assume log2Pos :: { n:Int | n > 1 } -> { log2 n > 0 } @-}
log2Pos :: Int -> Proof
log2Pos _ = ()

--
-- Division law: @log2 (m `div` n) == log2 m - log2 n@.
--
{-@ assume log2Div :: m:Int -> n:Int
    -> { log2 (m / n) = log2 m - log2 n }
@-}
log2Div :: Int -> Int -> Proof
log2Div _ _ = ()

--
-- Multiplication law: @log2 (m * n) == log2 m + log2 n@.
--
{-@ assume log2Times :: m:Int -> n:Int
    -> { log2 (m * n) = log2 m + log2 n }
@-}
log2Times :: Int -> Int -> Proof
log2Times _ _ = ()

-------------------------------------------------------------------------------
-- | Axioms:
-------------------------------------------------------------------------------

--
-- When pattern matching on even-length lists, Liquid Haskell doesn't know
-- that, if length xs /= 0, then length xs > 1. Hence, we must assume it.
--
{-@ assume greaterThan1 :: n:Int -> { n > 1 } @-}
greaterThan1 :: Int -> Proof
greaterThan1 _ = ()

--
-- Liquid Haskell does not use Haskell's 'mod' function defined in the Prelude.
-- Instead it uses z3's 'mod' function directly. Consequently, we must assume
-- any congruence properties we wish to utilise.
--
-- Here we assume
--
--  (m * n == o) ==> ((m * n) mod 2 == o mod 2)
--
-- which is trivially true.
--
{-@ assume timesModCong :: m:Int -> n:Int -> o:Int -> { p:Proof | m * n == o }
    -> { (m * n) mod 2 == o mod 2 } @-}
timesModCong :: Int -> Int -> Int -> Proof -> Proof
timesModCong _ _ _ _ = ()