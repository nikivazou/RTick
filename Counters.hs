
{- Counters 26/21/21 -}

--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.s
--

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Counters where

import Prelude hiding (return, (>>=), pure, length)

import RTick
import ProofCombinators
import Lists
import Erasure

--
-- Comparing bit flips using relational cost analysis.
--

{-@ reflect tt @-}
{-@ tt :: n:Nat -> { zs:[{ v:Bool | v == True }] | n == length zs } @-}
tt :: Int -> [Bool]
tt 0 = []
tt n = True : tt (n - 1)

{-@ reflect ff @-}
{-@ ff :: n:Nat -> { zs:[{ v:Bool | v == False }] | n == length zs } @-}
ff :: Int -> [Bool]
ff 0 = []
ff n = False : ff (n - 1)

dualTTFF :: Int -> Proof
{-@ dualTTFF :: l:Nat -> { dual (ff l) (tt l) } @-}
dualTTFF 0 = ()
dualTTFF i = dualTTFF (i - 1)

-------------------------------------------------------------------------------

property :: Int -> Int -> Proof
{-@ property
  :: m:Nat
  -> n:Nat
  -> { (tcost (incrN m (ff n)) == tcost (decrN m (tt n))) }
@-}
property k l = dualOpsGen k (ff l) (tt l ? dualTTFF l)

dualOpsGen :: Int -> [Bool] -> [Bool] -> Proof
{-@ dualOpsGen
  :: n:Nat
  -> xs:[Bool]
  -> { ys:[Bool] | length xs == length ys && dual xs ys }
  -> { tcost (incrN n xs) == tcost (decrN n ys) }
@-}
dualOpsGen 0 _ _ = ()
dualOpsGen n xs ys
  =   tcost (incrN n xs)
  ==. tcost (incr xs >>= incrN (n - 1))
   ? dualOps xs ys
   ? dualOpsGen (n - 1) (tval (incr xs)) (tval (decr ys))
  ==. tcost (decr ys >>= decrN (n - 1))
  ==. tcost (decrN n ys)
  *** QED

{-@ dualOps
  :: xs:[Bool]
  -> { ys:[Bool] | length xs == length ys && dual xs ys}
  -> { tcost (incr xs) == tcost (decr ys) && dual (tval (incr xs)) (tval (decr ys)) }
@-}
dualOps :: [Bool] -> [Bool] -> Proof
dualOps [] [] = ()
dualOps (x : xs) (y : ys) | x && not y = dualOps xs ys
dualOps (x : xs) (y : ys) | y && not x = dualOps xs ys
dualOps _ _ = ()

{-@ reflect dual @-}
{-@ dual
  :: xs:[Bool]
  -> { ys:[Bool] | length xs == length ys }
  -> Bool
@-}
dual :: [Bool] -> [Bool] -> Bool
dual [] [] = True
dual (x : xs) (y : ys) = x /= y && dual xs ys

{-@ reflect incrN @-}
{-@ incrN :: Nat -> [Bool] -> Tick [Bool] @-}
incrN :: Int -> [Bool] -> Tick [Bool]
incrN 0 xs = return xs
incrN n xs = incr xs >>= incrN (n - 1)

{-@ reflect incr @-}

{-@ incr
  :: xs:[Bool]
  -> Tick { zs:[Bool] | length zs == length xs }
@-}
incr :: [Bool] -> Tick [Bool]
incr [] = return []
incr (False:xs) = pure (True:)  </> pure xs
incr (True:xs)  = pure (False:) </> incr xs

{-@ reflect decrN @-}
{-@ decrN :: Nat -> [Bool] -> Tick [Bool]
@-}
decrN :: Int -> [Bool] -> Tick [Bool]
decrN 0 xs = return xs
decrN n xs = decr xs >>= decrN (n - 1)

{-@ reflect decr @-}
{-@ decr
  :: xs:[Bool]
  -> Tick { zs:[Bool] | length xs == length zs }
@-}
decr :: [Bool] -> Tick [Bool]
decr [] = return []
decr (False : xs) = pure (True:)  </> decr xs
decr (True  : xs) = pure (False:) </> pure xs