{-  POPL'17 Radicek et al. -}
{-  Lengths  10/04/06 -}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module BoolExpr where
import Prelude hiding (return, (>>=), pure, sort, (<*>), length)
import Lists
import RTick
import Erasure

import ProofCombinators

theorem :: [a] -> Proof
{-@ theorem :: xs:[a] -> { (tval (length1 xs) == length xs) && (tval (length2 xs) == length xs) && (tcost (length2 xs) - tcost (length1 xs) == length xs) } @-}
theorem xs =
      (tcost (length1 xs) ==. 0         *** QED)
    ? (tcost (length2 xs) ==. length xs *** QED)
    ? (tval  (length1 xs) ==. length xs *** QED)
    ? (tval  (length2 xs) ==. length xs *** QED)


{-@ reflect lengthH @-}
{-@ lengthH :: xs:[a] -> i:Int -> {o:Int | o == length xs + i } @-}
lengthH :: [a] -> Int -> Int
lengthH [] n     = n
lengthH (_:xs) n = lengthH xs (n+1)

{-@ reflect length1 @-}
{-@ length1 :: xs:[a] -> {t:Tick {i:Int | i == length xs } | tcost t == 0 } @-}
length1 :: [a] -> Tick Int
length1 xs = return (lengthH xs 0)

{-@ reflect length2 @-}
{-@ length2 :: xs:[a] -> {t:Tick {i:Int | i == length xs } | tcost t == length xs } @-}
length2 :: [a] -> Tick Int
length2 []     = return 0
length2 (_:xs) = (pure plus1) </> length2 xs

{-@ reflect plus1 @-}
plus1 :: Int -> Int
plus1 x = 1 + x