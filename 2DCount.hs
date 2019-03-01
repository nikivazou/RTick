{- 2DCount 16/3/24 -}

{-# LANGUAGE  FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module TwoDCount where

{-@ infix <*> @-}
{-@ infix :   @-}

import RTick
import ProofCombinators
import Lists
import Erasure

import Prelude hiding (return, (>>=), pure, length, (<*>))


theorem :: Ord a => ([a] -> Bool )-> a -> [[a]] -> Proof
{-@ theorem :: Ord a => p:([a] -> Bool) -> x:a -> m:[[a]]
  -> { tcost (count2D find1 p x m) <= tcost (count2D find2 p x m) } @-}
theorem p x [] = ()
theorem p x (l:m) = theorem p x m ? theoremFind x l

theoremFind :: Ord a => a -> [a] -> Proof
{-@ theoremFind :: x:a -> ls:[a] -> { tcost (find1 x ls) <= tcost (find2 x ls ) } @-}
theoremFind x [] = ()
theoremFind x (l:ls) | x == l
  =   tcost (find1 x (l:ls))
  ==. 0
  <=. 1 + tcost (find2 x ls)
  ==. 1 + tcost (find2 x ls) + tcost (find2Cond 1 (tval (find2 x ls)))
  ==. tcost (find2 x ls >/= find2Cond (if x == l then 1 else 0))
  ==. tcost (find2 x (l:ls))
  *** QED

theoremFind x (l:ls)
  =   tcost (find1 x (l:ls))
  ==. tcost (step 1 (find1 x ls))
  ==. 1 + tcost (find1 x ls)
      ? theoremFind x ls
  <=. 1 + tcost (find2 x ls)
  ==. 1 + tcost (find2 x ls) + tcost (find2Cond 0 (tval ((find2 x ls))))
  ==. tcost (find2 x ls >/= find2Cond 0)
  ==. tcost (find2 x ls >/= find2Cond (if x == l then 1 else 0))
  ==. tcost (find2 x (l:ls))
  *** QED

{-@ reflect count2D @-}
count2D :: Ord a => (a -> [a] -> Tick Int) -> ([a] -> Bool )-> a -> [[a]] -> Tick Int
count2D _    _ _ [] = return 0
count2D find p x (l:m) = count2D find p x m >>= count2D' (p l) (find x l)

{-@ reflect count2D' @-}
count2D' :: Bool -> Tick Int -> Int -> Tick Int
count2D' b c r = if b then (pure (+r) <*> c) else return r


{-@ reflect find1 @-}
find1 :: Ord a => a -> [a] -> Tick Int
{-@ find1 :: Ord a => a -> [a] -> {t:Tick Int | 0 <= tcost t} @-}
find1 x []    = return 0
find1 x (y:ys)
  | x == y    = return 1
  | otherwise = step 1 (find1 x ys)

{-@ reflect find2 @-}
{-@ find2 :: Ord a => a -> [a] -> {t:Tick Int | 0 <= tcost t} @-}
find2 :: Ord a => a -> [a] -> Tick Int
find2 x []     = return 1
find2 x (y:ys) = step 1 (eqBind 0 (find2 x ys) (find2Cond (if x == y then 1 else 0)))

{-@ reflect find2Cond @-}
{-@ find2Cond :: Ord a => Int -> Int -> {t:Tick Int | 0 == tcost t} @-}
find2Cond :: Int -> Int -> Tick Int
find2Cond d 1 = return 1
find2Cond d _ = return d