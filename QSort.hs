{- QSort 15/8/27 -}
{-# LANGUAGE  FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
module QSort where

{-@ infix <*> @-}
{-@ infix :   @-}

import RTick
import ProofCombinators
import Lists
import Erasure
import Arithmetic
import Prelude hiding (return, (>>=), pure, length, (<*>), log, take, drop, min)


qsortCost :: Ord a => [a] -> Proof
{-@ qsortCost :: Ord a => xs:[a] -> { tcost (qsort xs) <= (((length xs)+2) * ((length xs)+1)) / 2}
   / [length xs] @-}
qsortCost xs@[]
  = tcost (qsort xs)
  ==. tcost (return xs)
  ==. 0
  <=. ((length xs + 2) * (length xs +1)) `div` 2
  *** QED

qsortCost (x:xs)
  =   tcost (qsort (x:xs))
  ==. tcost (step 1 (zipWithM (appendWith x) (qsort lxs) (qsort gxs)))
  ==. 1 + tcost (zipWithM (appendWith x) (qsort lxs) (qsort gxs))
  ==. 1 + tcost (qsort lxs) + tcost (qsort gxs) + tcost (appendWith x (tval (qsort lxs)) (tval (qsort gxs)))
      ? qsortCost lxs ? qsortCost gxs
      ? assert (tcost (qsort lxs) <= ((l+2) * (l+1)) `div` 2)
      ? assert (tcost (qsort gxs) <= ((g+2) * (g+1)) `div` 2)
      ? assert (l + g == n)
  <=. 1 + ((l+2) * (l+1)) `div` 2 + ((g+2) * (g+1)) `div` 2 + l
  <=. ((n+2) * (n+1)) `div` 2 +  n + 2  -- 1 .. n+1
  <=. (n * n + 3*n + 2) `div` 2 +  n + 2
  <=. (n*n + 5*n + 6) `div` 2
  <=. ((n+3) * (n+2)) `div` 2 -- 1 .. n+2
  *** QED
    where
      P lxs gxs = splitOn x xs
      l = length lxs
      g = length gxs
      n = length xs

{-@ reflect qsort @-}
qsort :: Ord a => [a] -> Tick [a]
{-@ qsort :: Ord a => xs:[a] -> Tick ({o:OList a | length o == length xs })
          / [length xs] @-}
qsort []     = return []
qsort (x:xs) = step 1 (zipWithM (appendWith x) (qsort lxs) (qsort gxs))
  where
    P lxs gxs = splitOn x xs

{-@ reflect appendWith @-}
appendWith :: Ord a => a -> [a] -> [a] -> Tick [a]
{-@ appendWith :: Ord a => x:a -> l:OList {v:a | v <= x} -> g:OList {v:a | v > x}
               -> {t:Tick ({o:OList a | length o == length l + length g + 1}) | tcost t == length l } @-}
appendWith x [] g     = return (x:g)
appendWith x (l:ls) g = pure (l:) </> appendWith x ls g

{-@ reflect splitOn @-}
{-@ splitOn :: Ord a => x:a -> xs:[a] -> P <{\l r -> length l + length r == length xs }> [{v:a | v <= x}] [{v:a | v > x}] @-}
splitOn :: Ord a => a -> [a] -> P [a] [a]
splitOn _ [] = P [] []
splitOn x (y:ys)
  | y <= x    = P (y:l) g
  | otherwise = P l (y:g)
  where P l g = splitOn x ys


{-@ data P a b <p :: a -> b -> Bool> = P {left :: a, right :: b<p left>} @-}
data P a b = P a b
