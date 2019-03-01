{- Relational MSort 23/25/59 -}

{-# LANGUAGE  FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module RelationalMSort where

{-@ infix <*> @-}
{-@ infix :   @-}

import RTick
import ProofCombinators
import Lists
import Log2
import PowerOf2
import Erasure
import Prelude hiding (return, (>>=), pure, length, (<*>), log, take, drop, min)


{- ple theorem @-}
{-@ theorem :: Ord a => xs:[a] -> ys:{[a] | length xs = length ys && powerOf2 (length xs) }
  -> { tcost (msort xs) - tcost (msort ys) <= length xs * (1 + log (differ xs ys))}
  / [length xs] @-}
theorem :: Ord a => [a] -> [a] -> Proof
theorem xs@[] ys@[]
  =   tcost (msort xs) - tcost (msort ys)
  ==. 0 - 0
  <=. length xs * (1 + log (differ xs ys))
  *** QED
theorem xs@[x] ys@[y]
  =   tcost (msort xs) - tcost (msort ys)
  ==. tcost (return [x]) - tcost (return [y])
  ==. 0 - 0
      ? logNat (differ xs ys)
  <=. length xs * (1 + log (differ xs ys))
  *** QED
theorem xs@(_:_:_) ys@(_:_:_) = if differ xs ys == 0 then theoremSameLists xs ys else (
      tcost (msort xs) - tcost (msort ys)
  ==. tcost (step 2 (zipWithM merge (msort xs1) (msort xs2)))
  -   tcost (step 2 (zipWithM merge (msort ys1) (msort ys2)))
  ==. tcost (zipWithM merge (msort xs1) (msort xs2))
  -   tcost (zipWithM merge (msort ys1) (msort ys2))
  ==. tcost (msort xs1) + tcost (msort xs2) + tcost (merge (tval (msort xs1)) (tval (msort xs2)))
  -   tcost (msort ys1) - tcost (msort ys2) - tcost (merge (tval (msort ys1)) (tval (msort ys2)))
     ? powerOfIsEven n
     ? assert (length xs1 == n2)
     ? assert (length xs2 == n2)
     ? assert (length ys1 == n2)
     ? assert (length ys2 == n2)
     ? assert (n2 < n && 0 <= n2)
     ? theorem xs1 ys1
     ? theorem xs2 ys2
  <=. (n `div` 2) * (1 + log (differ xs1 ys1)) + (n `div` 2) * (1 + log (differ xs2 ys2))
       + tcost (merge (tval (msort xs1)) (tval (msort xs2)))
       - tcost (merge (tval (msort ys1)) (tval (msort ys2)))
  <=. (n `div` 2) * (1 + log (differ xs1 ys1)) + (n `div` 2) * (1 + log (differ xs2 ys2))
       + n2 + n2 - min n2 n2
  <=. (n `div` 2) * ( 3 + log (differ xs1 ys1) + log (differ xs2 ys2))
      ? splitDiffer (n `div` 2) xs ys
      ? assert (differ xs1 ys1 + differ xs2 ys2 == differ xs ys)
      ? loghelper (differ xs1 ys1) (differ xs2 ys2) (differ xs ys)
  <=. (n `div` 2) * ( 3 + 2 * log (differ xs ys))
       ? distributeDiv n 3 (log (differ xs ys))
  <=. n * (3 `div` 2 + log (differ xs ys))
  <=. n * (1 + log (differ xs ys))
  *** QED )
  where
    P xs1 xs2 = split xs
    P ys1 ys2 = split ys
    n         = length xs
    n2        = length xs `div` 2

-- Some math assumptions
distributeDiv :: Int -> Int -> Int -> Proof
{-@ assume distributeDiv
  :: n:{Int | powerOf2 n}
  -> x:Int -> y:Int
  -> {(n/2 * (x + 2 * y)) == n * (x/2 + y )} @-}
distributeDiv _ _ _ = ()


loghelper :: Int -> Int -> Int -> Proof
{-@ assume loghelper :: d1:Int -> d2:Int -> d:{Int | 0 < d && d == d1 + d2 }
          -> { log d1 + log d2 <= 2 * (log d)} @-}
loghelper _ _ _ = ()
{-

   log d1 + log d2
== log (d - d2) + log (d - d1)
== 2 * log d + log (1 - d2/d) + log (1 - d1/d)
<= 2 * log d
-}

-- This is assumed since the upper bound goes to -infinity in this case
{-@ assume theoremSameLists :: Ord a => xs:[a] -> ys:{[a] | length xs = length ys && powerOf2 (length xs) && (differ xs ys == 0) }
  -> { tcost (msort xs) - tcost (msort ys) <= length xs * (1 + log (differ xs ys))}
  @-}
theoremSameLists :: Ord a => [a] -> [a] -> Proof
theoremSameLists _ _ = ()

{-@ ple splitDiffer @-}
splitDiffer :: Ord a => Int -> [a] -> [a] -> Proof
{-@ splitDiffer :: Ord a => n:Nat
   -> xs:{[a] | n <= length xs }
   -> ys:{[a] | n <= length ys && length xs == length ys }
   -> { differ xs ys == differ (take n xs) (take n ys) + differ (drop n xs) (drop n ys) } @-}

splitDiffer 0 _ _
  = ()
splitDiffer n (_:xs) (_:ys)
  = splitDiffer (n-1) xs ys


{-@ reflect differ @-}
{-@ differ :: Ord a => xs:[a] -> ys:{[a] | length xs == length ys } -> Nat @-}
differ :: Ord a => [a] -> [a] -> Int
differ [] [] = 0
differ (x:xs) (y:ys)
  | x == y    = differ xs ys
  | otherwise = 1 + differ xs ys


{-@ reflect msort @-}
{-@ msort :: Ord a => xs:[a] -> Tick ({o:OList a | length o == length xs }) / [length xs] @-}
msort :: Ord a => [a] -> Tick [a]
msort []  = return []
msort [x] = return [x]
msort xs  = step 2 (zipWithM merge (msort xs1) (msort xs2))
  where
    P xs1 xs2 = split xs

{-@ reflect merge @-}
{-@ merge :: Ord a => xs:(OList a) -> ys:(OList a)
          -> {t:Tick ({o:OList a | length o == length xs + length ys }) | tcost t <= length xs + length ys && min (length xs) (length ys) <= tcost t }
          / [length xs + length ys] @-}
merge :: Ord a => [a] -> [a] -> Tick [a]
merge [] ys = return ys
merge xs [] = return xs
merge (x:xs) (y:ys)
  | x <= y    = pure (x:) </> merge xs (y:ys)
  | otherwise = pure (y:) </> merge (x:xs) ys


{-@ inline min @-}
min :: Int -> Int -> Int
min x y = if x <= y then x else y


data P a b = P a b
{-@ data P a b <p :: a -> b -> Bool> = P {left :: a, rigth :: b<p left>}@-}
{-@ reflect split @-}
split :: [a] -> P [a] [a]
{-@ split :: x:[a]
  -> P <{\l r -> (2 <= length x => (length l < length x && length r < length x)) && length l + length r == length x && (
    ((length x) mod 2 == 0 ) => (length l == length x / 2 && length r == length x / 2)
  )}> [a] [a] @-}

split xs = P (take n xs) (drop n xs)
    where n = length xs `div` 2
-- split []      = P [] []
-- split (x1:xs) = case xs of {[] -> P [x1] []; (x2:xs2) -> let P xs1 xs2 = split xs2 in P (x1:xs1) (x2:xs2)}