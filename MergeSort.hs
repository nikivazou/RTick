
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
--

{-@ LIQUID "--reflection" @-}

module MergeSort where

import Prelude hiding
  ( Functor(..)
  , Applicative(..)
  , Monad(..)
  , drop
  , length
  , take
  )

import RTick
import ProofCombinators
import Arithmetic
import Erasure
import Lists ( cons, length )

--
-- Merge sort. Throughout this file the cost model is the number
-- of comparisons.
--

-- A type for ordered lists.
{-@ type OList a = [a]<{\x y -> x <= y}> @-}

-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

{-@ reflect merge @-}
{-@ merge
  :: Ord a
  => xs:(OList a)
  -> ys:(OList a)
  -> { t:Tick { zs:(OList a) | length xs + length ys == length zs }
          | tcost t <= length xs + length ys &&
            tcost t >= if (length xs) < (length ys) then (length xs) else (length ys) }
  /  [length xs + length ys]
  @-}
merge :: Ord a => [a] -> [a] -> Tick [a]
merge xs [] = pure xs
merge [] ys = pure ys
merge (x : xs) (y : ys)
  | x <= y    = pure (cons x) </> merge xs (y : ys)
  | otherwise = pure (cons y) </> merge (x : xs) ys

{-@ reflect msort @-}
{-@ msort
  :: Ord a
  => xs:[a]
  -> Tick { zs:(OList a) | length xs == length zs }
  /  [length xs, 1]
@-}
msort :: Ord a => [a] -> Tick [a]
msort []  = pure []
msort [x] = pure [x]
msort xs  = (take l xs >>= msort) >>= msortMerge xs
  where l = length xs `div` 2

{-@ reflect msortMerge @-}
{-@ msortMerge
  :: Ord a
  => { xs:[a]            | length xs > 1                    }
  -> { sorted:(OList a)  | (length xs) / 2 == length sorted }
  -> Tick { zs:(OList a) | length xs       == length zs     }
  /  [length xs, 0]
@-}
msortMerge :: Ord a => [a] -> [a] -> Tick [a]
msortMerge xs sorted = (drop l xs >>= msort) >>= merge sorted
  where l = length xs `div` 2

-------------------------------------------------------------------------------
-- | Cost proofs:
-------------------------------------------------------------------------------

--
-- @msort@ upper bound is @2 * (length xs) * log2 (length xs)@.
--
{-@ msortCostUB
  :: Ord a
  => { xs:[a] | p2 (length xs) }
  -> { tcost (msort xs) <= 2 * (length xs) * log2 (length xs) }
  /  [length xs, 2]
@-}
msortCostUB :: Ord a => [a] -> Proof
msortCostUB xs@[x]
  =   tcost (msort xs)
   -- { defn. of msort }
  ==. tcost (pure xs)
   -- { defn. of pure }
  ==. tcost (Tick 0 xs)
   -- { defn. of tcost }
  ==. 0
   -- { zero property of (*) }
  ==. 2 * length xs * 0
   ? toProof (log2 1)
  ==. 2 * length xs * log2 1
   -- { defn. of length }
  ==. 2 * length xs * log2 (length xs)
  *** QED
msortCostUB xs
  =   tcost (msort xs)
   -- { defn. of msort }
  ==. tcost ((take l xs >>= msort) >>= msortMerge xs)
   -- { defn. of (>>=) }
  ==. tcost (take l xs >>= msort) + tcost (msortMerge xs (tval (take l xs >>= msort)))
   -- { defn. of (>>=) }
  ==. tcost (take l xs) + tcost (msort (tval (take l xs))) + tcost (msortMerge xs (tval (take l xs >>= msort)))
   -- { tcost (take l xs) == 0 }
  ==. tcost (msort (tval (take l xs))) + tcost (msortMerge xs (tval (take l xs >>= msort)))
   ? (length (tval (take l xs)) ==. l *** QED)
   ? toProof (prevP2 (length xs))
   ? msortCostUB (tval (take l xs))
  <=. (2 * l * log2 l) + tcost (msortMerge xs (tval (take l xs >>= msort)))
   ? msortMergeCostUB' xs (tval (take l xs >>= msort))
  <=. (2 * l * log2 l) + (length xs * log2 l) + length xs
   -- { inline l }
  ==. (2 * (length xs `div` 2) * log2 l) + (length xs * log2 l) + length xs
   ? toProof (p2Even (length xs))
   ? evenDiv2 (length xs)
  ==. (length xs * log2 l) + (length xs * log2 l) + length xs
   -- { arithmetic }
  ==. (2 * length xs * log2 l) + length xs
   -- { inline l }
  ==. (2 * length xs * log2 (length xs `div` 2)) + length xs
   ? log2Div (length xs) 2
  ==. (2 * length xs * (log2 (length xs) - log2 2)) + length xs
   ? toProof (log2 2)
  ==. (2 * length xs * (log2 (length xs) - 1)) + length xs
   -- { arithmetic }
  ==. (2 * length xs * log2 (length xs)) - (2 * length xs) + length xs
   -- { arithmetic }
  ==. (2 * length xs * log2 (length xs)) - length xs
   -- { arithmetic }
  <.  2 * length xs * log2 (length xs)
  *** QED
  where l = length xs `div` 2

--
-- @msortMerge@ upper bound is
-- @(length xs * log2 ((length xs) / 2)) + length xs@.
--
{-@ msortMergeCostUB'
  :: Ord a
  => { xs:[a]           | length xs > 1 && p2 (length xs) }
  -> { sorted:(OList a) | length sorted == length xs / 2 }
  -> { tcost (msortMerge xs sorted) <= (length xs * log2 ((length xs) / 2)) + length xs }
  /  [length xs, 1]
@-}
msortMergeCostUB' :: Ord a => [a] -> [a] -> Proof
msortMergeCostUB' xs sorted = ()
   ? msortMergeCostUB xs sorted
   ? toProof (p2Even (length xs))
   ? evenDiv2 (length xs)

--
-- @msortMerge@ upper bound is
-- @(2 * length sorted * log2 (length sorted))+ (2 * length sorted)@.
--
{-@ msortMergeCostUB
  :: Ord a
  => { xs:[a] | length xs > 1 && p2 (length xs) }
  -> sorted:{ (OList a) | length sorted == length xs / 2 }
  -> { tcost (msortMerge xs sorted) <= (2 * length sorted * log2 (length sorted))
          + (2 * length sorted) }
  /  [length xs, 0]
@-}
msortMergeCostUB :: Ord a => [a] -> [a] -> Proof
msortMergeCostUB xs sorted
  =   tcost (msortMerge xs sorted)
   -- { defn. of msortMerge }
  ==. tcost ((drop l xs >>= msort) >>= merge sorted)
   -- { defn. of (>>=) }
  ==. tcost (drop l xs >>= msort) + tcost (merge sorted (tval (drop l xs >>= msort)))
   -- { tcost (merge xs ys) <= length xs + length ys }
  <=. tcost (drop l xs >>= msort) + length sorted + length (tval (drop l xs >>= msort))
   ? (length (tval (drop l xs >>= msort)) == length xs - l *** QED)
  ==. tcost (drop l xs >>= msort) + length sorted + length xs - l
   -- { length sorted = length xs `div` 2 }
  ==. tcost (drop l xs >>= msort) + length xs `div` 2 + length xs - l
   -- { inline l }
  ==. tcost (drop l xs >>= msort) + length xs `div` 2 + length xs - length xs `div` 2
   -- { arithmetic }
  ==. tcost (drop l xs >>= msort) + length xs
   -- { defn. of (>>= ) }
  ==. tcost (drop l xs) + tcost (msort (tval (drop l xs))) + length xs
   -- { tcost (drop l xs) == 0 }
  ==. tcost (msort (tval (drop l xs))) + length xs
   ? toProof (prevP2 (length xs))
   ? msortCostUB (tval (drop l xs))
  <=. 2 * length (tval (drop l xs)) * log2 (length (tval (drop l xs))) + length xs
   ? (length (tval (drop l xs)) ==. length xs - l *** QED)
  ==. 2 * (length xs - l) * log2 (length xs - l) + length xs
   -- { arithmetic, inline l }
  ==. ((2 * length xs) - (2 * (length xs `div` 2))) * log2 (length xs - (length xs `div` 2)) + length xs
   ? evenDiv2 (length xs)
  ==. ((2 * length xs) - length xs) * log2 (length xs - (length xs `div` 2)) + length xs
   -- { arithmetic }
  ==. (length xs * log2 (length xs - (length xs `div` 2))) + length xs
   ? (l ==. length sorted *** QED)
   ? evenDiv2 (length xs)
  ==. ((2 * length sorted) * log2 ((2 * length sorted) - length sorted)) + (2 * length sorted)
   -- { arithmetic }
  ==. (2 * length sorted * log2 (length sorted)) + (2 * length sorted)
  *** ASS
  where l = length xs `div` 2

--
-- @msort@ lower bound is @((length xs) / 2) * log2 (length xs)@.
--
{-@ msortCostLB
  :: Ord a
  => { xs:[a] | p2 (length xs) }
  -> { tcost (msort xs) >= ((length xs) / 2) * log2 (length xs) }
  /  [length xs, 1]
@-}
msortCostLB :: Ord a => [a] -> Proof
msortCostLB xs@[x]
  =   tcost (msort xs)
   -- { defn. of msort }
  ==. tcost (pure xs)
   -- { defn. of pure }
  ==. tcost (Tick 0 xs)
   -- { defn. of tcost }
  ==. 0
   -- { zero property of (*) }
  ==. (length xs `div` 2) * 0
   ? toProof (log2 1)
  ==. (length xs `div` 2) * log2 1
   -- { defn. of length }
  ==. (length xs `div` 2) * log2 (length xs)
  *** QED
msortCostLB xs
  =   tcost (msort xs)
   -- { defn. of msort }
  ==. tcost ((take l xs >>= msort) >>= msortMerge xs)
   -- { defn. of (>>=) }
  ==. tcost (take l xs >>= msort) + tcost (msortMerge xs (tval (take l xs >>= msort)))
   -- { defn. of (>>=) }
  ==. tcost (take l xs) + tcost (msort (tval (take l xs))) + tcost (msortMerge xs (tval (take l xs >>= msort)))
   -- { tcost (take l xs) == 0 }
  ==. tcost (msort (tval (take l xs))) + tcost (msortMerge xs (tval (take l xs >>= msort)))
   ? toProof (prevP2 (length xs))
   ? msortCostLB (tval (take l xs))
   ? (length (tval (take l xs)) ==. l *** QED)
  >=. ((l `div` 2) * log2 l) + tcost (msortMerge xs (tval (take l xs >>= msort)))
   ? msortMergeCostLB xs (tval (take l xs >>= msort))
  >=. ((l `div` 2) * log2 l) + ((length xs `div` 4) * log2 (length xs `div` 2) + (length xs `div` 2))
   -- { inline l }
  ==. (((length xs `div` 2) `div` 2) * log2 (length xs `div` 2)) + ((length xs `div` 4) * log2 (length xs `div` 2) + (length xs `div` 2))
   ? (((length xs `div` 2) `div` 2) ==. length xs `div` 4 *** QED)
  ==. ((length xs `div` 4) * log2 (length xs `div` 2)) + ((length xs `div` 4) * log2 (length xs `div` 2) + (length xs `div` 2))
   -- { arithmetic }
  ==. (2 * (length xs `div` 4) * log2 (length xs `div` 2)) + (length xs `div` 2)
   ? lemma2 xs
  ==. ((length xs `div` 2) * log2 (length xs `div` 2)) + (length xs `div` 2)
   ? log2Div (length xs) 2
  ==. ((length xs `div` 2) * (log2 (length xs) - log2 2)) + (length xs `div` 2)
   ? toProof (log2 2)
  ==. ((length xs `div` 2) * (log2 (length xs) - 1)) + (length xs `div` 2)
   -- { arithmetic }
  ==. ((length xs `div` 2) * log2 (length xs)) - (length xs `div` 2) + (length xs `div` 2)
   -- { arithmetic }
  ==. (length xs `div` 2) * log2 (length xs)
  *** QED
  where l = length xs `div` 2

--
-- @msortMerge@ lower bound is
-- @((length xs / 4) * log2 (length xs / 2)) + (length xs / 2)@.
--
{-@ msortMergeCostLB
  :: Ord a
  => { xs:[a] | length xs > 1 && p2 (length xs) }
  -> { sorted:(OList a) | (length xs) / 2 == length sorted }
  -> { tcost (msortMerge xs sorted) >= ((length xs / 4) * log2 (length xs / 2)) + (length xs / 2) }
  / [length xs, 0]
@-}
msortMergeCostLB :: Ord a => [a] -> [a] -> Proof
msortMergeCostLB xs sorted
  =   tcost (msortMerge xs sorted)
   -- { defn. of msortMerge }
  ==. tcost ((drop l xs >>= msort) >>= merge sorted)
   -- { defn. of (>>=) }
  ==. tcost (drop l xs >>= msort) + tcost (merge sorted (tval (drop l xs >>= msort)))
   -- { defn. of (>>=) }
  ==. tcost (drop l xs) + tcost (msort (tval (drop l xs))) + tcost (merge sorted (tval (drop l xs >>= msort)))
   -- { tcost (drop l xs) == 0 }
  ==. tcost (msort (tval (drop l xs))) + tcost (merge sorted (tval (drop l xs >>= msort)))
   ? toProof (prevP2 (length xs))
   ? msortCostLB (tval (drop l xs))
  >=. ((length (tval (drop l xs)) `div` 2) * log2 (length (tval (drop l xs)))) + tcost (merge sorted (tval (drop l xs >>= msort)))
   ? (length (tval (drop l xs >>= msort)) == l *** QED)
  ==. ((l `div` 2) * log2 l) + tcost (merge sorted (tval (drop l xs >>= msort)))
   -- { inline l }
  ==. (((length xs `div` 2) `div` 2) * log2 (length xs `div` 2)) + tcost (merge sorted (tval (drop l xs >>= msort)))
   ? (((length xs `div` 2) `div` 2) ==. length xs `div` 4 *** QED)
  ==. ((length xs `div` 4) * log2 (length xs `div` 2)) + tcost (merge sorted (tval (drop l xs >>= msort)))
   ? lemma1 sorted (tval (drop l xs >>= msort))
  >=. ((length xs `div` 4) * log2 (length xs `div` 2)) + length sorted
   -- { (length xs) `div` 2 == length sorted }
  ==. ((length xs `div` 4) * log2 (length xs `div` 2)) + (length xs `div` 2)
  *** QED
  where l = length xs `div` 2

-- Lemmas: --------------------------------------------------------------------

--
-- If @length xs == length ys@, then the lower bound of @merge@ is @length xs@.
--
{-@ lemma1
      :: Ord a
      => xs:(OList a)
      -> { ys:(OList a) | length xs == length ys }
      -> { tcost (merge xs ys) >= length xs }
@-}
lemma1 :: Ord a => [a] -> [a] -> Proof
lemma1 xs ys
  =   tcost (merge xs ys)
  >=. (if length xs < length ys then length xs else length ys)
   -- { length xs == length ys }
  ==. (if length xs < length xs then length xs else length xs)
   -- { inline if }
  ==. length xs
  *** QED

--
-- If @length xs == 2@,
-- then @log2 ((length xs) / 2) == 0@.
--
-- If @length xs > 2 && p2 (length xs)@,
-- then @2 * ((length xs) / 4) == ((length xs) / 2)@.
--
{-@ lemma2
  :: Ord a
  => { xs:[a] | length xs >= 2 && p2 (length xs) }
  -> { 2 * ((length xs) / 4) * log2 ((length xs) / 2) ==
        ((length xs) / 2) * log2 ((length xs) / 2) }
@-}
lemma2 :: Ord a => [a] -> Proof
lemma2 xs | length xs == 2
  =   2 * (length xs `div` 4) * log2 (length xs `div` 2)
   -- { defn. of length }
  ==. 2 * (2 `div` 4) * log2 (2 `div` 2)
   -- { arithmetic }
  ==. 2 * (2 `div` 4) * log2 1
   -- { defn. of div, defn. of log2 }
   ? toProof (log2 1)
  ==. 2 * 0 * 0
   -- { arithmetic }
  ==. 0
   -- { zero property of (*) }
  ==. 1 * 0
   -- { defn. of div, defn. of log2 }
  ==. (2 `div` 2) * log2 (2 `div` 2)
   -- { defn. of length }
  ==. (length xs `div` 2) * log2 (length xs `div` 2)
  *** QED
-- Note: if @length xs > 2 && p2 (length xs)@,
-- then @2 * (length xs `div` 4) == length xs `div 2@.
-- This follows immediately because @length xs@ is a power of 2.
lemma2 xs | length xs > 2 = toProof (prevP2 (length xs)) &&& toProof (prevP2 (prevP2 (length xs)))

-------------------------------------------------------------------------------
-- | Helper functions:
-------------------------------------------------------------------------------

--
-- Notice that @tcost == 0@ for both @take@ and @drop@.
-- This is because neither function makes any comparisons.
--

{-@ reflect take @-}
{-@ take :: n:Nat -> { xs:[a] | n <= length xs }
    -> { t:Tick { zs:[a] | length zs == n } | tcost t == 0 }
@-}
take :: Int -> [a] -> Tick [a]
take _ []       = pure []
take 0 _        = pure []
take n (x : xs) = pure (cons x) <*> take (n - 1) xs

{-@ reflect drop @-}
{-@ drop :: n:Nat -> { xs:[a] | n <= length xs }
    -> { t:Tick { zs:[a] | length zs == length xs - n } | tcost t == 0 }
@-}
drop :: Int -> [a] -> Tick [a]
drop _ []       = pure []
drop 0 xs       = pure xs
drop n (_ : xs) = drop (n - 1) xs