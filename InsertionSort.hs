
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
-- Martin A.T. Handley, Niki Vazou, and Graham Hutton.
--

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module InsertionSort where

import Prelude hiding
  ( Functor(..)
  , Applicative(..)
  , Monad(..)
  , head
  , insert
  , length
  )

import RTick
import ProofCombinators
import Lists
import Erasure

--
-- Insertion sort. Throughout this file the cost model is the number
-- of comparisons.
--

-- A type for ordered lists.
{-@ type OList a = [a]<{\x y -> x <= y}> @-}

-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

{-@ reflect isort @-}
{-@ isort
  :: Ord a
  => xs:[a]
  -> t:Tick { zs : (OList a) | length xs == length zs }
@-}
isort :: Ord a => [a] -> Tick [a]
isort []       = return []
isort (x : xs) = isort xs >>= insert x

{-@ reflect isort' @-}
{-@ isort'
  :: Ord a
  => xs:[a]
  -> { t:Tick { zs : (OList a) | length xs == length zs }
       | tcost t <= length xs * length xs }
@-}
isort' :: Ord a => [a] -> Tick [a]
isort' []       = return []
isort' (x : xs) = leqBind (length xs) (isort' xs) (insert x)

{-@ reflect insert @-}
{-@ insert
  :: Ord a
  => x:a
  -> xs: OList a
  -> { t:Tick { zs : (OList a) | 1 + length xs == length zs }
       | tcost t <= length xs }
@-}
insert :: Ord a => a -> [a] -> Tick [a]
insert x [] = return [x]
insert x (y : ys)
  | x <= y    = wait (x : y : ys)
  | otherwise = pure (y:) </> insert x ys

-------------------------------------------------------------------------------
-- | Cost proofs:
-------------------------------------------------------------------------------

--
-- Extrinsic cost analysis for 'isort'.
-- Quadratic upper bound for any list.
--
{-@ isortCost :: Ord a => xs:[a]
    -> { tcost (isort xs) <= length xs * length xs } @-}
isortCost :: Ord a => [a] -> Proof
isortCost xs@[]
  =   tcost (isort xs)
   -- { defn. of isort}
  ==. tcost (return [])
   -- { defn. of return }
  ==. tcost (Tick 0 [])
   -- { defn. of tcost }
  ==. 0
   -- { arithmetic }
  ==. 0 * 0
   -- { defn. of length }
  ==. length [] * length []
   -- { (==.) implies (<=.) }
  <=. length [] * length []
  *** QED
isortCost (x : xs)
  =   tcost (isort (x : xs))
   -- { defn. of isort }
  ==. tcost (isort xs >>= insert x)
   -- { defn. of (>>=) }
  ==. tcost (isort xs) + tcost (insert x (tval (isort xs)))
   ? isortCost xs
  <=. length xs * length xs + tcost (insert x (tval (isort xs)))
   -- { tcost (insert x (tval (isort xs))) <= length xs }
  <=. length xs * length xs + length xs
   -- { + length xs + 1 }
  <=. 1 + length xs * length xs + 2 * length xs
   -- { arithmetic }
  ==. (length xs + 1) * (length xs + 1)
   -- { defn. of length }
  ==. length (x : xs) * length (x : xs)
  *** QED

--
-- Extrinsic cost analysis for 'isort'.
-- Linear upper bound when the list is already sorted.
--

isortCostSorted :: Ord a => [a] -> Proof
{-@ isortCostSorted
  :: Ord a
  => xs: OList a
  -> { tcost (isort' xs) <= length xs }
@-}
isortCostSorted []  = ()
isortCostSorted [x] = ()
isortCostSorted (x : (xs@(y : ys)))
  =   tcost (isort' (x : xs))
   -- { defn. of isort' }
  ==. tcost (leqBind (length xs) (isort' xs) (insert x))
   -- { defn. of leqBind }
  ==. tcost (isort' xs) + tcost (insert x (tval (isort' xs)))
   ? isortSortedVal xs
  ==. tcost (isort' xs) + tcost (insert x xs)
   ? isortCostSorted xs
  <=. length xs + tcost (wait (x : y : ys))
   -- { defn. of tcost }
  <=. length xs + 1
   -- { defn. of length }
  <=. length (x : xs)
  *** QED

-- Lemmas: --------------------------------------------------------------------

--
-- @tval . isort'@ is an identity on @xs@ if the list is sorted.
--
{-@ isortSortedVal
  :: Ord a
  => xs : OList a
  -> { tval (isort' xs) == xs }
@-}
isortSortedVal :: Ord a => [a] -> Proof
isortSortedVal []  = ()   -- ple
isortSortedVal [x] = ()   -- ple
isortSortedVal (x : xs)
  =   tval (isort' (x : xs))
   -- { defn. of isort }
  ==. tval (leqBind (length xs) (isort' xs) (insert x))
   -- { defn. of leqBind }
  ==. tval (insert x (tval (isort' xs)))
   ? isortSortedVal xs
  ==. tval (insert x xs)
   -- { defn. of insert }
  ==. (x : xs)
  *** QED

-------------------------------------------------------------------------------
-- | Other functions:
-------------------------------------------------------------------------------

{-@ head :: { xs:[a] | 0 < length xs } -> a @-}
head :: [a] -> a
head (x : _) = x

--
-- Quadratic upper bound because the analysis treats 'isort' as monolithic.
-- See 'NonStrictInsertionSort.hs' for more precise analysis.
--
{-@ minimum
  :: Ord a
  => { xs : [a] | 0 < length xs }
  -> { t:Tick a | tcost t <= length xs * length xs }
@-}
minimum :: Ord a => [a] -> Tick a
minimum xs = pure head <*> isort' xs