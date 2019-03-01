
{- NonStrictInsertionSort 12/08/00 -}

--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
-- Martin A.T. Handley, Niki Vazou, and Graham Hutton.
--

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple"            @-}

module NonStrictInsertionSort where

import Prelude hiding ( (>>=), (<*>), pure, return )

import RTick
import ProofCombinators
import LazyLists
import Lists
import Erasure

--
-- Non-strict insertion sort.
--

-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

{-@ reflect linsert @-}
{-@ linsert
  :: Ord a
  => a
  -> OLList a
  -> { t:Tick (OLList a) | tcost t <= 1 }
@-}
linsert :: Ord a => a -> LList a -> Tick (LList a)
linsert x Nil  = return (Cons x (return Nil))
linsert x (Cons y ys)
  | x <= y    = wait (Cons x (return (Cons y ys)))
  | otherwise = wait (Cons y (ys >>= linsert x))

{-@ reflect lisort @-}
{-@ lisort
  :: Ord a
  => xs:[a]
  -> { t:Tick (OLList a) | tcost t <= length xs }
@-}
lisort :: Ord a => [a] -> Tick (LList a)
lisort []       = return Nil
lisort (x : xs) = leqBind 1 (lisort xs) (linsert x)

-------------------------------------------------------------------------------
-- | Proofs:
-------------------------------------------------------------------------------

{-@ linsertLength :: Ord a => x:a -> xs:OLList a
    -> { llength (tval (linsert x xs)) == 1 + llength xs }
@-}
linsertLength :: Ord a => a -> LList a -> Proof
linsertLength x xs@Nil
  =   llength (tval (linsert x Nil))
  ==. llength (tval (return (Cons x (return Nil))))
  ==. llength (tval (Tick 0 (Cons x (return Nil))))
  ==. llength (Cons x (return Nil))
  ==. 1
  ==. 1 + llength Nil
  *** QED
linsertLength x xs@(Cons y ys) | x <= y
  =   llength (tval (linsert x (Cons y ys)))
  ==. llength (tval (wait (Cons x (return (Cons y ys)))))
  ==. llength (tval (Tick 0 (Cons x (return (Cons y ys)))))
  ==. llength (Cons x (return (Cons y ys)))
  ==. llength (Cons x (Tick 0 (Cons y ys)))
  ==. 1 + llength (Cons y ys)
  *** QED
linsertLength x xs@(Cons y ys) | x > y
  =   llength (tval (linsert x (Cons y ys)))
  ==. llength (tval (wait (Cons y (ys >>= linsert x))))
  ==. llength (tval (Tick 0 (Cons y (ys >>= linsert x))))
  ==. llength (Cons y (ys >>= linsert x))
  ==. llength (Cons y (let Tick o w = ys in Tick o w >>= linsert x))
  ==. llength (Cons y (let Tick o w = ys in let Tick p q = linsert x w in Tick (o + p) q))
   ? linsertLength x (tval ys)
  ==. 1 + 1 + llength (tval ys)
  ==. 1 + llength xs
  *** QED

-------------------------------------------------------------------------------
-- | Other functions:
-------------------------------------------------------------------------------

{-@ lminimum
  :: Ord a
  => { xs:[a] | 0 < length xs }
  -> { t:Tick a | tcost t <= length xs }
@-}
lminimum :: Ord a => [a] -> Tick a
lminimum xs = pure lhead <*> lisort xs