
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
--

--
-- tcost (reverse xs) == ((length xs * length xs) / 2) + ((length xs + 1) / 2)
--
-- Exec:   reverse: 3, snoc: 2, (++): 4  = 9
-- Spec:   reverseCost: 7                = 7
-- Proofs: reverseCost: 22               = 22
--
-- Total: 9, 7, 22
--
-------------------------------------------------------------------------------
--
-- (reverse xs >>= postApp ys) >~> t && tcost t == length xs
--
-- Exec:   reverse: 3, snoc: 2, (++): 4  = 9
-- Spec:   reverseApp: 6                 = 6
-- Proofs: reverseApp2: 36               = 36
--
-- Cost proofs: reverseCost, reverseAppCost,
--
-- Exec:   reverseCost: 0,  reverseAppCost: 0  = 0
-- Spec:   reverseCost: 7,  reverseAppCost: 6  = 13
-- Proofs: reverseCost: 21, reverseAppCost: 7  = 28
--
-- Lemmas: assocQImp, appSwap, snocCost,  distrPlus1Div2
--
-- Exec:  assocQImp: 0,  appSwap: 0, snocCost: 0, distrPlus1Div2: 0   = 0
-- Spec:  assocQImp: 6,  appSwap: 3, snocCost: 4, distrPlus1Div2: 6   = 19
-- Proof: assocQImp: 37, appSwap: 3, snocCost: 2, distrPlus1Div2: 14  = 56
--
-- Total: 9, 38, 120
--
-------------------------------------------------------------------------------
--
--  reverse xs >~> t && tcost t == length xs
--
-- Exec:   reverse: 3, snoc: 2, (++): 4  = 9
-- Spec:   fastReverse: 5                = 5
-- Proofs: fastReverse: 9                = 9
--
-- Lemmas: rightIdQImp
--
-- Exec:  rightIdQImp: 0   = 0
-- Spec:  rightIdQImp: 4   = 4
-- Proof: rightIdQImp: 11  = 11
--
-- Total: 9, 9, 20
--

{-@ LIQUID "--reflection" @-}
{-@ infix >>=             @-}

module OptimisedByConstructionReverse where

import Prelude hiding
  ( Functor(..)
  , Applicative(..)
  , Monad(..)
  , (++)
  , length
  , reverse
  )

import RTick
import ProofCombinators
import Append
import Arithmetic
import Erasure
import Lists

--
-- Optimised-by-constructing reverse. Throughout this file the cost model
-- is the number of recursive calls.
--

-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

{-@ reflect reverse @-}
{-@ reverse :: xs:[a] -> Tick { zs:[a] | length xs == length zs } @-}
reverse :: [a] -> Tick [a]
reverse []       = return []
reverse (x : xs) = reverse xs >/= snoc x

-------------------------------------------------------------------------------
-- | Cost proofs:
-------------------------------------------------------------------------------

{-@ reverseCost:: xs:[a]
    -> { tcost (reverse xs) == ((length xs * length xs) / 2)
           + ((length xs + 1) / 2) }
@-}
reverseCost :: [a] -> Proof
reverseCost xs@[]
  =   tcost (reverse xs)
   -- { defn. of reverse }
  ==. tcost (return xs)
   -- { defn. of return }
  ==. tcost (Tick 0 xs)
   -- { defn. of tcost }
  ==. 0
   -- { arithmetic }
  ==. ((0 * 0) `div` 2) + (0 `div` 2)
   -- { defn. of length }
  ==. ((length xs * length xs) `div` 2) + (length xs `div` 2)
   -- { arithmetic }
  ==. ((length xs * length xs) `div` 2) + ((length xs + 1) `div` 2)
  *** QED
reverseCost xs@(z : zs)
  =   tcost (reverse xs)
   -- { defn. of reverse }
  ==. tcost (reverse zs >/= snoc z)
   -- { defn. of (>/=) }
  ==. 1 + tcost (reverse zs) + tcost (snoc z (tval (reverse zs)))
   ? reverseCost zs
  ==. 1 + ((length zs * length zs) `div` 2) + ((length zs + 1) `div` 2) + tcost (snoc z (tval (reverse zs)))
   -- { defn. of length }
   ? snocCost z (reverse zs)
  ==. 1 + ((length zs * length zs) `div` 2) + (length xs `div` 2) + length (tval (reverse zs))
   -- { length (tval (reverse zs)) == length zs }
  ==. 1 + ((length zs * length zs) `div` 2) + (length xs `div` 2) + length zs
   -- { arithmetic }
  ==. (((length zs * length zs) + (2 * length zs) + 2) `div` 2) + (length xs `div` 2)
   -- { arithmetic }
  ==. (((length zs * length zs) + (2 * length zs) + 2) `div` 2) + (length xs `div` 2)
   -- { arithmetic: x^2 + 2x + 1 == (x + 1)^2  }
  ==. (((1 + length zs) * (1 + length zs) + 1) `div` 2) + (length xs `div` 2)
   -- { defn. of length }
  ==. (((length xs * length xs) + 1) `div` 2) + (length xs `div` 2)
   ? distrPlus1Div2 (length xs)
  ==. ((length xs * length xs) `div` 2) + ((length xs + 1) `div` 2)
  *** QED

-------------------------------------------------------------------------------
-- | Specification:
-------------------------------------------------------------------------------

{-@ reflect reverseApp @-}
{-@ reverseApp :: xs:[a] -> ys:[a]
    -> { t:(Tick [a]) | IMP (reverse xs >>= postApp ys) t }
@-}
reverseApp :: [a] -> [a] -> Tick [a]
reverseApp xs ys = reverse xs >>= postApp ys

{-@ reverseAppCost :: xs:[a] -> ys:[a]
    -> { tcost (reverseApp xs ys) == ((length xs * length xs) / 2)
           + ((length xs + 1) / 2) + length xs }
@-}
reverseAppCost :: [a] -> [a] -> Proof
reverseAppCost xs ys
  =   tcost (reverseApp xs ys)
   -- { defn. of reverseApp }
  ==. tcost (reverse xs >>= postApp ys)
   -- { defn. of (>>=) }
  ==. tcost (reverse xs) + tcost (postApp ys (tval (reverse xs)))
   ? reverseCost xs
  ==. ((length xs * length xs) `div` 2) + ((length xs + 1) `div` 2) + tcost (postApp ys (tval (reverse xs)))
   -- { defn. of postApp }
  ==. ((length xs * length xs) `div` 2) + ((length xs + 1) `div` 2) + tcost (tval (reverse xs) ++ ys)
   -- { tcost (tval (reverse xs) ++ ys) == length (tval (reverse xs)) == length xs }
  ==. ((length xs * length xs) `div` 2) + ((length xs + 1) `div` 2) + length xs
  *** QED

{-@ reverseAppCost' :: xs:[a] -> ys:[a]
    -> { tcost (reverseApp xs ys) == ((length xs * length xs) / 2)
           + (((3 * length xs) + 1) / 2) }
@-}
reverseAppCost' :: [a] -> [a] -> Proof
reverseAppCost'  = reverseAppCost

-------------------------------------------------------------------------------
-- | Inequational reasoning:
-------------------------------------------------------------------------------

{-@ reverseApp2 :: xs:[a] -> ys:[a]
    -> { t:Tick [a] | IMP (reverse xs >>= postApp ys) t && tcost t == length xs }
@-}
reverseApp2 :: [a] -> [a] -> Tick [a]
reverseApp2 xs@[] ys
  =    reverse xs >>= postApp ys
   -- { defn. of reverse }
  <=>. return xs >>= postApp ys
   -- { defn. of return }
  <=>. Tick 0 xs >>= postApp ys
   -- { defn. of (>>=) }
  <=>. (let Tick n y = postApp ys xs in Tick (0 + n) y)
   -- { defn. of postApp }
  <=>. (let Tick n y = xs ++ ys in Tick (0 + n) y)
   -- { defn. of (++) }
  <=>. (let Tick n y = pure ys in Tick (0 + n) y)
   -- { defn. of pure }
  <=>. (let Tick n y = Tick 0 ys in Tick (0 + n) y)
   -- { inline let }
  <=>. Tick (0 + 0) ys
   -- { arithmetic }
  <=>. Tick 0 ys
   -- { defn. of return }
  <=>. return ys
reverseApp2 xs@(z : zs) ys
  =    reverse xs >>= postApp ys
   -- { defn. of reverse }
  <=>. (reverse zs >/= snoc z) >>= postApp ys
   -- { introduce let }
  <=>. (let Tick o w = reverse zs in Tick o w >/= snoc z) >>= postApp ys
   -- { defn. of (>/=) }
  <=>. (let Tick o w = reverse zs in let Tick p v = snoc z w in Tick (1 + o + p) v >>= postApp ys)
   -- { defn. of (>>=) }
  <=>. (let Tick o w = reverse zs in let Tick p v = snoc z w in let Tick q u = postApp ys v in Tick (1 + o + p + q) u)
   -- { record recursive call with step }
  <=>. step 1 (let Tick o w = reverse zs in let Tick p v = snoc z w in let Tick q u = postApp ys v in Tick (o + p + q) u)
   -- { defn. of snoc }
  <=>. step 1 (let Tick o w = reverse zs in let Tick p v = w ++ [z] in let Tick q u = postApp ys v in Tick (o + p + q) u)
   -- { defn. of (>>=) }
  <=>. step 1 (let Tick o w = reverse zs in let Tick p v = w ++ [z] >>= postApp ys in Tick (o + p) v)
   ? assocQImp (tval (reverse zs)) [z] ys
  .>== length zs ==>. step 1 (let Tick o w = reverse zs in let Tick p v = [z] ++ ys >>= preApp w in Tick (o + p) v)
   -- { defn. of (++) }
  <=>. step 1 (let Tick o w = reverse zs in let Tick p v = pure (cons z) </> ([] ++ ys) >>= preApp w in Tick (o + p) v)
   -- { defn. of (++) }
  <=>. step 1 (let Tick o w = reverse zs in let Tick p v = pure (cons z) </> pure ys >>= preApp w in Tick (o + p) v)
   -- { defn. of pure }
  <=>. step 1 (let Tick o w = reverse zs in let Tick p v = Tick 0 (cons z) </> Tick 0 ys >>= preApp w in Tick (o + p) v)
   -- { defn. of (</>) }
  <=>. step 1 (let Tick o w = reverse zs in let Tick p v = Tick (1 + 0 + 0) (cons z ys) >>= preApp w in Tick (o + p) v)
   -- { arithmetic }
  <=>. step 1 (let Tick o w = reverse zs in let Tick p v = Tick 1 (cons z ys) >>= preApp w in Tick (o + p) v)
   -- { quantified improvement: 1 }
  .>== 1 ==>. step 1 (let Tick o w = reverse zs in let Tick p v = Tick 0 (cons z ys) >>= preApp w in Tick (o + p) v)
   -- { defn. of cons }
  <=>. step 1 (let Tick o w = reverse zs in let Tick p v = Tick 0 (z : ys) >>= preApp w in Tick (o + p) v)
   -- { defn. of (>>=) }
  <=>. step 1 (let Tick o w = reverse zs in let Tick p v = Tick 0 (z : ys) in let Tick q u = preApp w v in Tick (o + p + q) u)
   ? appSwap (tval (reverse zs)) (z : ys)
  <=>. step 1 (let Tick o w = reverse zs in let Tick p v = Tick 0 (z : ys) in let Tick q u = postApp v w in Tick (o + p + q) u)
   -- { inline let }
  <=>. step 1 (let Tick o w = reverse zs in let Tick q u = postApp (z : ys) w in Tick (o + 0 + q) u)
   -- { arithmetic }
  <=>. step 1 (let Tick o w = reverse zs in let Tick q u = postApp (z : ys) w in Tick (o + q) u)
   -- { defn. of (>>=) }
  <=>. step 1 (reverse zs >>= postApp (z : ys))
      ? (tcost (reverse zs >>= postApp (z : ys)) ==. tcost (reverseApp zs (z : ys)) *** QED)
      ? reverseAppCost zs (z : ys)
  .>== ((length zs * length zs) `div` 2) + ((length zs + 1) `div` 2) ==>. step 1 (reverseApp2 zs (z : ys))

-- Resource usages/savings: ---------------------------------------------------

--
-- Initial usage (u)        ((length (x : xs) * length (x : xs)) `div` 2) + (((3 * length (x : xs)) + 1) `div` 2)
-- Total saving  (s)        length xs + 1 + ((length xs * length xs) `div` 2) + ((length xs + 1) `div` 2)
-- Final usage   (u - s)    length (x : xs)
--

-- Derived implementation: ----------------------------------------------------

{-@ reflect reverseApp_final @-}
{-@ reverseApp_final :: [a] -> [a] -> Tick [a] @-}
reverseApp_final :: [a] -> [a] -> Tick [a]
reverseApp_final []       ys = return ys
reverseApp_final (x : xs) ys = step 1 (reverseApp_final xs (x : ys))

-------------------------------------------------------------------------------
-- | Optimising reverse:
-------------------------------------------------------------------------------

{-@ fastReverse :: xs:[a]
    -> { t:Tick [a] | IMP (reverse xs) t && tcost t == length xs }
@-}
fastReverse :: [a] -> Tick [a]
fastReverse xs
  =    reverse xs
   -- { introduce lets }
  <=>. (let Tick o w = reverse xs in let Tick p v = pure w in Tick (o + p) v)
   ? rightIdQImp (tval (reverse xs))
  .<== length xs ==<. (let Tick o w = reverse xs in let Tick p v = w ++ [] in Tick (o + p) v)
   -- { defn. of postApp }
  <=>. (let Tick o w = reverse xs in let Tick p v = postApp [] w in Tick (o + p) v)
   -- { defn. of (>>= )}
  <=>. (reverse xs >>= postApp [])
   ? (tcost (reverse xs >>= postApp []) ==. tcost (reverseApp xs []) *** QED)
   ? reverseAppCost xs []
  .>== ((length xs * length xs) `div` 2) + ((length xs + 1) `div` 2) ==>. reverseApp2 xs []

-- Resource usages/savings: ---------------------------------------------------

--
-- Initial usage (u)        ((length xs * length xs) `div` 2) + ((length xs + 1) `div` 2)
-- Total saving  (s)        - length xs + ((length xs * length xs) `div` 2) + ((length xs + 1) `div` 2)
-- Final usage   (u - s)    length xs
--

-- Derived implementation: ----------------------------------------------------

{-@ reflect fastReverse_final @-}
{-@ fastReverse_final :: [a] -> Tick [a] @-}
fastReverse_final :: [a] -> Tick [a]
fastReverse_final xs = reverseApp_final xs []

-------------------------------------------------------------------------------
-- | Erasure calculations:
-------------------------------------------------------------------------------
--
-- Erasing the annotations gives the well-known linear reverse function.
--

{-@ revApp :: xs:[a] -> ys:[a]
    -> { zs:[a] | zs == erase (reverseApp_final xs ys) }
@-}
revApp :: [a] -> [a] -> [a]
revApp [] ys
  =   erase (reverseApp_final [] ys)
   -- { defn. of reverseApp_final }
  ==. erase (return ys)
   ? erase_return ys
  ==. ys
revApp (x : xs) ys
  =   erase (reverseApp_final (x : xs) ys)
   -- { defn. of reverseApp_final }
  ==. erase (step 1 (reverseApp_final xs (x : ys)))
   ? toProof (revApp xs (x : ys))
   ? erase_step 1 (revApp xs (x : ys)) (reverseApp_final xs (x : ys))
  ==. revApp xs (x : ys)

{-@ fastRev :: xs:[a] -> { zs:[a] | zs == erase (fastReverse_final xs) } @-}
fastRev :: [a] -> [a]
fastRev []
  =   erase (fastReverse_final [])
   -- { defn. of fastReverse_final }
  ==. erase (reverseApp_final [] [])
   -- { defn. of reverseApp_final }
  ==. erase (return [])
   ? erase_return []
  ==. []
fastRev xs
  =   erase (fastReverse_final xs)
   -- { defn. of fastReverse_final }
  ==. erase (reverseApp_final xs [])
   ? toProof (revApp xs [])
  ==. revApp xs []

-- Derived implementations: ---------------------------------------------------

{-@ reflect revApp_final @-}
{-@ revApp_final :: [a] -> [a] -> [a] @-}
revApp_final :: [a] -> [a] -> [a]
revApp_final []       ys = ys
revApp_final (x : xs) ys = revApp_final xs (x : ys)

{-@ reflect fastRev_final @-}
{-@ fastRev_final :: [a] -> [a] @-}
fastRev_final :: [a] -> [a]
fastRev_final xs = revApp_final xs []