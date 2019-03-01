{-  POPL'17 Radicek et al. -}
{-  ISort  16/11/69 -}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module BoolExpr where
import Prelude hiding (return, (>>=), pure, sort, (<*>), length)
import Lists
{-@ infix :   @-}
{-@ infix </> @-}
import RTick
import Erasure

import ProofCombinators
import Language.Haskell.Liquid.Bag

{-@ ple theorem @-}
theorem :: Ord a => [a] -> [a] -> Proof
{-@ theorem :: Ord a => l1:[a] -> l2:{[a] | length l1 == length l2}
            -> { tcost (isort l1) - tcost (isort l2) <= unsortedDiff l1 l2 } @-}
theorem [] []
  = ()
theorem (x1:xs1) (x2:xs2)
  = theorem xs1 xs2
  ? lemma x1 (getISortVal xs1)
  ? lemma_preservation x1 xs1
  ? lemma x2 (getISortVal xs2)
  ? lemma_preservation x2 xs2


{-@ ple lemma @-}
lemma :: Ord a => a -> [a] -> Proof
{-@ lemma :: Ord a => x:a -> xs:(OList a) -> { tcost (insert x xs) == largerThan x xs } @-}
lemma _ [] = ()
lemma x (y:ys)
  | x <= y
  = lemma1 x (castLEqCons x y ys)
  | otherwise
  =  lemma x ys

castLEqCons :: Ord a => a -> a -> [a] -> [a]
{-@ castLEqCons :: Ord a => x:a -> y':{a | x <= y'} -> ys':(OList {v:a | y' <= v }) -> {o:OList {v:a | x <= v } | o == y':ys'} @-}
castLEqCons x y' ys' = y':ys'

getISortVal :: Ord a => [a] -> [a]
{-@ getISortVal :: Ord a => xs:[a] -> {o:OList a | length o == length xs &&  o == tval (isort xs)} @-}
getISortVal xs = tval (isort xs)

{-@ ple lemma1 @-}
lemma1 :: Ord a => a -> [a] -> Proof
{-@ lemma1 :: Ord a => x:a -> xs:(OList {v:a | x <= v}) -> {largerThan x xs == 0 } @-}
lemma1 _ [] = ()
lemma1 x (_:xs) = lemma1 x xs

{-@ ple lemma_preservation @-}
lemma_preservation :: Ord a => a -> [a] -> Proof
{-@ lemma_preservation :: Ord a => x:a -> xs:[a] -> {largerThan x xs == largerThan x (tval (isort xs))} / [length xs] @-}
lemma_preservation x []     = ()
lemma_preservation x (y:ys) = preservation_insert x y (getISortVal ys) ? lemma_preservation x ys


{-@ ple preservation_insert @-}
preservation_insert :: Ord a => a -> a -> [a] -> Proof
{-@ preservation_insert :: Ord a => x:a -> y:a -> ys:(OList a)
                        -> { largerThan x (y:ys) == largerThan x (tval (insert y ys)) } @-}
preservation_insert _ _ [] = ()
preservation_insert x y (z:zs)
  | y <= z
  =   largerThan x (tval (insert y (z:zs)))
  ==. largerThan x (tval (return (y:z:zs)))
  ==. largerThan x (y:z:zs)
  *** QED
preservation_insert x y (z:zs)
  | not (y <= z) && (x <= z)
  =   largerThan x (tval (insert y (z:zs)))
  ==! largerThan x (tval ((pure (z:)) </> insert y zs))
  ==! largerThan x ((tval (pure (z:))) (tval (insert y zs)))
  ==! largerThan x (z:(tval (insert y zs)))
  ==! largerThan x (tval (insert y zs))
      ? preservation_insert x y zs
  ==! largerThan x (y:zs)
  ==! (if x <= y then largerThan x zs else 1 + largerThan x zs)
  ==! (if x <= y then largerThan x (z:zs) else 1 + largerThan x (z:zs))
  ==! largerThan x (y:z:zs)
  *** QED
  | otherwise
  =   largerThan x (tval (insert y (z:zs)))
      -- NV CHECK: the following steps could not be checked, so left them uncheck
  ==! largerThan x (tval ((pure (z:)) </> insert y zs))
  ==! largerThan x ((tval (pure (z:))) (tval (insert y zs)))
  ==! largerThan x (z:(tval (insert y zs)))
  ==! 1 + largerThan x (tval (insert y zs))
      ? preservation_insert x y zs
  ==! 1 + largerThan x (y:zs)
  ==! 1 + (if x <= y then largerThan x zs else 1 + largerThan x zs)
  ==! (if x <= y then largerThan x (z:zs) else 1 + largerThan x (z:zs))
  ==! largerThan x (y:z:zs)
  *** QED



{-@ reflect isort @-}
isort :: Ord a => [a] -> Tick [a]
{-@ isort :: Ord a => xs:[a] -> Tick {os:(OList a) | length os == length xs && fromList os == fromList xs } @-}
isort [] = return []
isort (x:xs) = isort xs >/= insert x


{-@ reflect insert @-}
insert :: Ord a => a -> [a] -> Tick [a]
{-@ insert :: Ord a => x:a -> xs:(OList a)
  -> Tick {os:(OList a) | length os == 1 + length xs && fromList os == put x (fromList xs)} @-}
insert x [] = return [x]
insert x (y:ys)
  | x <= y    = return (x:y:ys)
  | otherwise = (pure (y:)) </> insert x ys

{-@ reflect unsortedDiff @-}
unsortedDiff :: Ord a => [a] -> [a] -> Int
unsortedDiff l1 l2 = unsorted l1 - unsorted l2

{-@ reflect sorted @-}
sorted :: Ord a => [a] -> Bool
sorted xs = unsorted xs == 0

{-@ reflect unsorted @-}
unsorted :: Ord a => [a] -> Int
unsorted [] = 0
unsorted (x:xs) = largerThan x xs + unsorted xs

{-@ reflect largerThan @-}
largerThan :: Ord a => a -> [a] -> Int
largerThan _ [] = 0
largerThan x (y:ys)
  | x <= y    = largerThan x ys
  | otherwise = 1 + largerThan x ys