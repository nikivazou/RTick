{- Square And Multiply 13/5/4 -}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Counters where

{-@ infix <*> @-}
{-@ infix :   @-}

import RTick
import ProofCombinators
import Lists
import Prelude hiding (return, (>>=), pure, length, (<*>))
import Erasure

theorem :: Int -> Int -> [Int] -> [Int] -> Proof
{-@ theorem :: t:Nat -> x:Int -> l1:{[Int] | 0 < length l1} -> l2:{[Int] | length l1 == length l2 }
    -> { tcost (sam t x l1) - tcost (sam t x l2) <= t * (diff l1 l2)} @-}
theorem _ _ [_] [_] = ()
theorem t x (l1:ls1@(_:_)) (l2:ls2@(_:_)) -- explicitly say that the tails are not empty
  = theorem t x ls1 ls2

{-@ reflect diff @-}
{-@ diff :: l1:[Int] -> l2:{[Int] | length l1 == length l2 } -> Int @-}
diff :: [Int] -> [Int] -> Int
diff [] [] = 0
diff (x:xs) (y:ys) = (if x == y then 0 else 1) + diff xs ys

{-@ reflect sam @-}
sam :: Int -> Int -> [Int] -> Tick Int
{-@ sam :: t:Nat -> Int -> bs:{[Int] | 0 < length bs } -> Tick Int @-}
sam t x [b] = return (if x == 0 then 1 else x)
sam t x (b:bs) | b == 0 = pure power2 <*> sam t x bs
sam t x (b:bs)          = sam t x bs  >>= power2Times t x


{-@ reflect power2Times @-}
{-@ power2Times :: Nat -> Int -> Int -> Tick Int @-}
power2Times :: Int -> Int -> Int -> Tick Int
power2Times t x s = waitN t (multiply x (power2 s))

{-@ reflect multiply @-}
multiply :: Int -> Int -> Int
multiply x y = x * y

{-@ reflect power2 @-}
power2 :: Int -> Int
power2 x = x * x