
{-@ LIQUID "--reflection" @-}

module PowerOf2 where

import ProofCombinators

assumption = () 
    
--
-- Define an abstract measure called 'powerOf2'
-- LH knows nothing about its implementation
--
{-@ measure powerOf2 :: Int -> Bool @-}

--
-- Multiplication/division identity law: 2 * (x / 2) == x
--
{-@ assume timesDiv :: x:{ Int | powerOf2 x } -> { 2 * (x / 2) == x } @-}
timesDiv :: Int -> Proof
timesDiv _ = assumption

--
-- Assume that if x is a power of 2 then x / 2 is a power of 2
--
{-@ assume powerOf2Div2 :: x:{ Int | powerOf2 x } -> { powerOf2 (x / 2) } @-}
powerOf2Div2 :: Int -> Proof
powerOf2Div2 _ = assumption

--
-- Assume that if x is a power of 2 then (x - x / 2) is a power of 2
--
{-@ assume powerOf2Div2' :: x:{ Int | powerOf2 x } -> { powerOf2 (x - (x / 2)) } @-}
powerOf2Div2' :: Int -> Proof
powerOf2Div2' _ = assumption



{-@ assume powerOfIsEven :: x:{ Int | powerOf2 x } -> { (x mod 2 == 0) && (0 <= x/2) && powerOf2 (x / 2) && (2 <= x => (x/2 < x)) } @-}
powerOfIsEven :: Int -> Proof
powerOfIsEven _ = assumption
-------------------------------------------------------------------------------

--
-- 2^x
--
{-@ reflect twoToPower @-}
{-@ twoToPower :: Nat -> Nat @-}
twoToPower :: Int -> Int
twoToPower 0 = 1
twoToPower n = 2 * twoToPower (n - 1)