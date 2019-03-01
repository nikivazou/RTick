
module Log2 where

import ProofCombinators

assumption = () 
--
-- Define an abstract measure called 'log'
-- LH knows nothing about its implementation
--
{-@ measure log :: a -> a @-}

--
-- log_2 rounded to the nearest integer
--
{-@ assume log :: x:Int -> {v:Int | v == log x } @-}
log :: Int -> Int
log x = round (logBase 2 (fromIntegral x))

--
-- Assume that log_2 1 == 0
--
{-@ assume logOne :: { log 1 == 0 } @-}
logOne :: Proof
logOne  = assumption
--
-- Assume that log_2 == 1
--
{-@ assume logTwo :: { log 2 == 1 } @-}
logTwo :: Proof
logTwo  = assumption


{-@ assume logNat :: x:{ Int | 0 <= x } -> { 0 <= log x } @-}
logNat :: Int -> Proof
logNat _ = assumption

{-@ assume logPos :: x:{ Int | 1 < x } -> { 0 < log x } @-}
logPos :: Int -> Proof
logPos _ = assumption

--
-- Log ratio law: log_b (x / y) == log_b x - log_b y
--
{-@ assume logDiv :: x:Int -> y:Int -> {log (x / y) = log x - log y } @-}
logDiv :: Int -> Int -> Proof
logDiv _ _ = assumption

--
-- Log ratio law: log_b (x + y) == log_b x + log_b (1+y/x)
--
{-@ assume logPlus :: x:Int -> y:Int -> {log (x + y) = log x + log (1 + y/x) } @-}
logPlus :: Int -> Int -> Proof
logPlus _ _ = assumption