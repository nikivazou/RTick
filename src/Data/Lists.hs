{-@ LIQUID "--reflection" @-}
module Data.Lists where 

import Prelude hiding (length)
{-@ infix   :   @-}

{-@ measure length @-}
length :: [a] -> Int 
length [] = 0 
length (x:xs) = 1 + length xs     

{-@ reflect cons @-}
{-@ cons :: x:a -> xs:[a] -> {z:[a] | z == x:xs} @-}
cons :: a -> [a] -> [a]
cons x xs = x:xs