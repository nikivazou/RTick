
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
-- Martin A.T. Handley, Niki Vazou, and Graham Hutton.
--

{-@ LIQUID "--reflection" @-}
{-@ infix ++              @-}

module FreeAppend where

import Prelude hiding ( (++), pure )

import RTick
import ProofCombinators
import Lists
import Append
import Erasure

--
-- The 'tval' function can be used to discard resource usage. This is
-- exemplified by 'freeAppend' below.
--
-- Users of the library should, therefore, /not/ use 'tval' (or 'tcost') inside
-- programs whose resource usage is being analysed. Furthermore, users should
-- not perform case analysis on the 'Tick' data constructor.
--
-- Resource usage should only be modified by the functions defined in the
-- 'RTick' module.
--

--
-- Notice: @tcost t == length xs@.
--
{-@ reflect realAppend @-}
{-@ realAppend :: xs:[a] -> ys:[a]
    -> { t:Tick { zs:[a] | length xs + length ys == length zs }
         | tcost t == length xs }
@-}
realAppend :: [a] -> [a] -> Tick [a]
realAppend xs ys = xs ++ ys

--
-- Notice: @tcost t == 0@.
--
{-@ reflect freeAppend @-}
{-@ freeAppend :: xs:[a] -> ys:[a]
    -> { t:Tick { zs:[a] | length xs + length ys == length zs }
         | tval t == tval (xs ++ ys) && tcost t == 0 }
@-}
freeAppend :: [a] -> [a] -> Tick [a]
freeAppend xs ys = pure (tval (xs ++ ys))