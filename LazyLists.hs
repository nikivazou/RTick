
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
-- Martin A.T. Handley, Niki Vazou, and Graham Hutton.
--

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt"     @-}

module LazyLists where

import RTick

--
-- Lazy lists.
--

-------------------------------------------------------------------------------
-- | Datatype:
-------------------------------------------------------------------------------

data LList a = Nil | Cons { lhead :: a, ltail :: Tick (LList a) }

{-@ data LList a <p :: a -> a -> Bool > = Nil
      | Cons {lhead :: a, ltail :: Tick (LList <p> (a<p lhead>))} @-}

{-@ type OLList a = LList <{\x v -> x <= v }> a @-}

-------------------------------------------------------------------------------
-- | Measures:
-------------------------------------------------------------------------------

{-@ measure llength @-}
{-@ llength :: LList a -> Nat @-}
llength :: LList a -> Int
llength Nil = 0
llength (Cons _ (Tick _ t)) = 1 + llength t