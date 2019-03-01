
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
--

--
-- tcost (xs ++ ys) == length xs
--
-- Exec:  (++): 4, snoc: 2, cons: 2  = 8
-- Spec:                             = 3
-- Proof:                            = 0
--
-- Total: 8, 3, 0
--
-------------------------------------------------------------------------------
--
-- Append's monoid laws:
--
-- Exec:  (++): 4, snoc: 2, cons: 2, preApp: 2, postApp: 2        = 12
-- Spec:  leftIdCostEq: 1, rightIdQImp: 4,  assocQImp: 2          = 7
-- Proof: leftIdCostEq: 7, rightIdQImp: 11, assocQImp: 42         = 60
--
--
-- Lemmas: leftIdCostEq: N/A,
--         rightIdQImp:  N/A,
--         assocQImp:    leftId, nilPreApp
--
-- Exec:  leftId: 0 (no new lines), nilPreApp: 0 (no new lines)   = 0
-- Spec:  leftId: 2, nilPreApp: 1                                 = 3
-- Proof: leftId: 4, nilPreApp: 10                                = 14
--
--
-- Total: 12, 10, 74
--

{-@ LIQUID "--reflection" @-}
{-@ infix >>=             @-}

module Append where

import Prelude hiding
  ( Functor(..)
  , Applicative(..)
  , Monad(..)
  , (++)
  , length
  )

import RTick
import ProofCombinators
import Lists
import Erasure

--
-- Some proofs about Haskell's append function. Throughout this file the cost
-- model is the number of recursive calls.
--

-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

{-@ reflect ++ @-}
{-@ infix   ++ @-}
{-@ (++) :: xs:[a] -> ys:[a]
    -> { t:Tick { os:[a] | length os == length xs + length ys }
         | tcost t == length xs }
@-}
(++) :: [a] -> [a] -> Tick [a]
[]       ++ ys = pure ys
(x : xs) ++ ys = pure (cons x)         {- Tick <\i -> i == 0> (a -> b) -}
                    </> (xs ++ ys)     {- Tick <\i -> i == len xs> a)  -}

--
-- We define 'snoc' because Liquid Haskell doesn't like @(++ [x])@ in
-- some proofs.
--
{-@ reflect snoc @-}
{-@ snoc :: x:a -> xs:[a]
    -> { t:Tick { os:[a] | length os == 1 + length xs }
         | tcost t == length xs }
@-}
snoc :: a -> [a] -> Tick [a]
snoc x xs = xs ++ [x]

--
-- We define 'preApp' because Liquid Haskell doesn't like @(xs ++)@ in
-- some proofs.
--
{-@ reflect preApp @-}
{-@ preApp :: xs:[a] -> ys:[a]
    -> { t:Tick { os:[a] | length os == length xs + length ys }
         | tcost t == length xs }
@-}
preApp :: [a] -> [a] -> Tick [a]
preApp xs ys = xs ++ ys

--
-- We define 'postApp' because Liquid Haskell doesn't like @(++ ys)@ in
-- some proofs.
--
{-@ reflect postApp @-}
{-@ postApp :: ys:[a] -> xs:[a]
    -> { t:Tick { os:[a] | length os == length xs + length ys }
         | tcost t == length xs }
@-}
postApp :: [a] -> [a] -> Tick [a]
postApp ys xs = xs ++ ys

-------------------------------------------------------------------------------
-- | Cost proofs:
-------------------------------------------------------------------------------

--
-- Note: Liquid Haskell can intrinsically verify this execution cost. See
-- the specification of '(++)'.
--
{-@ appendCost :: xs:[a] -> ys:[a] -> { tcost (xs ++ ys) == length xs } @-}
appendCost :: [a] -> [a] -> Proof
appendCost [] ys
  =   tcost ([] ++ ys)
   -- { defn. of (++) }
  ==. tcost (pure ys)
   -- { defn. of pure }
  ==. tcost (Tick 0 ys)
   -- { defn. of tcost }
  ==. 0
   -- { defn. of length }
  ==. length []
  *** QED
appendCost (x : xs) ys
  =   tcost ((x : xs) ++ ys)
   -- { defn. of (++) }
  ==. tcost (pure (x:) </> (xs ++ ys))
   -- { cost of (</>) }
  ==. 1 + tcost (pure (x:)) + tcost (xs ++ ys)
   -- { defn. of pure }
  ==. 1 + tcost (Tick 0 (x:)) + tcost (xs ++ ys)
   -- { defn. of tcost }
  ==. 1 + 0 + tcost (xs ++ ys)
   -- { arithmetic }
  ==. 1 + tcost (xs ++ ys)
   ? appendCost xs ys
  ==. 1 + length xs
   -- { defn. of length }
  ==. length (x : xs)
  *** QED

{-@ snocCost :: x:a -> t:Tick [a]
    -> { tcost (snoc x (tval t)) == length (tval t) }
@-}
snocCost :: a -> Tick [a] -> Proof
snocCost x t
  =   tcost (snoc x (tval t))
  ==. length (tval t)
  *** QED

--
-- Append's left identity law.
--
{-@ leftId :: ys:[a]
    -> { tcost ([] ++ ys) == 0 &&
         tval  ([] ++ ys) == ys }
@-}
leftId :: [a] -> Proof
leftId ys
  =   ([] ++ ys)
   -- { defn. of (++) }
  <=>. pure ys
   -- { defn. of pure }
  <=>. Tick 0 ys
  ***  QED

--
-- Append's right identity law.
--
{-@ rightId :: xs:[a] -> { (xs ++ []) == Tick (length xs) xs } @-}
rightId :: [a] -> Proof
rightId []
  =    [] ++ []
   -- { defn. of (++) }
  <=>. pure []
   -- { defn. of pure }
  <=>. Tick 0 []
   -- { defn. of length }
  <=>. Tick (length []) []
  ***  QED
rightId (x : xs)
  =   (x : xs) ++ []
   -- { defn. of (++) }
  <=>. pure (cons x) </> (xs ++ [])
   ? rightId xs
  <=>. pure (cons x) </> Tick (length xs) xs
   -- { defn. of pure }
  <=>. Tick 0 (cons x) </> Tick (length xs) xs
   -- { defn. of (</>) }
  <=>. Tick (1 + length xs) (cons x xs)
   -- { defn. of length }
  <=>. Tick (length (x : xs)) (x : xs)
  *** QED

--
-- Associativity.
--

{-@ assocLeft :: xs:[a] -> ys:[a] -> zs:[a]
    -> { tcost (xs ++ ys >>= postApp zs) == 2 * length xs + length ys  }
@-}
assocLeft :: [a] -> [a] -> [a] -> Proof
assocLeft xs ys zs
  =   tcost (xs ++ ys >>= postApp zs)
   -- { defn. of >>= }
  ==. tcost (xs ++ ys) + tcost (postApp zs (tval (xs ++ ys)))
   -- { tcost (xs ++ ys) == length xs }
  ==. length xs + tcost (postApp zs (tval (xs ++ ys)))
   -- { defn. of postApp }
  ==. length xs + tcost (tval (xs ++ ys) ++ zs)
   -- { tcost (xs ++ ys) == length xs }
  ==. length xs + length (tval (xs ++ ys))
   -- { length xs ++ ys = length xs + length ys }
  ==. length xs + length xs + length ys
   -- { arithmetic }
  ==. 2 * length xs + length ys
  *** QED

{-@ assocRight :: xs:[a] -> ys:[a] -> zs:[a]
    -> { tcost (ys ++ zs >>= preApp xs) == length ys + length xs }
@-}
assocRight :: [a] -> [a] -> [a] -> Proof
assocRight xs ys zs
  =   tcost (ys ++ zs >>= preApp xs)
   -- { defn. of >>= }
  ==. tcost (ys ++ zs) + tcost (preApp xs (tval (ys ++ zs)))
   -- { tcost (ys ++ zs) == length ys }
  ==. length ys + tcost (preApp xs (tval (ys ++ zs)))
   -- { defn. of preApp }
  ==. length ys + tcost (xs ++ tval (ys ++ zs))
   -- { tcost (xs ++ tval (ys ++ zs)) == length xs }
  ==. length ys + length xs
   -- { commutativity of + }
  ==. length xs + length ys
  *** QED

-------------------------------------------------------------------------------
-- | Improvement proofs:
-------------------------------------------------------------------------------

--
-- Append's left identity law.
--
{-@ leftIdCostEq :: ys:[a] -> { COSTEQ ([] ++ ys) (pure ys) } @-}
leftIdCostEq :: [a] -> Proof
leftIdCostEq ys
  =   [] ++ ys
   ? leftId ys
  <=>. Tick 0 ys
   -- { defn. of pure }
  <=>. pure ys
  *** QED

--
-- Append's right identity law.
--
{-@ rightIdQImp :: xs:[a] -> { QIMP (xs ++ []) (length xs) (pure xs) } @-}
rightIdQImp :: [a] -> Proof
rightIdQImp xs
  =   xs ++ []
   ? rightId xs
  <=>. Tick (length xs) xs
  .>== length xs ==>. Tick 0 xs
   -- { defn. of pure }
  <=>. pure xs
  *** QED

{-@ rightIdQImp' :: xs:[a] -> { QIMP (xs ++ []) (length xs) (pure xs) } @-}
rightIdQImp' :: [a] -> Proof
rightIdQImp' []
  =    [] ++ []
   -- { defn. of (++) }
  <=>. pure []
  ***  QED
rightIdQImp' (x : xs)
  =    (x : xs) ++ []
   -- { defn. of (++) }
  <=>. pure (cons x) </> (xs ++ [])
   ? rightIdQImp' xs
  .>== length xs ==>. pure (cons x) </> pure xs
   -- { defn. of pure }
  <=>. Tick 0 (cons x) </> Tick 0 xs
   -- { defn. of (</>) }
  <=>. Tick 1 (cons x xs)
   -- { defn. of cons }
  <=>. Tick 1 (x : xs)
  .>== 1 ==>. Tick 0 (x : xs)
   -- { defn. of pure }
  <=>. pure (x : xs)
  ***  QED

{-@ rightIdQDim :: xs:[a] -> { QDIM (pure xs) (length xs) (xs ++ []) } @-}
rightIdQDim :: [a] -> Proof
rightIdQDim []
  =    pure []
   -- { defn. of (++) }
  <=>. [] ++ []
  ***  QED
rightIdQDim (x : xs)
  =    pure (x : xs)
   -- { defn. of pure }
  <=>. Tick 0 (x : xs)
   -- { quantified diminishment: 1 }
  .<== 1 ==<. Tick 1 (x : xs)
   -- { defn. of cons }
  <=>. Tick 1 (cons x xs)
   -- { defn. of (</>) }
  <=>. Tick 0 (cons x) </> Tick 0 xs
   -- { defn. of pure }
  <=>. pure (cons x) </> pure xs
   ? rightIdQDim xs
   -- { quantified diminishment: length xs }
  .<== length xs ==<. pure (cons x) </> (xs ++ [])
   -- { defn. of (++) }
  <=>. (x : xs) ++ []
  ***  QED

{-@ assocQImp :: xs:[a] -> ys:[a] -> zs:[a]
    -> { QIMP (xs ++ ys >>= postApp zs) (length xs) (ys ++ zs >>= preApp xs) }
@-}
assocQImp :: [a] -> [a] -> [a] -> Proof
assocQImp [] ys zs
  =    [] ++ ys >>= postApp zs
   ? leftId ys
  <=>. pure ys >>= postApp zs
   -- { defn. of pure }
  <=>. Tick 0 ys >>= postApp zs
   -- { defn. of (>>=) }
  <=>. (let Tick o u = postApp zs ys in Tick (0 + o) u)
   -- { defn. of postApp }
  <=>. (let Tick o u = ys ++ zs in Tick (0 + o) u)
  .>== length [] ==>. (let Tick o u = ys ++ zs in Tick o u)
   -- { inline let }
  <=>. ys ++ zs
   ? nilPreApp (ys ++ zs)
  <=>. ys ++ zs >>= preApp []
  ***  QED
assocQImp (x : xs) ys zs
  =    (x : xs) ++ ys >>= postApp zs
   -- { defn. of (++) }
  <=>. pure (cons x) </> (xs ++ ys) >>= postApp zs
   -- { defn. of pure }
  <=>. (Tick 0 (cons x) </> (xs ++ ys)) >>= postApp zs
   -- { introduce let }
  <=>. (Tick 0 (cons x) </> (let Tick o p = xs ++ ys in Tick o p)) >>= postApp zs
   -- { float (</>) inside let }
  <=>. (let Tick o w = xs ++ ys in Tick 0 (cons x) </> Tick o w) >>= postApp zs
   -- { defn. of (</>) }
  <=>. (let Tick o w = xs ++ ys in Tick (1 + 0 + o) (cons x w)) >>= postApp zs
   -- { arithmetic }
  <=>. (let Tick o w = xs ++ ys in Tick (1 + o) (cons x w)) >>= postApp zs
   -- { float postApp zs inside (>>=) }
  <=>. (let Tick o w = xs ++ ys in Tick (1 + o) (cons x w) >>= postApp zs)
   -- { defn. of cons }
  <=>. (let Tick o w = xs ++ ys in Tick (1 + o) (x : w) >>= postApp zs)
   -- { defn. of >>= }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = postApp zs (x : w) in Tick (0 + 1 + o + p) v)
   -- { arithmetic }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = postApp zs (x : w) in Tick (1 + o + p) v)
   -- { defn. of postApp }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = (x : w) ++ zs in Tick (1 + o + p) v)
   -- { defn. of (++) }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = pure (cons x) </> (w ++ zs) in Tick (1 + o + p) v)
  .>== 1 ==>. (let Tick o w = xs ++ ys in let Tick p v = pure (cons x) </> (w ++ zs) in Tick (o + p) v)
   -- { defn. of postApp }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = pure (cons x) </> postApp zs w in Tick (o + p) v)
   -- { defn. of pure }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = Tick 0 (cons x) </> postApp zs w in Tick (o + p) v)
   -- { introduce let }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = postApp zs w in Tick (1 + 0 + o + p) (cons x v))
   --  { arithmetic }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = postApp zs w in Tick (1 + o + p) (cons x v))
   -- { defn. of (>>=) }
  <=>. (let Tick o w = xs ++ ys >>= postApp zs in Tick (1 + o) (cons x w))
   ? assocQImp xs ys zs
  .>== length xs ==>. (let Tick o w = ys ++ zs >>= preApp xs in Tick (1 + o) (cons x w))
   -- { defn. of (>>=) }
  <=>. (let Tick o w = ys ++ zs in let Tick p v = preApp xs w in Tick (1 + o + p) (cons x v))
   -- { defn. of preApp }
  <=>. (let Tick o w = ys ++ zs in let Tick p v = xs ++ w in Tick (1 + o + p) (cons x v))
   -- { defn. of (</>) }
  <=>. (let Tick o w = ys ++ zs in let Tick p v = pure (cons x) </> (xs ++ w) in Tick (o + p) v)
   -- { defn. of (++) }
  <=>. (let Tick o w = ys ++ zs in let Tick p v = (x : xs) ++ w in Tick (o + p) v)
   -- { defn. of preApp }
  <=>. (let Tick o w = ys ++ zs in let Tick p v = preApp (x : xs) w in Tick (o + p) v)
   -- { defn. of (>>=) }
  <=>. (ys ++ zs) >>= preApp (x : xs)
  ***  QED

-- Lemmas: --------------------------------------------------------------------

{-@ nilPreApp :: t:Tick [a] -> { t >>= preApp [] == t } @-}
nilPreApp :: Tick [a] -> Proof
nilPreApp (Tick m xs)
  =    Tick m xs >>= preApp []
   -- { defn. of >>= }
  <=>. (let Tick n y = preApp [] xs in Tick (n + m) y)
   -- { defn. of preApp }
  <=>. (let Tick n y = [] ++ xs in Tick (n + m) y)
   ? leftId xs
  <=>. (let Tick n y = Tick 0 xs in Tick (n + m) y)
   -- { inline let }
  <=>. Tick (0 + m) xs
   -- { arithmetic }
  <=>. Tick m xs
  ***  QED

{-@ nilPostApp :: t:Tick [a] -> { QIMP (t >>= postApp []) (length (tval t)) t } @-}
nilPostApp :: Tick [a] -> Proof
nilPostApp (Tick m xs)
  =    (Tick m xs >>= postApp []
   -- { defn. of >>= }
  <=>. (let Tick n y = postApp [] xs in Tick (n + m) y)
   -- { defn. of postApp }
  <=>. (let Tick n y = xs ++ [] in Tick (n + m) y)
   -- { quantified improvement: length xs }
   ? rightIdQImp xs
  .>== length xs ==>. (let Tick n y = pure xs in Tick (n + m) y))
   -- { defn. of pure }
  <=>. (let Tick n y = Tick 0 xs in Tick (n + m) y)
   -- { inline let }
  <=>. Tick (0 + m) xs
   -- { arithmetic }
  <=>. Tick m xs
  ***  QED

{-@ appSwap :: xs:[a] -> ys:[a] -> { preApp xs ys == postApp ys xs } @-}
appSwap :: [a] -> [a] -> Proof
appSwap xs ys
  =   preApp xs ys
   -- { defn. of preApp }
  ==. xs ++ ys
   -- { defn. of postApp }
  ==. postApp ys xs
  *** QED

-------------------------------------------------------------------------------
-- | Erasure proofs:
-------------------------------------------------------------------------------
--
-- We prove that erasing the annotations from '(++)' returns the standard
-- append function.
--

-- Functions: -----------------------------------------------------------------

{-@ reflect app @-}
{-@ app :: [a] -> [a] -> [a] @-}
app :: [a] -> [a] -> [a]
app []       ys = ys
app (x : xs) ys = x : app xs ys

-- Proofs: --------------------------------------------------------------------

{-@ append_erase :: xs:[a] -> ys:[a] -> { erase (xs ++ ys) == app xs ys } @-}
append_erase :: [a] -> [a] -> Proof
append_erase [] ys
  =   erase ([] ++ ys)
   -- { defn. of (++) }
  ==. erase (pure ys)
   ? erase_pure ys
  ==. ys
   -- { defn. of app }
  ==. app [] ys
  *** QED
append_erase (x : xs) ys
  =   erase ((x : xs) ++ ys)
   -- { defn. of (++) }
  ==. erase (pure (cons x) </> (xs ++ ys))
   ? append_erase xs ys
   ? erase_pure (cons x)
   ? erase_wapp (cons x) (app xs ys) (pure (cons x)) (xs ++ ys)
  ==. cons x (app xs ys)
   -- { defn. of cons }
  ==. x : app xs ys
   -- { defn. of app }
  ==. app (x : xs) ys
  *** QED