
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
-- Martin A.T. Handley, Niki Vazou, and Graham Hutton.
--

{-@ LIQUID "--reflection" @-}
{-@ infix >>=             @-}
{-@ infix ++              @-}

module Reverse where

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
import Lists
import Append
import Erasure

--
-- Reversing lists. Throughout this file the cost model is the number
-- of recursive calls.
--

-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

--
-- Requires extrinsic cost analysis.
--
{-@ reflect reverse @-}
{-@ reverse :: xs:[a] -> Tick { zs:[a] | length xs == length zs } @-}
reverse :: [a] -> Tick [a]
reverse []       = return []
reverse (x : xs) = reverse xs >/= snoc x

--
-- Intrinsic cost analysis works using 'leqBind'.
--
{-@ reverse' :: xs:[a]
    -> { t:Tick { zs:[a] | length xs == length zs }
         | tcost t <= length xs * length xs }
@-}
reverse' :: [a] -> Tick [a]
reverse' []       = return []
reverse' (x : xs) = leqBind (length xs) (step 1 (reverse' xs)) (snoc x)

{-@ reflect reverseApp @-}
{-@ reverseApp :: xs:[a] -> ys:[a]
    -> Tick { zs:[a] | length xs + length ys == length zs }
@-}
reverseApp :: [a] -> [a] -> Tick [a]
reverseApp xs ys = reverse xs >>= postApp ys

-------------------------------------------------------------------------------

{-@ reflect fastReverse @-}
{-@ fastReverse :: xs:[a]
    -> { t:Tick { zs:[a] | length xs == length zs }
         | tcost t == length xs }
@-}
fastReverse :: [a] -> Tick [a]
fastReverse xs = reverseCat xs []

{-@ reflect reverseCat @-}
{-@ reverseCat :: xs:[a] -> ys:[a]
    -> { t:Tick { zs:[a] | length xs + length ys == length zs }
         | tcost t == length xs }
@-}
reverseCat :: [a] -> [a] -> Tick [a]
reverseCat [] ys       = pure ys
reverseCat (x : xs) ys = step 1 (reverseCat xs (x : ys))

-------------------------------------------------------------------------------
-- | Cost proofs:
-------------------------------------------------------------------------------

--
-- Note: the precise execution cost of @reverse xs@ is
-- @((length xs * length xs) / 2) + (length xs / 2)@.
--
{-@ reverseCost :: xs:[a] -> { tcost (reverse xs) <= length xs * length xs } @-}
reverseCost :: [a] -> Proof
reverseCost []
  =   tcost (reverse [])
   -- { defn. of reverse }
  ==. tcost (return [])
   -- { defn. of return }
  ==. tcost (Tick 0 [])
   -- { defn. of tcost }
  ==. 0
   -- { arithmetic }
  ==. 0 * 0
   -- { defn. of length }
  ==. length [] * length []
  *** QED
reverseCost (x : xs)
  =   tcost (reverse (x : xs))
   -- { defn. of reverse }
  ==. tcost (reverse xs >/= snoc x)
   -- { defn. of (>/=) }
  ==. 1 + tcost (reverse xs) + tcost (snoc x (tval (reverse xs)))
   ? reverseCost xs
  <=. 1 + (length xs * length xs) + tcost (snoc x (tval (reverse xs)))
   ? snocCost x (reverse xs)
  ==. 1 + (length xs * length xs) + length (tval (reverse xs))
   -- { length (tval (reverse xs)) == length xs }
  ==. 1 + (length xs * length xs) + length xs
   -- { + length xs, commutativity of (+) }
  <=. (length xs * length xs) + 2 * length xs + 1
   -- { arithmetic }
  ==. (1 + length xs) * (1 + length xs)
   -- { defn. of length }
  ==. length (x : xs) * length (x : xs)
  *** QED

--
-- Note: the precise execution cost of @reverseApp xs ys@ is
-- @((lxs * lxs) / 2) + (lxs / 2) + lxs@
-- where @lxs = length xs@ and @lys = length ys@.
--
{-@ reverseAppCost :: xs:[a] -> ys:[a]
    -> { tcost (reverseApp xs ys) <= (length xs * length xs) + length xs }
@-}
reverseAppCost :: [a] -> [a] -> Proof
reverseAppCost xs ys
  =   tcost (reverseApp xs ys)
   -- { defn. of reverseApp }
  ==. tcost (reverse xs >>= postApp ys)
   -- { defn. of (>>=) }
  ==. tcost (reverse xs) + tcost (postApp ys (tval (reverse xs)))
   ? reverseCost xs
  <=. length xs * length xs + tcost (postApp ys (tval (reverse xs)))
   -- { tcost (postApp ys (tval (reverse xs))) == length xs }
  <=. length xs * length xs + length xs
  *** QED

-------------------------------------------------------------------------------
-- | Improvement proofs:
-------------------------------------------------------------------------------

{-@ singletonQImp :: x:a -> { QIMP (reverse [x]) 1 (pure [x]) } @-}
singletonQImp :: a -> Proof
singletonQImp x
  =    reverse [x]
   -- { defn. of reverse }
  <=>. reverse [] >/= snoc x
   -- { defn. of reverse  }
  <=>. return [] >/= snoc x
   -- { defn. of return }
  <=>. Tick 0 [] >/= snoc x
   -- { defn. of (>/=) }
  <=>. (let Tick n y = snoc x [] in Tick (1 + 0 + n) y)
   -- { arithmetic }
  <=>. (let Tick n y = snoc x [] in Tick (1 + n) y)
   -- { defn. of snoc }
  <=>. (let Tick n y = [] ++ [x] in Tick (1 + n) y)
   -- { defn. of (++) }
  <=>. (let Tick n y = pure [x] in Tick (1 + n) y)
   -- { defn. of pure }
  <=>. (let Tick n y = Tick 0 [x] in Tick (1 + n) y)
   -- { inline let }
  <=>. Tick (1 + 0) [x]
   -- { arithmetic }
  <=>. Tick 1 [x]
  .>== 1 ==>. Tick 0 [x]
   -- { defn. of pure }
  <=>. pure [x]
  ***  QED

--
-- List reversal distributes contravariantly over list append. This is an
-- interesting example because in the base case, i.e., when @length xs == 0@,
-- @xs ++ ys >>= reverse@ costs /less/ than @reverse xs >>= reverseApp ys@
-- (by @length ys@, see 'distributivityNilQImp'). Hence in this case,
-- @xs ++ ys >>= reverse@ is an improvement. However, in all other cases,
-- i.e., when @length xs > 0@, @reverse xs >>= reverseApp ys@ is the cheaper
-- option. Thus, overall we say that replacing @xs ++ ys >>= reverse@ with
-- @reverse xs >>= reverseApp ys@ is an improvement.
--

{-@ distributivityNilQImp :: { xs:[a] | length xs == 0 } -> ys:[a]
    -> { QIMP (reverse xs >>= reverseApp ys) (length ys) (xs ++ ys >>= reverse) }
@-}
distributivityNilQImp :: [a] -> [a] -> Proof
distributivityNilQImp [] ys
  =    reverse [] >>= reverseApp ys
   -- { defn. of reverse }
  <=>. return [] >>= reverseApp ys
   -- { defn. of return }
  <=>. Tick 0 [] >>= reverseApp ys
   -- { defn. of (>>=) }
  <=>. (let Tick o w = reverseApp ys [] in Tick (0 + o) w)
   -- { arithmetic }
  <=>. (let Tick o w = reverseApp ys [] in Tick o w)
   -- { defn. of reverseApp }
  <=>. (let Tick o w = reverse ys >>= postApp [] in Tick o w)
   ? nilPostApp (reverse ys)
  .>== length ys ==>. (let Tick o w = reverse ys in Tick o w)
   -- { arithmetic }
  <=>. (let Tick o w = reverse ys in Tick (0 + o) w)
   -- { defn. of (>>=) }
  <=>. Tick 0 ys >>= reverse
   -- { defn. of pure }
  <=>. pure ys >>= reverse
   -- { defn. of (++) }
  <=>. [] ++ ys >>= reverse
  ***  QED

{-@ distributivityQImp :: xs:[a] -> ys:[a]
    -> { QIMP (xs ++ ys >>= reverse) ((length ys * (length xs - 1)) + length xs) (reverse xs >>= reverseApp ys) }
@-}
distributivityQImp :: [a] -> [a] -> Proof
distributivityQImp [] ys
  =    [] ++ ys >>= reverse
   -- { defn. of (++) }
  <=>. pure ys >>= reverse
   -- { defn. of pure }
  <=>. Tick 0 ys >>= reverse
   -- { defn. of (>>=) }
  <=>. (let Tick o w = reverse ys in Tick (0 + o) w)
   -- { arithmetic }
  <=>. (let Tick o w = reverse ys in Tick o w)
   ? nilPostApp (reverse ys)
   -- { (length ys * (length xs - 1)) + length xs = - length ys }
  .<== length ys ==<. (let Tick o w = reverse ys >>= postApp [] in Tick o w)
   -- { defn. of reverseApp }
  <=>. (let Tick o w = reverseApp ys [] in Tick o w)
   -- { arithmetic }
  <=>. (let Tick o w = reverseApp ys [] in Tick (0 + o) w)
   -- { defn. of (>>=) }
  <=>. Tick 0 [] >>= reverseApp ys
   -- { defn. of return }
  <=>. return [] >>= reverseApp ys
   -- { defn. of reverse }
  <=>. reverse [] >>= reverseApp ys
  ***  QED
distributivityQImp (x : xs) ys
  =    (x : xs) ++ ys >>= reverse
   -- { defn. of (++) }
  <=>. (pure (cons x) </> (xs ++ ys)) >>= reverse
   -- { defn. of pure }
  <=>. (Tick 0 (cons x) </> (xs ++ ys)) >>= reverse
   -- { introduce let }
  <=>. (Tick 0 (cons x) </> (let Tick o p = xs ++ ys in Tick o p)) >>= reverse
   -- { float (</>) inside let }
  <=>. (let Tick o w = xs ++ ys in Tick 0 (cons x) </> Tick o w) >>= reverse
   -- { defn. of (</>) }
  <=>. (let Tick o w = xs ++ ys in Tick (1 + 0 + o) (cons x w)) >>= reverse
   -- { arithmetic }
  <=>. (let Tick o w = xs ++ ys in Tick (1 + o) (cons x w)) >>= reverse
   -- { float reverse inside (>>=) }
  <=>. (let Tick o w = xs ++ ys in Tick (1 + o) (cons x w) >>= reverse)
   -- { defn. of cons }
  <=>. (let Tick o w = xs ++ ys in Tick (1 + o) (x : w) >>= reverse)
   -- { defn. of (>>=) }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = reverse (x : w) in Tick (0 + 1 + o + p) v)
   -- { arithmetic }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = reverse (x : w) in Tick (1 + o + p) v)
   -- { defn. of reverse }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = reverse w >/= snoc x in Tick (1 + o + p) v)
  .>== 1 ==>. (let Tick o w = xs ++ ys in let Tick p v = reverse w >/= snoc x in Tick (o + p) v)
   -- { defn. of (>/=) }
  <=>. (let Tick o w = xs ++ ys in let Tick p v = reverse w in let Tick q u = snoc x v in Tick (1 + o + p + q) u)
   -- { defn. of (>>=) }
  <=>. (let Tick o w = xs ++ ys >>= reverse in let Tick p v = snoc x w in Tick (1 + o + p) v)
   ? distributivityQImp xs ys
  .>== length ys * (length xs - 1) + length xs ==>. (let Tick o w = reverse xs >>= reverseApp ys in let Tick p v = snoc x w in Tick (1 + o + p) v)
   -- { defn. of (>>=), renaming }
  <=>. (let Tick o w = reverse xs in let Tick p v = reverseApp ys w in let Tick q u = snoc x v in Tick (1 + o + p + q) u)
   -- { defn. of reverseApp }
  <=>. (let Tick o w = reverse xs in let Tick p v = reverse ys >>= postApp w in let Tick q u = snoc x v in Tick (1 + o + p + q) u)
   -- { defn. of (>>=), renaming }
  <=>. (let Tick o w = reverse xs in let Tick p v = reverse ys in let Tick q u = postApp w v in let Tick r t = snoc x u in Tick (1 + o + p + q + r) t)
   -- { defn. of postApp }
  <=>. (let Tick o w = reverse xs in let Tick p v = reverse ys in let Tick q u = v ++ w in let Tick r t = snoc x u in Tick (1 + o + p + q + r) t)
   -- { defn. of snoc }
  <=>. (let Tick o w = reverse xs in let Tick p v = reverse ys in let Tick q u = v ++ w in let Tick r t = u ++ [x] in Tick (1 + o + p + q + r) t)
   -- { defn. of postApp }
  <=>. (let Tick o w = reverse xs in let Tick p v = reverse ys in let Tick q u = v ++ w in let Tick r t = postApp [x] u in Tick (1 + o + p + q + r) t)
   -- { defn. of (>>=) }
  <=>. (let Tick o w = reverse xs in let Tick p v = reverse ys in let Tick q u = v ++ w >>= postApp [x] in Tick (1 + o + p + q) u)
   ? assocQImp (tval (reverse ys)) (tval (reverse xs)) [x]
  .>== length ys ==>. (let Tick o w = reverse xs in let Tick p v = reverse ys in let Tick q u = w ++ [x] >>= preApp v in Tick (1 + o + p + q) u)
   -- { defn. of (>>=) }
  <=>. (let Tick o w = reverse xs in let Tick p v = reverse ys in let Tick q u = w ++ [x] in let Tick r t = preApp v u in Tick (1 + o + p + q + r) t)
   -- { defn. of snoc }
  <=>. (let Tick o w = reverse xs in let Tick p v = reverse ys in let Tick q u = snoc x w in let Tick r t = preApp v u in Tick (1 + o + p + q + r) t)
   -- { defn. of (>/=) }
  <=>. (let Tick o w = reverse xs >/= snoc x in let Tick p v = reverse ys in let Tick r t = preApp v w in Tick (o + p + r) t)
   ? appSwap (tval (reverse ys)) (tval (reverse xs))
  <=>. (let Tick o w = reverse xs >/= snoc x in let Tick p v = reverse ys in let Tick r t = postApp w v in Tick (o + p + r) t)
   -- { defn. of (>>=) }
  <=>. (let Tick o w = reverse xs >/= snoc x in let Tick p v = reverse ys >>= postApp w in Tick (o + p) v)
   -- { defn. of reverseApp }
  <=>. (let Tick o w = reverse xs >/= snoc x in let Tick p v = reverseApp ys w in Tick (o + p) v)
   -- { defn. of reverse }
  <=>. (let Tick o w = reverse (x : xs) in let Tick p v = reverseApp ys w in Tick (o + p) v)
   -- { defn. of (>>=) }
  <=>. reverse (x : xs) >>= reverseApp ys
  ***  QED

--
-- Reversing a list twice gives back the same result but requires
-- @(length xs * length xs) + length xs@ recursive calls to 'reverse' and
-- '(++')'.
--
{-@ involutionQImp :: xs:[a]
    -> { QIMP (reverse xs >>= reverse) ((length xs * length xs) + length xs) (pure xs) }
@-}
involutionQImp :: [a] -> Proof
involutionQImp []
  =    reverse [] >>= reverse
   -- { defn. of reverse }
  <=>. return [] >>= reverse
   -- { defn. of pure }
  <=>. Tick 0 [] >>= reverse
   -- { defn. of (>>=) }
  <=>. (let Tick n y = reverse [] in Tick (0 + n) y)
   -- { arithmetic }
  <=>. (let Tick n y = reverse [] in Tick n y)
   -- { defn. of reverse }
  <=>. (let Tick n y = return [] in Tick n y)
   -- { defn. of return }
  <=>. (let Tick n y = Tick 0 [] in Tick n y)
   -- { inline let }
  <=>. Tick 0 []
  .>== (length [] * length []) + length [] ==>. Tick 0 []
   -- { defn. of pure }
  <=>. pure []
  ***  QED
involutionQImp (x : xs)
  =    reverse (x : xs) >>= reverse
   -- { defn. of reverse }
  <=>. (reverse xs >/= snoc x) >>= reverse
   -- { introduce let }
  <=>. (let Tick o w = reverse xs >/= snoc x in Tick o w) >>= reverse
   -- { float (>>=) inside let }
  <=>. (let Tick o w = reverse xs >/= snoc x in Tick o w >>= reverse)
   -- { defn. of (>>=) }
  <=>. (let Tick o w = reverse xs >/= snoc x in let Tick p v = reverse w in Tick (o + p) v)
   -- { defn. of (>/=), renaming }
  <=>. (let Tick o w = reverse xs in let Tick p v = snoc x w in let Tick q u = reverse v in Tick (1 + o + p + q) u)
  .>== 1 ==>. (let Tick o w = reverse xs in let Tick p v = snoc x w in let Tick q u = reverse v in Tick (o + p + q) u)
   -- { defn. of snoc }
  <=>. (let Tick o w = reverse xs in let Tick p v = w ++ [x] in let Tick q u = reverse v in Tick (o + p + q) u)
   -- { defn. of (>>=) }
  <=>. (let Tick o w = reverse xs in let Tick p v = w ++ [x] >>= reverse in Tick (o + p) v)
   ? distributivityQImp (tval (reverse xs)) [x]
  .>== (length [x] * (length xs - 1)) + length xs ==>. (let Tick o w = reverse xs in let Tick p v = reverse w >>= reverseApp [x] in Tick (o + p) v)
   -- { defn. of (>>=) }
  <=>. (let Tick o w = reverse xs in let Tick p v = reverse w in let Tick q u = reverseApp [x] v in Tick (o + p + q) u)
   -- { defn. of (>>=), renaming }
  <=>. (let Tick o w = reverse xs >>= reverse in let Tick p v = reverseApp [x] w in Tick (o + p) v)
   ? involutionQImp xs
  .>== (length xs * length xs) + length xs ==>. (let Tick o w = pure xs in let Tick p v = reverseApp [x] w in Tick (o + p) v)
   -- { defn. of pure }
  <=>. (let Tick o w = Tick 0 xs in let Tick p v = reverseApp [x] w in Tick (o + p) v)
    -- { inline let }
  <=>. (let Tick p v = reverseApp [x] xs in Tick p v)
   -- { defn. of reverseApp }
  <=>. (let Tick p v = reverse [x] >>= postApp xs in Tick p v)
   -- { defn. of (>>=), renaming }
  <=>. (let Tick o w = reverse [x] in let Tick p v = postApp xs w in Tick (o + p) v)
   ? singletonQImp x
  <=>. (let Tick o w = pure [x] in let Tick p v = postApp xs w in Tick (1 + o + p) v)
  .>== 1 ==>. (let Tick o w = pure [x] in let Tick p v = postApp xs w in Tick (o + p) v)
   -- { defn. of pure }
  <=>. (let Tick o w = Tick 0 [x] in let Tick p v = postApp xs w in Tick (o + p) v)
   -- { inline let }
  <=>. (let Tick p v = postApp xs [x] in Tick p v)
   ? postAppSingleton xs x
  <=>. (let Tick p v = pure (cons x xs) in Tick (1 + p) v)
  .>== 1 ==>. (let Tick p v = pure (cons x xs) in Tick p v)
   -- { defn of pure }
  <=>. (let Tick p v = Tick 0 (x : xs) in Tick p v)
   -- { inline let }
  <=>. Tick 0 (x : xs)
   -- { defn. of pure }
  <=>. pure (x : xs)
  ***  QED

-- Lemmas: --------------------------------------------------------------------

{-@ postAppSingleton :: xs:[a] -> x:a
    -> { postApp xs [x] ==  Tick 1 (cons x xs) }
@-}
postAppSingleton :: [a] -> a -> Proof
postAppSingleton xs x
  =   postApp xs [x]
   -- { defn. of postApp }
  ==. [x] ++ xs
   -- { defn. of (++) }
  ==. pure (cons x) </> ([] ++ xs)
   -- { def. of (++) }
  ==. pure (cons x) </> pure xs
   -- { defn. of pure }
  ==. Tick 0 (cons x) </> Tick 0 xs
   -- { defn. of (</>) }
  ==. Tick 1 (cons x xs)
  *** QED

-------------------------------------------------------------------------------
-- | Erasure proofs:
-------------------------------------------------------------------------------
--
-- We prove that erasing the annotations from 'reverse' gives back
-- the standard reverse function.
--

-- Functions: -----------------------------------------------------------------

{-@ reflect rev @-}
{-@ rev :: [a] -> [a] @-}
rev :: [a] -> [a]
rev []       = []
rev (x : xs) = app (rev xs) [x]

-- Proofs: --------------------------------------------------------------------

{-@ reverse_erase :: xs:[a] -> { erase (reverse xs) == rev xs } @-}
reverse_erase :: [a] -> Proof
reverse_erase []
  =   erase (reverse [])
   -- { defn. of reverse }
  ==. erase (return [])
   ? erase_return []
  ==. []
   -- { defn. of rev }
  ==. rev []
  *** QED
reverse_erase (x : xs)
  =   erase (reverse (x : xs))
   -- { defn. of reverse }
  ==. erase (reverse xs >/= snoc x)
   ? reverse_erase xs
   ? snoc_erase x (rev xs)
   ? erase_wbind (snoc' x) (rev xs) (reverse xs) (snoc x)
  ==. snoc' x (rev xs)
   -- { defn. of snoc' }
  ==. app (rev xs) [x]
   -- { defn. of rev }
  ==. rev (x : xs)
  *** QED

-- Lemmas: --------------------------------------------------------------------

--
-- 'snoc' with no annotations.
--
{-@ reflect snoc' @-}
{-@ snoc' :: a -> [a] -> [a] @-}
snoc' :: a -> [a] -> [a]
snoc' x xs = app xs [x]

{-@ snoc_erase :: x:a -> xs:[a]
    -> { erase (snoc x xs) == snoc' x xs }
@-}
snoc_erase :: a -> [a] -> Proof
snoc_erase x xs
  =   erase (snoc x xs)
   -- { defn. of snoc }
  ==. erase (xs ++ [x])
   ? append_erase xs [x]
  ==. app xs [x]
   -- { defn. of snoc' }
  ==. snoc' x xs
  *** QED