-- 5 / 18 / 45

{-@ LIQUID "--reflection" @-}
{- LIQUID "--ple-local"   @-}

module Tree where

import Prelude hiding
  ( Functor(..)
  , Applicative(..)
  , Monad(..)
  , (++)
  , length
  )

import RTick
import ProofCombinators
import Append
import Arithmetic
import Erasure
import Lists

--
-- Flattening a tree to a list. Throughout this file the cost model is the
-- number of recursive calls.
--

-------------------------------------------------------------------------------
-- | Datatype:
-------------------------------------------------------------------------------

data Tree = Leaf Int | Node Tree Tree

-- Perfect binary tree
{-@ type PTree = { t:Tree | perfect t } @-}

{-@ measure leftChild @-}
{-@ leftChild :: { p:PTree | 0 < height p } -> PTree @-}
leftChild :: Tree -> Tree
leftChild (Node l _) = l

{-@ measure rightChild @-}
{-@ rightChild :: { p:PTree | 0 < height p } -> PTree @-}
rightChild :: Tree -> Tree
rightChild (Node _ r) = r

-------------------------------------------------------------------------------
-- | Measures:
-------------------------------------------------------------------------------

{-@ measure size @-}
{-@ size :: Tree -> { v:Int | 0 < v} @-}
size :: Tree -> Int
size Leaf{} = 1
size (Node l r) = 1 + size l + size r

{-@ measure nodes @-}
{-@ nodes :: Tree -> Nat @-}
nodes :: Tree -> Int
nodes Leaf{}     = 0
nodes (Node l r) = 1 + nodes l + nodes r

{-@ measure leaves @-}
{-@ leaves :: Tree -> {v:Int | 0 < v} @-}
leaves :: Tree -> Int
leaves Leaf{}     = 1
leaves (Node l r) = leaves l + leaves r

{-@ measure height @-}
{-@ height :: Tree -> Nat @-}
height :: Tree -> Int
height Leaf{} = 0
height (Node l r)
  | hl > hr   = 1 + hl
  | otherwise = 1 + hr
  where
    hl = height l
    hr = height r

{-@ measure perfect @-}
{-@ perfect :: Tree -> Bool @-}
perfect :: Tree -> Bool
perfect Leaf{}     = True
perfect (Node l r) = perfect l && perfect r && size l == size r

-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

{-@ measure flatten @-}
{-@ flatten :: t:Tree -> Tick { xs:[Int] | leaves t == length xs } / [size t, 0]
@-}
flatten :: Tree -> Tick [Int]
flatten (Leaf n)   = return [n]
flatten (Node l r) = flatten l >>= flattenRest r

{-@ reflect flattenRest @-}
{-@ flattenRest :: t:Tree -> xs:[Int] -> Tick { ys:[Int]
    | length ys == leaves t + length xs } / [size t, 1]
@-}
flattenRest :: Tree -> [Int] -> Tick [Int]
flattenRest r xs = flatten r >>= (xs ++)

-------------------------------------------------------------------------------
-- | Cost proofs:
-------------------------------------------------------------------------------

-- Naive flatten:

{-@ flattenCost :: p:PTree
    -> { tcost (flatten p) <= height p * (leaves p / 2) } / [size p, 0]
@-}
flattenCost :: Tree -> Proof
flattenCost p@(Leaf n)
  =   tcost (flatten p)
   -- { defn. of flatten }
  ==. tcost (return [n])
   -- { defn. of return }
  ==. tcost (Tick 0 [n])
   -- { defn. of tcost }
  ==. 0
   -- { arithmetic }
  ==. 0 * (1 `div` 2)
   -- { defn. of height }
  ==. height p * (1 `div` 2)
   -- { defn. of leaves }
  ==. height p * (leaves p `div` 2)
  *** QED
flattenCost p@(Node l r)
  = tcost (flatten p)
   -- { defn. of flatten }
  ==. tcost (flatten l >>= flattenRest r)
   -- { defn. of (>>=) }
  ==. tcost (flatten l)
       + tcost (flattenRest r (tval (flatten l)))
   ? flattenCost l
  <=. height l * (leaves l `div` 2)
        + tcost (flattenRest r (tval (flatten l)))
   ? flattenRestCost r (tval (flatten l))
  <=. height l * (leaves l `div` 2)
        + height r * (leaves r `div` 2) + length (tval (flatten l))
   -- { length (tval (flatten l)) == leaves l }
  <=. height l * (leaves l `div` 2)
        + height r * (leaves r `div` 2) + leaves l
   -- { arithmetic }
  ==. leaves l
        + height l * (leaves l `div` 2)
        + height r * (leaves r `div` 2)
   ? mulDiv (height l) (leaves l)
   ? mulDiv (height r) (leaves r)
  ==. leaves l
        + ((height l * leaves l) `div` 2)
        + ((height r * leaves r) `div` 2)
   ? lemma1 p
   ? lemma3 p
   ? (height l ==. height r *** QED)
   ? (leaves l ==. leaves r *** QED)
  ==. leaves l
        + height l * (leaves l `div` 2)
        + height l * (leaves l `div` 2)
   ? addTwoDivTwo (height l) (leaves l)
  ==. leaves l + height l * leaves l
   -- { height p = 1 + height l }
  ==. leaves l + (height p - 1) * leaves l
   -- { arithmetic }
  ==. leaves l + height p * leaves l - leaves l
   -- { arithmetic }
  ==. height p * leaves l
   ? (leaves p ==. 2 * leaves l   *** QED)
   ? (leaves p `div` 2  ==. leaves l *** QED)
   -- { leaves p = 2 * leaves l }
  ==. height p * (leaves p `div` 2)
  *** QED

{-@ flattenRestCost :: p:PTree -> xs:[Int]
    -> { tcost (flattenRest p xs) <= height p * (leaves p / 2) + length xs } / [size p, 1]
@-}
flattenRestCost :: Tree -> [Int] -> Proof
flattenRestCost p xs
  =   tcost (flattenRest p xs)
   -- { defn. of tcost }
  ==. tcost (flatten p >>= (xs ++))
   -- { defn. of (>>=) }
  ==. tcost (flatten p) + tcost (xs ++ tval (flatten p))
   ? flattenCost p
  <=. height p * (leaves p `div` 2) + tcost (xs ++ tval (flatten p))
   -- { tcost (xs ++ tval (flatten p)) == length xs }
  ==. height p * (leaves p `div` 2) + length xs
  *** QED

-- Optimised flatten: ---------------------------------------------------------

{-@ reflect flattenOpt @-}
{-@ flattenOpt :: t:Tree -> xs:[Int] -> Tick { os:[Int]
  | length os == leaves t + length xs } @-}
flattenOpt :: Tree -> [Int] -> Tick [Int]
flattenOpt (Leaf n)   ns = return (n : ns)
flattenOpt (Node l r) ns = flattenOpt l =/< flattenOpt r ns

--
-- Cost in terms of number of leaves.
--
{-@ flattenOptCost :: t:Tree -> xs:[Int]
    -> { tcost (flattenOpt t xs) == leaves t - 1 }
@-}
flattenOptCost :: Tree -> [Int] -> Proof
flattenOptCost (Leaf n) ns
  =   tcost (flattenOpt (Leaf n) ns)
   -- { defn. of flattenOpt }
  ==. tcost (return (n : ns))
   -- { defn. of return }
  ==. tcost (Tick 0 (n : ns))
   -- { defn. of tcost }
  ==. 0
   -- { arithmetic }
  ==. 1 - 1
   -- { defn. of leaves }
  ==. leaves (Leaf n) - 1
  *** QED
flattenOptCost (Node l r) ns
  =   tcost (flattenOpt (Node l r) ns)
   -- { defn. of flattenOpt }
  ==. tcost (flattenOpt l =/< flattenOpt r ns)
   -- { defn. of (=/<) }
  ==. 1 + tcost (flattenOpt r ns) + tcost (flattenOpt l (tval (flattenOpt r ns)))
   ? flattenOptCost r ns
  ==. 1 + leaves r - 1 + tcost (flattenOpt l (tval (flattenOpt r ns)))
   ? flattenOptCost l (tval (flattenOpt r ns))
  ==. 1 + leaves r - 1 + leaves l - 1
   -- { arithmetic }
  ==. leaves r + leaves l - 1
   -- { leaves (Node l r) == leaves l + leaves r }
  ==. leaves (Node l r) - 1
  *** QED

--
-- Cost in terms of height of tree.
-- Note: tree must be perfect in this case.
--
{-@ flattenOptCost2 :: t:PTree -> xs:[Int]
    -> { tcost (flattenOpt t xs) == twoToPower (height t) - 1 }
@-}
flattenOptCost2 :: Tree -> [Int] -> Proof
flattenOptCost2 p@(Leaf n) ns
  =   tcost (flattenOpt (Leaf n) ns)
   -- { defn. of flattenOpt }
  ==. tcost (return (n : ns))
   -- { defn. of return }
  ==. tcost (Tick 0 (n : ns))
   -- { defn. of tcost }
  ==. 0
   -- { arithmetic }
  ==. 1 - 1
   -- { 2^0 == 1 }
  ==. twoToPower 0 - 1
   -- { defn. of height }
  ==. twoToPower (height p) - 1
  *** QED
flattenOptCost2 p@(Node l r) ns
  =   tcost (flattenOpt (Node l r) ns)
   -- { defn. of flattenOpt }
  ==. tcost (flattenOpt l =/< flattenOpt r ns)
   -- { defn. of (=/<) }
  ==. 1 + tcost (flattenOpt r ns) + tcost (flattenOpt l (tval (flattenOpt r ns)))
   ? flattenOptCost2 r ns
  ==. 1 + twoToPower (height r) - 1 + tcost (flattenOpt l (tval (flattenOpt r ns)))
   ? flattenOptCost2 l (tval (flattenOpt r ns))
  ==. 1 + twoToPower (height r) - 1 + twoToPower (height l) - 1
   ? lemma1 p
  ==. 1 + twoToPower (height l) - 1 + twoToPower (height l) - 1
   -- { arithmetic }
  ==. twoToPower (height l) + twoToPower (height l) - 1
   -- { 2^x + 2^x = 2 * 2^x = 2^(x + 1) }
  ==. twoToPower (height l + 1) - 1
   -- { height p == height l + 1 }
  ==. twoToPower (height p) - 1
  *** QED

-- Lemmas: --------------------------------------------------------------------

{-@ lemma0 :: t1:PTree  -> t2:PTree
    -> { (size t1 == size t2) => (height t1 == height t2) } / [size t1]
@-}
lemma0 :: Tree -> Tree -> Proof
lemma0 (Leaf _) (Leaf _)   = () -- trivial
lemma0 (Leaf _) (Node _ _) = () -- assumption is false
lemma0 (Node _ _) (Leaf _) = () -- assumption is false
lemma0 t1@(Node l1 r1) t2@(Node l2 r2) | size t1 == size t2
  =   height t1
  ==. (if hl1 > hr1 then 1 + hl1 else 1 + hr1)
   ? lemma0 l1 r1
   ? (hl1 == hl2 *** QED)
  ==. 1 + hl1
   ? ((size t1 == size t2)
         ==. (1 + size l1 + size r1 == 1 + size l2 + size r2)
         ==. (1 + 2 * size l1       == 1 + 2 * size l2)
         ==. (size l1 == size l2)
          ? lemma0 l1 l2
         ==. (hl1 == hl2)
         *** QED)
  ==. 1 + hl2
   ? lemma0 l2 r2
  ==. (if hl2 > hr2 then 1 + hl2 else 1 + hr2)
  ==. height t2
  *** QED
  where
    hl1 = height l1
    hl2 = height l2
    hr1 = height r1
    hr2 = height r2
lemma0 _ _ = () -- assumption is false

{-@ lemma1 :: { p : PTree | 0 < height p }
    -> { height (leftChild p) == height (rightChild p) } / [size p]
@-}
lemma1 :: Tree -> Proof
lemma1 p@(Node l r)
  =   height (leftChild p)
  ==. height l
   ? lemma0 l r
  ==. height r
  ==. height (rightChild  p)
      *** QED
lemma1 _ = ()

{-@ lemma2 :: t1:PTree  -> t2:PTree
    -> { (size t1 == size t2) => (leaves t1 == leaves t2) } / [size t1]
@-}
lemma2 :: Tree -> Tree -> Proof
lemma2 (Leaf _) (Leaf _)   = () -- trivial
lemma2 (Leaf _) (Node _ _) = () -- assumption is false
lemma2 (Node _ _) (Leaf _) = () -- assumption is false
lemma2 t1@(Node l1 r1) t2@(Node l2 r2) | size t1 == size t2
  =   leaves t1
  ==. leaves l1 + leaves r1
   ? lemma2 l1 r1
   ? lemma2 l2 r2
   ? (ll1 == ll2 *** QED)
   ? (lr1 == lr2 *** QED)
   ? ((size t1 == size t2)
        ==. (1 + size l1 + size r1 == 1 + size l2 + size r2)
        ==. (1 + 2 * size l1       == 1 + 2 * size l2)
        ==. (size l1 == size l2)
         ? lemma2 l1 l2
        ==. (ll1 == ll2)
        *** QED)
   ? ((size t1 == size t2)
        ==. (1 + size l1 + size r1 == 1 + size l2 + size r2)
        ==. (1 + 2 * size r1       == 1 + 2 * size r2)
        ==. (size r1 == size r2)
         ? lemma2 l1 l2
        ==. (lr1 == lr2)
        *** QED)
  ==. leaves l2 + leaves r2
  ==. leaves t2
  *** QED
  where
    ll1 = leaves l1
    ll2 = leaves l2
    lr1 = leaves r1
    lr2 = leaves r2
lemma2 _ _ = () -- assumption is false

{-@ lemma3 :: { p:PTree | height p > 0 }
    -> { leaves (leftChild p) == leaves (rightChild p) }
@-}
lemma3 :: Tree -> Proof
lemma3 p@(Node l r)
  =   leaves (leftChild p)
  ==. leaves l
   ? lemma2 l r
  ==. leaves r
  ==. leaves (rightChild  p)
  *** QED
lemma3 _ = ()

-- Arithmetic assumptions: ----------------------------------------------------

{-@ assume addTwoDivTwo :: x:Int -> y:Int
    -> { (x * (y / 2)) + (x * (y / 2)) == x * y }
@-}
addTwoDivTwo :: Int -> Int -> Proof
addTwoDivTwo _ _ = ()

{-@ assume mulDiv :: x:Int -> y:Int
    -> { x * (y / 2) == (x * y) / 2 }
@-}
mulDiv :: Int -> Int -> Proof
mulDiv _ _ = ()