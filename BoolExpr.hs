{-  POPL'17 Radicek et al. -}
{-  Lazy ISort  28/02/13 -}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module BoolExpr where
import Prelude hiding (return, (>>=), pure, sort, (<*>), length)
import RTick
import Erasure

import ProofCombinators



data BExpr = Const Bool | And BExpr BExpr | Or BExpr BExpr


theorem :: BExpr -> Bool -> Proof
{-@ theorem :: e:BExpr -> b:{Bool | noShort e b} -> {tcost (eval1 e) == tcost (eval2 e)} @-}
theorem (Const b) _ = ()
theorem e@(And e1 e2) b
  =   theorem e1 True  ? theorem e2 b ? lemma e1 True
theorem e@(Or e1 e2) b
  = theorem e1 False ? theorem e2 b ? lemma e1 False

{-@ reflect eval1 @-}
eval1 :: BExpr -> Tick Bool
eval1 (Const b)   = pure b
eval1 (And b1 b2) = eval1 b1 >>= eval1And b2
eval1 (Or b1 b2)  = eval1 b1 >>= eval1Or b2

{-@ reflect eval1And @-}
eval1And :: BExpr -> Bool -> Tick Bool
eval1And b2 x1 = eval1 b2 >>= eval1And' x1

{-@ reflect eval1Or @-}
eval1Or  :: BExpr -> Bool -> Tick Bool
eval1Or b2 x1 = eval1 b2 >>= eval1Or' x1

{-@ reflect eval1Or' @-}
eval1Or' :: Bool -> Bool -> Tick Bool
eval1Or' x1 y1 = wait (if x1 then True else y1)



{-@ reflect eval1And' @-}
eval1And' :: Bool -> Bool -> Tick Bool
eval1And' x1 y1 =  wait (if x1 then y1 else False)


{-@ reflect eval2 @-}
eval2 :: BExpr -> Tick Bool
eval2 (Const b)   = pure b
eval2 (And b1 b2) = eval2 b1 >>= eval2And b2
eval2 (Or b1 b2)  = eval2 b1 >>= eval2Or  b2

{-@ reflect eval2Or @-}
eval2Or :: BExpr -> Bool -> Tick Bool
eval2Or b2 x2 = step 1 (if x2 then return True else eval2 b2)


{-@ reflect eval2And @-}
eval2And :: BExpr -> Bool -> Tick Bool
eval2And b2 x2 = step 1 (if x2 then eval2 b2 else return False)

{-@ reflect noShort @-}
noShort :: BExpr -> Bool -> Bool
noShort (Const b') b
  = b' == b
noShort (And e1 e2) b
  = noShort e1 True && noShort e2 b
noShort (Or e1 e2) b
  = noShort e1 False && noShort e2 b


lemma :: BExpr -> Bool -> Proof
{-@ lemma :: e:BExpr -> b:{Bool | noShort e b }  -> { tval (eval2 e) == b} @-}
lemma (Const b') b
  = ()
lemma (And e1 e2) b
  = lemma e1 True ? lemma e2 b
lemma (Or e1 e2) b
  = lemma e1 False ? lemma e2 b