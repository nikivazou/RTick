
{-  Queues 50/14/00 -}

--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
--

{-@ LIQUID "--reflection"      @-}
{-@ LIQUID "--no-adt"          @-}
{-@ LIQUID "--no-termination"  @-}

module ImplicitQueues where

import RTick

--
-- Okasaki's implicit queues.
--

data Pair a b = Pair a b

data Q a
  = QEmp
  | QSingle a
  | QTwoZero a a (Tick (Q (Pair a a)))
  | QTwoOne  a a (Tick (Q (Pair a a))) a
  | QOneZero a   (Tick (Q (Pair a a)))
  | QOneOne  a   (Q (Pair a a)) a

{-@
data Q a = QEmp
  | QSingle  { qsingle :: a }
  | QTwoZero { q201 :: a, q202 :: a, q20s :: {t:Tick (Q (Pair a a)) | tcost t == 5 } }
  | QTwoOne  { q211 :: a, q212 :: a, q21a :: {t:Tick (Q (Pair a a)) | tcost t == 3 } , q21b :: a}
  | QOneZero { q101 :: a, q10s :: {t:Tick (Q (Pair a a)) | tcost t == 2 } }
  | QOneOne  { q111 :: a, q11s :: Q (Pair a a), q11b :: a}
@-}

{-@ snoc :: Q a -> a -> { t:Tick (Q a) | tcost t == 5 } @-}
snoc :: Q a -> a -> Tick (Q a)
snoc QEmp x                  = waitN 5 (QSingle x)
snoc (QSingle y1) x          = waitN 5 (QTwoZero y1 x (waitN 5 QEmp))
snoc (QTwoZero y1 y2 ys) x   = eqBind 3 (pay 2 ys) (\ys' -> waitN 3 (QTwoOne y1 y2 ys' x))
snoc (QTwoOne y1 y2 ys y3) x = eqBind 2 ys (\ys' -> waitN 2 (QTwoZero y1 y2 (snoc ys' (Pair y3 x))))
snoc (QOneZero y1 ys) x      = eqBind 3 ys (\ys' -> waitN 3 (QOneOne y1 ys' x))
snoc (QOneOne y1 ys y2) x    = eqBind 2 (pay 3 $ snoc ys (Pair y2 x)) (\ys' -> waitN 2 (QOneZero y1 ys'))

data View a = VNil | VCons a (Tick (Q a))
{-@ data View a = VNil
  | VCons { vconsval :: a, vconstail :: { t:Tick (Q a) | tcost t == 4 }} @-}

{-@ view :: Q a -> { t:Tick (View a) | tcost t == 1 } @-}
view :: Q a -> Tick (View a)
view QEmp                  = waitN 1 VNil
view (QSingle x)           = waitN 1 $ VCons x (waitN 4 QEmp)
view (QTwoZero x1 x2 xs)   = waitN 1 (VCons x1 (eqBind 1 (pay 3 xs) (\xs' -> waitN 1 (QOneZero x2 xs'))))
view (QTwoOne x1 x2 xs x4) = waitN 1 (VCons x1 (eqBind 1 xs (\xs' -> waitN 1 (QOneOne x2 xs' x4))))
view (QOneZero x1 xs)      = waitN 1 (VCons x1 (eqBind 1 (eqBind 1 xs view) expand))
  where
    {-@ expand :: _ -> { t:_ | tcost t == 1 } @-}
    expand VNil                    = waitN 1 QEmp
    expand (VCons (Pair x1 x2) xs) = waitN 1 (QTwoZero x1 x2 (step 1 xs))
view (QOneOne x1 xs x3) = waitN 1 (VCons x1 (eqBind 3 (view xs) expand))
  where
    {-@ expand :: _ -> { t:_ | tcost t == 3 } @-}
    expand VNil                       = waitN 3 (QSingle x3)
    expand (VCons (Pair x21 x22) xs2) = eqBind 2 (pay 1 xs2) (\xs2' -> waitN 2 $ QTwoOne x21 x22 xs2' x3)