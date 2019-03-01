
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
-- Martin A.T. Handley, Niki Vazou, and Graham Hutton.
--

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

{-@ infix <*>  @-}
{-@ infix </>  @-}
{-@ infix <//> @-}
{-@ infix <\>  @-}
{-@ infix <\\> @-}
{-@ infix >>=  @-}
{-@ infix =<<  @-}
{-@ infix >/=  @-}
{-@ infix =/<  @-}
{-@ infix >//= @-}
{-@ infix =//< @-}
{-@ infix >\=  @-}
{-@ infix =\<  @-}
{-@ infix >\\= @-}
{-@ infix =\\< @-}
{-@ infix >>>  @-}

module ResourceModifiers where

import Prelude hiding
  ( Functor(..)
  , Applicative(..)
  , Monad(..)
  , (=<<)
  , id
  )

import RTick
import ProofCombinators

--
-- Proofs that all resource modifiers to 'return', '(>>=)', and 'step'.
--

{-@ wait_return_step :: x:a -> { wait x == step 1 (return x) } @-}
wait_return_step :: a -> Proof
wait_return_step x
  =   wait x
  ==. Tick 1 x
  ==. step 1 (Tick 0 x)
  ==. step 1 (return x)
  *** QED

{-@ waitN_return_step :: { n:Nat | n > 0 } -> x:a
    -> { waitN n x == step n (return x) }
@-}
waitN_return_step :: Int -> a -> Proof
waitN_return_step n x
  =   waitN n x
  ==. Tick n x
  ==. step n (Tick 0 x)
  ==. step n (return x)
  *** QED

{-@ go_return_step :: x:a -> { go x == step (-1) (return x) } @-}
go_return_step :: a -> Proof
go_return_step x
  =   go x
  ==. Tick (-1) x
  ==. step (-1) (Tick 0 x)
  ==. step (-1) (return x)
  *** QED

{-@ goN_return_step :: { n:Nat | n > 0 } -> x:a
    -> { goN n x == step (-n) (return x) }
@-}
goN_return_step :: Int -> a -> Proof
goN_return_step n x
  =   goN n x
  ==. Tick (-n) x
  ==. step (-n) (Tick 0 x)
  ==. step (-n) (return x)
  *** QED

{-@ fmap_return_bind :: f:(a -> b) -> t:(Tick a)
    -> { fmap f t == t >>= (f >>> return) }
@-}
fmap_return_bind :: (a -> b) -> Tick a -> Proof
fmap_return_bind f (Tick m x)
  =   fmap f (Tick m x)
  ==. Tick m (f x)
  ==. Tick (m + 0) (f x)
  ==. (let Tick n y = return (f x) in Tick (m + n) y)
  ==. (let Tick n y = (f >>> return) x in Tick (m + n) y)
  ==. Tick m x >>= (f >>> return)
  *** QED

{-@ wmap_return_bind_step :: f:(a -> b) -> t:(Tick a)
    -> { wmap f t == step 1 (t >>= (f >>> return)) }
@-}
wmap_return_bind_step :: (a -> b) -> Tick a -> Proof
wmap_return_bind_step f (Tick m x)
  =   wmap f (Tick m x)
  ==. Tick (1 + m) (f x)
  ==. step 1 (Tick m (f x))
  ==. step 1 (fmap f (Tick m x))
   ? fmap_return_bind f (Tick m x)
  ==. step 1 (Tick m x >>= (f >>> return))
  *** QED

{-@ wmapN_return_bind_step :: { m:Nat | m > 0 } -> f:(a -> b) -> t:(Tick a)
    -> { wmapN m f t == step m (t >>= (f >>> return)) }
@-}
wmapN_return_bind_step :: Int -> (a -> b) -> Tick a -> Proof
wmapN_return_bind_step m f (Tick n x)
  =   wmapN m f (Tick n x)
  ==. Tick (m + n) (f x)
  ==. step m (Tick n (f x))
  ==. step m (fmap f (Tick n x))
   ? fmap_return_bind f (Tick n x)
  ==. step m (Tick n x >>= (f >>> return))
  *** QED

{-@ gmap_return_bind_step :: f:(a -> b) -> t:(Tick a)
    -> { gmap f t == step (-1) (t >>= (f >>> return)) }
@-}
gmap_return_bind_step :: (a -> b) -> Tick a -> Proof
gmap_return_bind_step f (Tick m x)
  =   gmap f (Tick m x)
  ==. Tick (m - 1) (f x)
  ==. step (-1) (Tick m (f x))
  ==. step (-1) (fmap f (Tick m x))
   ? fmap_return_bind f (Tick m x)
  ==. step (-1) (Tick m x >>= (f >>> return))
  *** QED

{-@ gmapN_return_bind_step :: { m:Nat | m > 0 } -> f:(a -> b) -> t:(Tick a)
    -> { gmapN m f t == step (-m) (t >>= (f >>> return)) }
@-}
gmapN_return_bind_step :: Int -> (a -> b) -> Tick a -> Proof
gmapN_return_bind_step m f (Tick n x)
  =   gmapN m f (Tick n x)
  ==. Tick (n - m) (f x)
  ==. step (-m) (Tick n (f x))
  ==. step (-m) (fmap f (Tick n x))
   ? fmap_return_bind f (Tick n x)
  ==. step (-m) (Tick n x >>= (f >>> return))
  *** QED

{-@ pure_return :: x:a -> { pure x == return x } @-}
pure_return :: a -> Proof
pure_return x
  =   pure x
  ==. Tick 0 x
  ==. return x
  *** QED

{-@ ple app_return_bind @-}
{-@ app_return_bind :: t1:(Tick (a -> b)) -> t2:(Tick a)
    -> { t1 <*> t2 == t1 >>= (bind_return t2) }
@-}
app_return_bind :: Tick (a -> b) -> (Tick a) -> Proof
app_return_bind (Tick m f) (Tick n x)
  =   Tick m f <*> Tick n x
  ==. Tick (m + n) (f x)
  ==. Tick (m + n + 0) (f x)
  ==. (let Tick o w = pure (f x) in Tick (m + n) w)
  ==. (let Tick o w = (f >>> pure) x in Tick (m + n) w)
  ==. Tick (m + n) x >>= (f >>> pure)
  ==. bind_return (Tick (m + n) x) f
  ==. (let Tick o w = bind_return (Tick (m + n) x) f in Tick o w)
   -- { uses PLE }
  ==. (let Tick o w = bind_return (Tick n x) f in Tick (m + o) w)
  ==. Tick m f >>= bind_return (Tick n x)
  ==. Tick m f >>= bind_return (Tick n x)
  *** QED

{-@ wapp_return_bind_step :: t1:(Tick (a -> b)) -> t2:(Tick a)
    -> { t1 </> t2 == step 1 (t1 >>= (bind_return t2)) }
@-}
wapp_return_bind_step :: Tick (a -> b) -> (Tick a) -> Proof
wapp_return_bind_step (Tick m f) (Tick n x)
  =   Tick m f </> Tick n x
  ==. Tick (1 + m + n) (f x)
  ==. step 1 (Tick (m + n) (f x))
  ==. step 1 (Tick m f <*> Tick n x)
   ? app_return_bind (Tick m f) (Tick n x)
  ==. step 1 ((Tick m f) >>= (bind_return (Tick n x)))
  *** QED

{-@ wwapp_return_bind_step :: t1:(Tick (a -> b)) -> t2:(Tick a)
    -> { t1 <//> t2 == step 2 (t1 >>= (bind_return t2)) }
@-}
wwapp_return_bind_step :: Tick (a -> b) -> (Tick a) -> Proof
wwapp_return_bind_step (Tick m f) (Tick n x)
  =   Tick m f <//> Tick n x
  ==. Tick (2 + m + n) (f x)
  ==. step 2 (Tick (m + n) (f x))
  ==. step 2 (Tick m f <*> Tick n x)
   ? app_return_bind (Tick m f) (Tick n x)
  ==. step 2 ((Tick m f) >>= (bind_return (Tick n x)))
  *** QED

{-@ gapp_return_bind_step :: t1:(Tick (a -> b)) -> t2:(Tick a)
    -> { t1 <\> t2 == step (-1) (t1 >>= (bind_return t2)) }
@-}
gapp_return_bind_step :: Tick (a -> b) -> (Tick a) -> Proof
gapp_return_bind_step (Tick m f) (Tick n x)
  =   Tick m f <\> Tick n x
  ==. Tick (m + n - 1) (f x)
  ==. step (-1) (Tick (m + n) (f x))
  ==. step (-1) (Tick m f <*> Tick n x)
   ? app_return_bind (Tick m f) (Tick n x)
  ==. step (-1) ((Tick m f) >>= (bind_return (Tick n x)))
  *** QED

{-@ ggapp_return_bind_step :: t1:(Tick (a -> b)) -> t2:(Tick a)
    -> { t1 <\\> t2 == step (-2) (t1 >>= (bind_return t2)) }
@-}
ggapp_return_bind_step :: Tick (a -> b) -> (Tick a) -> Proof
ggapp_return_bind_step (Tick m f) (Tick n x)
  =   Tick m f <\\> Tick n x
  ==. Tick (m + n - 2) (f x)
  ==. step (-2) (Tick (m + n) (f x))
  ==. step (-2) (Tick m f <*> Tick n x)
   ? app_return_bind (Tick m f) (Tick n x)
  ==. step (-2) ((Tick m f) >>= (bind_return (Tick n x)))
  *** QED

{-@ liftA2_return_bind :: f:(a -> b -> c) -> t1:(Tick a) -> t2:(Tick b)
    -> { liftA2 f t1 t2 == (return f >>= bind_return t1) >>= (bind_return t2) }
@-}
liftA2_return_bind :: (a -> b -> c) -> Tick a -> Tick b -> Proof
liftA2_return_bind f (Tick m x) (Tick n y)
  =   liftA2 f (Tick m x) (Tick n y)
  ==. Tick (m + n) (f x y)
  ==. Tick (0 + m + n) (f x y)
  ==. Tick (0 + m) (f x) <*> Tick n y
  ==. (Tick 0 f <*> Tick m x) <*> Tick n y
  ==. (return f <*> Tick m x) <*> Tick n y
   ? app_return_bind (return f) (Tick m x)
  ==. (return f >>= (bind_return (Tick m x))) <*> Tick n y
   ? app_return_bind (return f >>= bind_return (Tick m x)) (Tick n y)
  ==. (return f >>= bind_return (Tick m x)) >>= bind_return (Tick n y)
  *** QED

{-@ flipped_bind_bind :: f:(a -> Tick b) -> t:(Tick a)
    -> { f =<< t == t >>= f }
@-}
flipped_bind_bind :: (a -> Tick b) -> Tick a -> Proof
flipped_bind_bind f (Tick m x)
  =   f =<< Tick m x
  ==. (let Tick n y = f x in Tick (m + n) y)
  ==. Tick m x >>= f
  *** QED

{-@ ap_return_bind :: t1:(Tick (a -> b)) -> t2:(Tick a)
    -> { ap t1 t2 == t1 >>= (bind_return t2) }
@-}
ap_return_bind :: Tick (a -> b) -> Tick a -> Proof
ap_return_bind (Tick m f) (Tick n x)
  =   ap (Tick m f) (Tick n x)
  ==. Tick (m + n) (f x)
  ==. Tick m f <*> Tick n x
   ? app_return_bind (Tick m f) (Tick n x)
  ==. (Tick m f) >>= (bind_return (Tick n x))
  *** QED

{-@ ple eqBind_bind @-}
{-@ eqBind_bind
  :: n:Int
  -> f:(a -> { tf:Tick b | n == tcost tf })
  -> t:(Tick a)
  -> { eqBind n t f == t >>= f }
@-}
eqBind_bind :: Int -> (a -> Tick b) -> Tick a -> Proof
eqBind_bind n f (Tick m x)
  =   leqBind n (Tick m x) f
  ==. (let Tick n y = f x in Tick (m + n) y)
  ==. Tick m x >>= f
  *** QED

{-@ ple leqBind_bind @-}
{-@ leqBind_bind
  :: n:Int
  -> f:(a -> { tf:Tick b | n >= tcost tf })
  -> t:(Tick a)
  -> { leqBind n t f == t >>= f }
@-}
leqBind_bind :: Int -> (a -> Tick b) -> Tick a -> Proof
leqBind_bind n f (Tick m x)
  =   leqBind n (Tick m x) f
  ==. (let Tick n y = f x in Tick (m + n) y)
  ==. Tick m x >>= f
  *** QED

{-@ ple geqBind_bind @-}
{-@ geqBind_bind
  :: n:Int
  -> f:(a -> { tf:Tick b | n <= tcost tf })
  -> t:(Tick a)
  -> { geqBind n t f == t >>= f }
@-}
geqBind_bind :: Int -> (a -> Tick b) -> Tick a -> Proof
geqBind_bind n f (Tick m x)
  =   geqBind n (Tick m x) f
  ==. (let Tick n y = f x in Tick (m + n) y)
  ==. Tick m x >>= f
  *** QED

{-@ wbind_bind_step :: t:(Tick a) -> f:(a -> Tick b)
    -> { t >/= f == step 1 (t >>= f) }
@-}
wbind_bind_step :: Tick a -> (a -> Tick b) -> Proof
wbind_bind_step (Tick m x) f
  =   Tick m x >/= f
  ==. (let Tick n y = f x in Tick (1 + m + n) y)
  ==. step 1 (let Tick n y = f x in Tick (m + n) y)
  ==. step 1 (Tick m x >>= f)
  *** QED

{-@ flipped_wbind_bind_step :: f:(a -> Tick b) -> t:(Tick a)
    -> { f =/< t == step 1 (t >>= f) }
@-}
flipped_wbind_bind_step :: (a -> Tick b) -> Tick a -> Proof
flipped_wbind_bind_step f (Tick m x)
  =   f =/< Tick m x
  ==. (let Tick n y = f x in Tick (1 + m + n) y)
  ==. step 1 (let Tick n y = f x in Tick (m + n) y)
  ==. step 1 (Tick m x >>= f)
  *** QED

{-@ wwbind_bind_step :: t:(Tick a) -> f:(a -> Tick b)
    -> { t >//= f == step 2 (t >>= f) }
@-}
wwbind_bind_step :: Tick a -> (a -> Tick b) -> Proof
wwbind_bind_step (Tick m x) f
  =   Tick m x >//= f
  ==. (let Tick n y = f x in Tick (2 + m + n) y)
  ==. step 2 (let Tick n y = f x in Tick (m + n) y)
  ==. step 2 (Tick m x >>= f)
  *** QED

{-@ flipped_wwbind_bind_step :: f:(a -> Tick b) -> t:(Tick a)
    -> { f =//< t == step 2 (t >>= f) }
@-}
flipped_wwbind_bind_step :: (a -> Tick b) -> Tick a -> Proof
flipped_wwbind_bind_step f (Tick m x)
  =   f =//< Tick m x
  ==. (let Tick n y = f x in Tick (2 + m + n) y)
  ==. step 2 (let Tick n y = f x in Tick (m + n) y)
  ==. step 2 (Tick m x >>= f)
  *** QED

{-@ gbind_bind_step :: t:(Tick a) -> f:(a -> Tick b)
    -> { t >\= f == step (-1) (t >>= f) }
@-}
gbind_bind_step :: Tick a -> (a -> Tick b) -> Proof
gbind_bind_step (Tick m x) f
  =   Tick m x >\= f
  ==. (let Tick n y = f x in Tick (m + n - 1) y)
  ==. step (-1) (let Tick n y = f x in Tick (m + n) y)
  ==. step (-1) (Tick m x >>= f)
  *** QED

{-@ flipped_gbind_bind_step :: f:(a -> Tick b) -> t:(Tick a)
    -> { f =\< t == step (-1) (t >>= f) }
@-}
flipped_gbind_bind_step :: (a -> Tick b) -> Tick a -> Proof
flipped_gbind_bind_step f (Tick m x)
  =   f =\< Tick m x
  ==. (let Tick n y = f x in Tick (m + n - 1) y)
  ==. step (-1) (let Tick n y = f x in Tick (m + n) y)
  ==. step (-1) (Tick m x >>= f)
  *** QED

{-@ ggbind_bind_step :: t:(Tick a) -> f:(a -> Tick b)
    ->  { t >\\= f == step (-2) (t >>= f) }
@-}
ggbind_bind_step :: Tick a -> (a -> Tick b) -> Proof
ggbind_bind_step (Tick m x) f
  =   Tick m x >\\= f
  ==. (let Tick n y = f x in Tick (m + n - 2) y)
  ==. step (-2) (let Tick n y = f x in Tick (m + n) y)
  ==. step (-2) (Tick m x >>= f)
  *** QED

{-@ flipped_ggbind_bind_step :: f:(a -> Tick b) -> t:(Tick a)
    ->  { f =\\< t == step (-2) (t >>= f) }
@-}
flipped_ggbind_bind_step :: (a -> Tick b) -> Tick a -> Proof
flipped_ggbind_bind_step f (Tick m x)
  =   f =\\< Tick m x
  ==. (let Tick n y = f x in Tick (m + n - 2) y)
  ==. step (-2) (let Tick n y = f x in Tick (m + n) y)
  ==. step (-2) (Tick m x >>= f)
  *** QED

{-@ liftM_return_bind :: f:(a -> b) -> t:(Tick a)
    -> { liftM f t == t >>= (f >>> return) } @-}
liftM_return_bind :: (a -> b) -> Tick a -> Proof
liftM_return_bind f (Tick m x)
  =  liftM f (Tick m x)
  ==. Tick m (f x)
  ==. fmap f (Tick m x)
   ? fmap_return_bind f (Tick m x)
  ==. Tick m x >>= (f >>> return)
  *** QED

{-@ liftM2_return_bind :: f:(a -> b -> c) -> t1:(Tick a) -> t2:(Tick b)
    -> { liftM2 f t1 t2 == (return f >>= bind_return t1) >>= (bind_return t2) }
@-}
liftM2_return_bind :: (a -> b -> c) -> Tick a -> Tick b -> Proof
liftM2_return_bind f (Tick m x) (Tick n y)
  =   liftM2 f (Tick m x) (Tick n y)
  ==. Tick (m + n) (f x y)
  ==. liftA2 f (Tick m x) (Tick n y)
   ? liftA2_return_bind f (Tick m x) (Tick n y)
  ==. (return f >>= bind_return (Tick m x)) >>= (bind_return (Tick n y))
  *** QED

{-@ pay_return_step :: m:Int
    -> { t:Tick a | m <= tcost t }
    -> { pay m t == step m (return (step (-m) t)) }
@-}
pay_return_step :: Int -> Tick a -> Proof
pay_return_step m (Tick n x)
  =   pay m (Tick n x)
  ==. Tick m (Tick (n - m) x)
  ==. Tick m (step (-m) (Tick n x))
  ==. step m (return (step (-m) (Tick n x)))
  *** QED

-------------------------------------------------------------------------------
-- | Helper functions:
-------------------------------------------------------------------------------

{-@ reflect >>> @-}
{-@ (>>>) :: (a -> b) -> (b -> c) -> a -> c @-}
(>>>) :: (a -> b) -> (b -> c) -> a -> c
f >>> g = \x -> g (f x)

{-@ reflect bind_return @-}
{-@ bind_return :: Tick a -> (a -> b) -> Tick b @-}
bind_return :: Tick a -> (a -> b) -> Tick b
bind_return m f = m >>= (f >>> return)