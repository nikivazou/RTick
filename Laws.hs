
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
-- Martin A.T. Handley, Niki Vazou, and Graham Hutton.
--

{-@ LIQUID "--reflection" @-}

{-@ infix <*> @-}
{-@ infix </> @-}
{-@ infix >>= @-}
{-@ infix >/= @-}
{-@ infix >>> @-}
{-@ infix <<< @-}

module Laws where

import Prelude hiding
  ( Functor(..)
  , Applicative(..)
  , Monad(..)
  , id
  )

import RTick
import ProofCombinators

--
-- Functor, Applicative, and Monad laws for the 'Tick' datatype.
--
-- There's also some experimentation with laws concerning other resource
-- modifiers such as '(</>)' and '(>>=)'.
--

-------------------------------------------------------------------------------
-- Functor:
-------------------------------------------------------------------------------
--
-- Standard functor laws:
--
-- Identity:     fmap id          <=>   id                                                fmap_id
-- Composition:  fmap (g <<< f)   <=>   fmap g <<< fmap f                                 fmap_comp
--
--
-- Resource functor laws:
--
-- Identity:     wmap id                   >== 1 ==>   id                                 wmap_id
--               wmapN n id                >== n ==>   id                                 wmapN_id
--               gmap id                   <== 1 ==<   id                                 gmap_id
--               gmapN n id                <== n ==<   id                                 gmapN_id
-- Composition:  wmap (g <<< f)            <== 1 ==<   wmap g <<< wmap f                  wmap_comp
--               gmap (g <<< f)            >== 1 ==>   gmap g <<< gmap f
--               wmapN (m + n) (g <<< f)      <=>      wmapN m g <<< wmapN n f            wmapN_comp
--               gmapN (m + n) (g <<< f)      <=>      gmapN m g <<< gmapN n f            wmapN_comp
--

{-@ fmap_id :: t:Tick a -> { COSTEQ (fmap id t) (id t) } @-}
fmap_id :: Tick a -> Proof
fmap_id (Tick m x)
  =    fmap id (Tick m x)
   --  { defn. of fmap }
  <=>. Tick m (id x)
   -- { defn. of id }
  <=>. Tick m x
   -- { defn. of id }
  <=>. id (Tick m x)
  ***  QED

{-@ wmap_id :: t:Tick a -> { QIMP (wmap id t) 1 (id t) } @-}
wmap_id :: Tick a -> Proof
wmap_id (Tick m x)
  =    wmap id (Tick m x)
   -- { defn. of wmap }
  <=>. Tick (1 + m) (id x)
  .>== 1 ==>. Tick m (id x)
   -- { defn. of id }
  <=>. Tick m x
   -- { defn. of id }
  <=>. id (Tick m x)
  ***  QED

{-@ wmapN_id :: { n:Nat | n > 0 } -> t:Tick a
    -> { QIMP (wmapN n id t) n (id t) }
@-}
wmapN_id :: Int -> Tick a -> Proof
wmapN_id n (Tick m x)
  =    wmapN n id (Tick m x)
   -- { defn. of wmapN }
  <=>. Tick (n + m) (id x)
  .>== n ==>. Tick m (id x)
   -- { defn. of id }
  <=>. Tick m x
   -- { defn. of id }
  <=>. id (Tick m x)
  ***  QED

{-@ gmap_id :: t:Tick a -> { QDIM (gmap id t) 1 (id t) } @-}
gmap_id :: Tick a -> Proof
gmap_id (Tick m x)
  =    gmap id (Tick m x)
   -- { defn. of gmap }
  <=>. Tick (m - 1) (id x)
  .<== 1 ==<. Tick m (id x)
   -- { defn. of id }
  <=>. Tick m x
   -- { defn. of id }
  <=>. id (Tick m x)
  ***  QED

{-@ gmapN_id :: { n:Nat | n > 0 } -> t:Tick a
    -> { QDIM (gmapN n id t) n (id t) }
@-}
gmapN_id :: Int -> Tick a -> Proof
gmapN_id n (Tick m x)
  =    gmapN n id (Tick m x)
   -- { defn. of gmapN }
  <=>. Tick (m - n) (id x)
  .<== n ==<. Tick m (id x)
   -- { defn. of id }
  <=>. Tick m x
   -- { defn. of id }
  <=>. id (Tick m x)
  ***  QED

{-@ fmap_comp :: f:(a -> b) -> g:(b -> c) -> t:Tick a
    -> { COSTEQ (fmap (g <<< f) t) (fcomp (fmap g) (fmap f) t) }
@-}
fmap_comp :: (a -> b) -> (b -> c) -> Tick a -> Proof
fmap_comp f g (Tick m x)
  =    fmap (g <<< f) (Tick m x)
   -- { defn. of fmap }
  <=>. Tick m ((g <<< f) x)
   -- { defn. of (<<<) }
  <=>. Tick m (g (f x))
   -- { defn. of fmap }
  <=>. fmap g (Tick m (f x))
   -- { defn. of fmap }
  <=>. fmap g (fmap f (Tick m x))
   -- { defn. of fcomp }
  <=>. fcomp (fmap g) (fmap f) (Tick m x)
  ***  QED

{-@ wmap_comp :: f:(a -> b) -> g:(b -> c) -> t:Tick a
    -> { QDIM (wmap (g <<< f) t) 1 (fcomp (wmap g) (wmap f) t) }
@-}
wmap_comp :: (a -> b) -> (b -> c) -> Tick a -> Proof
wmap_comp f g (Tick m x)
  =    (wmap (g <<< f) (Tick m x)
   -- { defn. of wmap }
  <=>. Tick (1 + m) ((g <<< f) x)
   -- { defn. of (<<<) }
  <=>. Tick (1 + m) (g (f x))
  .<== 1 ==<. Tick (1 + 1 + m) (g (f x)))
   -- { defn. of wmap }
  <=>. wmap g (Tick (1 + m) (f x))
   -- { defn. of wmap }
  <=>. wmap g (wmap f (Tick m x))
   -- { defn. of fcomp }
  <=>. fcomp (wmap g) (wmap f) (Tick m x)
  ***  QED

{-@ wmapN_comp
  :: { m:Nat | m > 0 }
  -> { n:Nat | n > 0 }
  -> f:(a -> b)
  -> g:(b -> c)
  -> t:Tick a
  -> { COSTEQ (wmapN (m + n) (g <<< f) t) (fcomp (wmapN m g) (wmapN n f) t) }
@-}
wmapN_comp :: Int -> Int -> (a -> b) -> (b -> c) -> Tick a -> Proof
wmapN_comp m n f g (Tick o x)
  =    wmapN (m + n) (g <<< f) (Tick o x)
   -- { defn. of wmapN }
  <=>. Tick (m + n + o) ((g <<< f) x)
   -- { defn. of (<<<) }
  <=>. Tick (m + n + o) (g (f x))
   -- { defn. of wmapN }
  <=>. wmapN m g (Tick (n + o) (f x))
   -- { defn. of wmapN }
  <=>. wmapN m g (wmapN n f (Tick o x))
   -- { defn. of fcomp }
  <=>. fcomp (wmapN m g) (wmapN n f) (Tick o x)
  ***  QED

{-@ gmapN_comp
  :: { m:Nat | m > 0 }
  -> { n:Nat | n > 0 }
  -> f:(a -> b)
  -> g:(b -> c)
  -> t:Tick a
  -> { COSTEQ (gmapN (m + n) (g <<< f) t) (fcomp (gmapN m g) (gmapN n f) t) }
@-}
gmapN_comp :: Int -> Int -> (a -> b) -> (b -> c) -> Tick a -> Proof
gmapN_comp m n f g (Tick o x)
  =    gmapN (m + n) (g <<< f) (Tick o x)
   -- { defn. of gmapN }
  <=>. Tick (o - m - n) ((g <<< f) x)
   -- { defn. of (<<<) }
  <=>. Tick (o - m - n) (g (f x))
   -- { defn. of gmapN }
  <=>. gmapN m g (Tick (o - n) (f x))
   -- { defn. of gmapN }
  <=>. gmapN m g (gmapN n f (Tick o x))
   -- { defn. of fcomp }
  <=>. fcomp (gmapN m g) (gmapN n f) (Tick o x)
  ***  QED

-------------------------------------------------------------------------------
-- Applicative:
-------------------------------------------------------------------------------
--
-- Standard applicative laws:
--
-- Identity:      pure id <*> v                       <=>      v                          app_id
-- Homomorphism:  pure f <*> pure x                   <=>      pure (f x)                 app_homo
-- Interchange:   u <*> pure x                        <=>      pure (paf x) <*> u         app_inter
-- Composition:   pure (fcomp) <*> u <*> v <*> w      <=>      u <*> (v <*> w)            app_comp
--
--
-- Resource applicative laws:
--
-- Identity:      pure id </>  v                   >== 1 ==>   v                          wapp_id
--                pure id <//> v                   >== 2 ==>   v
--                pure id <\>  v                   <== 1 ==<   v
--                pure id <\\> v                   <== 2 ==<   v
-- Homomorphism:  pure f </>  pure x               >== 1 ==>   f x                        wapp_homo
--                pure f <//> pure x               >== 2 ==>   f x
--                pure f <\>  pure x               <== 1 ==<   f x
--                pure f <\\> pure x               <== 2 ==<   f x
-- Interchange:   u </>  pure x                       <=>      (paf x) </>  u             wapp_inter
--                u <//> pure x                       <=>      (paf x) <//> u
--                u <//> pure x                    >== 1 ==>   (paf x) </>  u
--                u <\> pure x                     <== 2 ==<   (paf x) </>  u
-- Composition:   pure (fcomp) </> u </> v </> w   >== 1 ==>   u </> (v </> w)            wapp_comp
--

{-@ app_id :: t:Tick a -> { COSTEQ (pure id <*> t) t } @-}
app_id :: Tick a -> Proof
app_id (Tick m x)
  =    pure id <*> Tick m x
   -- { defn. of pure }
  <=>. Tick 0 id <*> Tick m x
   -- { defn. of (<*>) }
  <=>. Tick (0 + m) (id x)
   -- { arithmetic }
  <=>. Tick m (id x)
   -- { defn. of id }
  <=>. Tick m x
  ***  QED

{-@ app_homo :: x:a -> f:(a -> b)
    -> { COSTEQ (pure f <*> pure x) (pure (f x)) }
@-}
app_homo :: a -> (a -> b) -> Proof
app_homo x f
  =    pure f <*> pure x
   -- { defn. of pure }
  <=>. Tick 0 f <*> Tick 0 x
   -- { defn. of (<*>) }
  <=>. Tick (0 + 0) (f x)
   -- { arithmetic }
  <=>. Tick 0 (f x)
   -- { defn. of pure }
  <=>. pure (f x)
  ***  QED

{-@ app_inter :: x:a -> u:Tick (a -> b)
    -> { COSTEQ (u <*> pure x) (pure (paf x) <*> u) }
@-}
app_inter :: a -> Tick (a -> b) -> Proof
app_inter x (Tick m f)
  =    Tick m f <*> pure x
   -- { defn. of pure }
  <=>. Tick m f <*> Tick 0 x
   -- { defn. of (<*>) }
  <=>. Tick (m + 0) (f x)
   -- { arithmetic }
  <=>. Tick (0 + m) (f x)
   -- { defn. of paf }
  <=>. Tick (0 + m) (paf x f)
   -- { defn. of (<*>) }
  <=>. Tick 0 (paf x) <*> Tick m f
   -- { defn. of pure }
  <=>. pure (paf x) <*> Tick m f
  ***  QED

{-@ app_comp :: t:Tick a -> v:Tick (a -> b) -> u:Tick (b -> c)
    -> { COSTEQ ((pure fcomp) <*> u <*> v <*> t) (u <*> (v <*> t)) }
@-}
app_comp :: Tick a -> Tick (a -> b) -> Tick (b -> c) -> Proof
app_comp (Tick o x) (Tick m f) (Tick n g)
  =    pure fcomp <*> Tick n g <*> Tick m f <*> Tick o x
   -- { defn. of pure }
  <=>. Tick 0 fcomp <*> Tick n g <*> Tick m f <*> Tick o x
   -- { defn. of (<*>) }
  <=>. Tick (0 + n + m + o) (fcomp g f x)
   -- { defn. of (<<<) }
  <=>. Tick (0 + n + m + o) (g (f x))
   -- { arithmetic }
  <=>. Tick (n + m + o) (g (f x))
   -- { defn. of (<*>) }
  <=>. Tick n g <*> Tick (m + o) (f x)
   -- { defn. of (<*>) }
  <=>. Tick n g <*> (Tick m f <*> Tick o x)
  ***  QED

{-@ wapp_id :: t:Tick a -> { QIMP (pure id </> t) 1 t } @-}
wapp_id :: Tick a -> Proof
wapp_id (Tick m x)
  =    pure id </> Tick m x
   -- { defn. of pure }
  <=>. Tick 0 id </> Tick m x
   -- { defn. of (</>) }
  <=>. Tick (1 + m) (id x)
  .>== 1 ==>. Tick m (id x)
   -- { defn. of id }
  <=>. Tick m x
  ***  QED

{-@ wapp_homo :: x:a -> f:(a -> b)
    -> { QIMP (pure f </> pure x) 1 (pure (f x)) }
@-}
wapp_homo :: a -> (a -> b) -> Proof
wapp_homo x f
  =    pure f </> pure x
   -- { defn. of pure }
  <=>. Tick 0 f </> Tick 0 x
   -- { defn. of (</>) }
  <=>. Tick (1 + 0 + 0) (f x)
   -- { arithmetic }
  <=>. Tick 1 (f x)
  .>== 1 ==>. Tick 0 (f x)
   -- { defn. of pure }
  <=>. pure (f x)
  ***  QED

{-@ wapp_inter :: x:a -> u:Tick (a -> b)
    -> { COSTEQ (u </> pure x) (pure (paf x) </> u) }
@-}
wapp_inter :: a -> Tick (a -> b) -> Proof
wapp_inter x (Tick m f)
  =    Tick m f </> pure x
    -- { defn. of pure }
  <=>. Tick m f </> Tick 0 x
    -- { defn. of (</>) }
  <=>. Tick (1 + m + 0) (f x)
    -- { arithmetic }
  <=>. Tick (1 + 0 + m) (f x)
    -- { defn. of paf }
  <=>. Tick (1 + 0 + m) (paf x f)
    -- { defn. of (</>) }
  <=>. Tick 0 (paf x) </> Tick m f
    -- { defn. of pure }
  <=>. pure (paf x) </> Tick m f
  ***  QED

{-@ wapp_comp :: t:Tick a -> v:Tick (a -> b) -> u:Tick (b -> c)
    -> { QIMP ((pure fcomp) </> u </> v </> t) 1 (u </> (v </> t)) }
@-}
wapp_comp :: Tick a -> Tick (a -> b) -> Tick (b -> c) -> Proof
wapp_comp (Tick o x) (Tick m f) (Tick n g)
  =    pure fcomp </> Tick n g </> Tick m f </> Tick o x
   -- { defn. of pure }
  <=>. Tick 0 fcomp </> Tick n g </> Tick m f </> Tick o x
   -- { defn. of (</>) }
  <=>. Tick (3 + n + m + o) (fcomp g f x)
   -- { defn. of (<<<) }
  <=>. Tick (3 + n + m + o) (g (f x))
  .>== 1 ==>. Tick (2 + n + m + o) (g (f x))
   -- { defn. of (</>) }
  <=>. Tick n g </> Tick (1 + m + o) (f x)
   -- { defn. of (</>) }
  <=>. Tick n g </> (Tick m f </> Tick o x)
  ***  QED

-------------------------------------------------------------------------------
-- Monad:
-------------------------------------------------------------------------------

--
-- Standard applicative laws:
--
-- Left identity:   return x >>= f       <=>      f x                                     bind_leftId
-- Right identity:  m >>= return         <=>      m                                       bind_rightId
-- Associativity:   (m >>= f) >>= g      <=>      m >>= (\x -> f x >>= g)                 bind_assoc
--
-- Resource applicative laws:
--
-- Left identity:   return x >/= f    >== 1 ==>   f x                                     wbind_leftId
--                  f =/< return x    >== 1 ==>   f x
--                  return x >\= f    <== 1 ==<   f x
--                  f =\< return x    <== 1 ==<   f x
-- Right identity:  m >/= return      >== 1 ==>   m                                       wbind_rightId
--                  return =/< m      >== 1 ==>   m
--                  m >\= return      <== 1 ==<   m
--                  return =\< m      <== 1 ==<   m
-- Associativity:   (m >/= f) >/= g      <=>      m >/= (\x -> f x >/= g)                 wbind_assoc
--

{-@ bind_leftId :: x:a -> f:(a -> Tick b)
   -> { COSTEQ (pure x >>= f) (f x) }
@-}
bind_leftId :: a -> (a -> Tick b) -> Proof
bind_leftId x f
  =    pure x >>= f
   -- { defn. of pure }
  <=>. Tick 0 x >>= f
   -- { defn. of (>>=) }
  <=>. (let Tick n y = f x in Tick (0 + n) y)
   -- { arithmetic }
  <=>. (let Tick n y = f x in Tick n y)
   -- { inline let }
  <=>. f x
  ***  QED

{-@ bind_rightId :: t:Tick a -> { COSTEQ (t >>= pure) t } @-}
bind_rightId :: Tick a -> Proof
bind_rightId (Tick m x)
  =    Tick m x >>= pure
   -- { defn. of (>>=) }
  <=>. (let Tick n y = pure x in Tick (m + n) y)
   -- { defn. of pure }
  <=>. (let Tick n y = Tick 0 x in Tick (m + n) y)
   -- { inline let }
  <=>. Tick (m + 0) x
   -- { arithmetic }
  <=>. Tick m x
  ***  QED

{-@ reflect rightBindAssoc @-}
{-@ rightBindAssoc :: (a -> Tick b) -> (b -> Tick c) -> a -> Tick c @-}
rightBindAssoc :: (a -> Tick b) -> (b -> Tick c) -> a -> Tick c
rightBindAssoc f g x = f x >>= g

{-@ bind_assoc :: t:Tick a -> f:(a -> Tick b) -> g:(b -> Tick c)
   -> { COSTEQ ((t >>= f) >>= g) (t >>= rightBindAssoc f g) }
@-}
bind_assoc :: Tick a -> (a -> Tick b) -> (b -> Tick c) -> Proof
bind_assoc (Tick m x) f g
 =    (Tick m x >>= f) >>= g
  -- { defn. of (>>=) }
 <=>. (let Tick n y = f x in Tick (m + n) y) >>= g
  -- { defn. of (>>=) }
 <=>. (let Tick n y = f x in let Tick o w = g y in Tick (m + n + o) w)
  -- { defn. of (>>=) }
 <=>. (let Tick n y = f x >>= g in Tick (m + n) y)
  -- { defn. of rightBindAssoc }
 <=>. (let Tick n y = rightBindAssoc f g x in Tick (m + n) y)
  -- { defn. of (>>=) }
 <=>. Tick m x >>= rightBindAssoc f g
 ***  QED

{-@ wbind_leftId :: x:a -> f:(a -> Tick b)
    -> { QIMP (pure x >/= f) 1 (f x) }
@-}
wbind_leftId :: a -> (a -> Tick b) -> Proof
wbind_leftId x f
  =    pure x >/= f
   -- { defn. of pure }
  <=>. Tick 0 x >/= f
   -- { defn. of (>/=) }
  <=>. (let Tick n y = f x in Tick (1 + 0 + n) y)
   -- { arithmetic }
  <=>. (let Tick n y = f x in Tick (1 + n) y)
  .>== 1 ==>. (let Tick n y = f x in Tick n y)
   -- { arithmetic }
  <=>. (let Tick n y = f x in Tick n y)
   -- { inline let }
  <=>. f x
  ***  QED

{-@ wbind_rightId :: t:Tick a -> { QIMP (t >/= pure) 1 t } @-}
wbind_rightId :: Tick a -> Proof
wbind_rightId (Tick m x)
  =    Tick m x >/= pure
   -- { defn. of (>/=) }
  <=>. (let Tick n y = pure x in Tick (1 + m + n) y)
   -- { defn. of pure }
  <=>. (let Tick n y = Tick 0 x in Tick (1 + m + n) y)
  .>== 1 ==>. (let Tick n y = Tick 0 x in Tick (m + n) y)
   -- { inline let }
  <=>. Tick (m + 0) x
   -- { arithmetic }
  <=>. Tick m x
  ***  QED

{-@ reflect rightWbindAssoc @-}
{-@ rightWbindAssoc :: (a -> Tick b) -> (b -> Tick c) -> a -> Tick c @-}
rightWbindAssoc :: (a -> Tick b) -> (b -> Tick c) -> a -> Tick c
rightWbindAssoc f g x = f x >/= g

{-@ wbind_assoc :: t:Tick a -> f:(a -> Tick b) -> g:(b -> Tick c)
    -> { COSTEQ ((t >/= f) >/= g) (t >/= rightWbindAssoc f g) }
@-}
wbind_assoc :: Tick a -> (a -> Tick b) -> (b -> Tick c) -> Proof
wbind_assoc (Tick m x) f g
 =    (Tick m x >/= f) >/= g
  -- { defn. of (>/=) }
 <=>. (let Tick n y = f x in Tick (1 + m + n) y) >/= g
  -- { defn. of (>/=) }
 <=>. (let Tick n y = f x in let Tick o w = g y in Tick (2 + m + n + o) w)
  -- { defn. of (>/=) }
 <=>. (let Tick n y = f x >/= g in Tick (1 + m + n) y)
  -- { defn. of rightWbindAssoc }
 <=>. (let Tick n y = rightWbindAssoc f g x in Tick (1 + m + n) y)
  -- { defn. of (>/=) }
 <=>. Tick m x >/= rightWbindAssoc f g
 ***  QED

-------------------------------------------------------------------------------
-- Helper functions:
-------------------------------------------------------------------------------

{-@ reflect id @-}
{-@ id :: a -> a @-}
id :: a -> a
id x = x

--
-- 'paf' is just @flip ($)@.
--
{-@ reflect paf @-}
{-@ paf :: a -> (a -> b) -> b @-}
paf :: a -> (a -> b) -> b
paf x f = f x

--
-- @g <<< f@ reads \"g after f\".
--
{-@ reflect <<< @-}
{-@ (<<<) :: (b -> c) -> (a -> b) -> a -> c @-}
(<<<) :: (b -> c) -> (a -> b) -> a -> c
g <<< f = \x -> g (f x)

--
-- 'fcomp' is just '(<<<)' but not infix.
--
{-@ reflect fcomp @-}
{-@ fcomp :: (b -> c) -> (a -> b) -> a -> c @-}
fcomp :: (b -> c) -> (a -> b) -> a -> c
fcomp g f  = \x -> g (f x)

--
-- @f >>> g@ reads \"f before g\".
--
{-@ reflect >>> @-}
{-@ (>>>) :: (a -> b) -> (b -> c) -> a -> c @-}
(>>>) :: (a -> b) -> (b -> c) -> a -> c
f >>> g = \x -> g (f x)