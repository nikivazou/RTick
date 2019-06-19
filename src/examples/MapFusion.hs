{-@ LIQUID "--reflection" @-}
module MapFusion where 

import Prelude hiding (mapM, Applicative (..), Monad (..), length)    
import Data.RTick 
import Data.Lists 
import Proof.Combinators 
import Proof.Quantified 
{-@ infix   >>= @-}
{-@ infix   >=> @-}
{-@ infix   :   @-}



{-@ reflect mapM @-}
mapM :: (a -> Tick b) -> [a] -> Tick [b]
mapM f []     = pure [] 
mapM f (x:xs) = step 1 (liftA2 cons (f x) (mapM f xs))


mapFusion :: Eq c => (a -> Tick b) -> (b -> Tick c) -> [a] -> () 
{-@ mapFusion :: f:(a -> Tick b) -> g:(b -> Tick c) -> xs:[a] 
              -> { (tval (mapM f xs >>= mapM g)  == tval (mapM (f >=> g) xs)) && 
                   (tcost (mapM f xs >>= mapM g) == length xs  + tcost (mapM (f >=> g) xs))
                 }
  @-}
mapFusion f g [] 
  =   mapM f [] >>= mapM g
  ==. pure []   >>= mapM g 
  ==. (let Tick j w = mapM g [] in Tick (0 + j) w)   
  ==. mapM (f >=> g) [] 
  *** QED 
mapFusion f g (x:xs) 
  =   mapM f (x:xs) >>= mapM g
  <=> step 1 (liftA2 cons (f x) (mapM f xs)) >>= mapM g
  >== 1 ==> 
      Tick (cf+cfs) (fx `cons` fxs) >>= mapM g
  <=> Tick (cf+cfs+cgs) gfxs
      ? (mapM g (fx:fxs) ==. step 1 (liftA2 cons (g fx) (mapM g fxs)) *** QED)
  <=> Tick (1+cfg+cfgs) (fgx `cons` fgxs)   
      ? mapFusion f g xs 
  >== length xs ==>  
      Tick (1+cfg + cfgsr) (fgx:fgxsr)
  <=> step 1 (liftA2 cons ((f >=> g) x) (mapM (f >=> g) xs))      
  <=> mapM (f >=> g) (x:xs) 
  *** QED 
  where
    Tick cf fx     = f x 
    Tick cfs fxs   = mapM f xs   
    Tick cgs gfxs  = mapM g (fx:fxs)  
    Tick cfg fgx   = (f >=> g) x
    Tick cfgs fgxs = mapM f xs >>= mapM g
    Tick cfgsr fgxsr = mapM (f >=> g) xs





