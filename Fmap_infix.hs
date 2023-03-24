module Fmap_infix where

import RTick
import Prelude hiding (fmap, (<$>), (<*>))
import ProofCombinators


fmap_infix_proof :: Tick a -> (a -> b) -> ()
fmap_infix_proof t f = fmap f t ==. (f <$> t) *** QED