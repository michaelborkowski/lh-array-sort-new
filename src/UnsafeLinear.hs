{-# LANGUAGE LinearTypes   #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--higherorder"  @-}

module UnsafeLinear (toLinear, toLinear3) where

import qualified Unsafe.Linear as Unsafe

-- these may need be generalized later

{-@ assume toLinear :: f:_ -> x:_ -> { tup:_ | tup == f x} @-}
toLinear :: (a -> (b,a)) -> (a %1-> (b,a))
toLinear f = Unsafe.toLinear f

{-@ assume toLinear3 :: f:_ -> x:_ -> y:_ -> z:_ -> { v:_ | v == f x y z } @-}
toLinear3 :: (a -> b -> c -> a) -> (a %1-> b -> c -> a)
toLinear3 f = Unsafe.toLinear3 f