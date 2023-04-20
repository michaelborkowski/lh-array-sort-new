{-# LANGUAGE LinearTypes   #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--higherorder"  @-}

{-    @ LIQUID "--extensionality" @-}

module UnsafeLinear (toLinear, toLinear3) where

import qualified Unsafe.Linear as Unsafe

-- these may need be generalized later

{-    @ assume toLinear :: f:_ -> { g:_ | f == g} @-}
{-@ assume toLinear :: f:(a->b) -> x:a -> { v:b | v == f x} @-}
toLinear :: (a -> b) -> (a %1-> b)
--toLinear :: (a -> (b,a)) -> (a %1-> (b,a))
toLinear f = Unsafe.toLinear f

{-@ assume toLinear3 :: f:_ -> x:_ -> y:_ -> z:_ -> { v:d | v == f x y z } @-}
toLinear3 :: (a -> b -> c -> d) -> (a %1-> b -> c -> d)
toLinear3 f = Unsafe.toLinear3 f