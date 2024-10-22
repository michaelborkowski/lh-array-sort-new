

{-@ LIQUID "--higherorder"  @-}

{-    @ LIQUID "--extensionality" @-}

module Linear.Unsafe (toLinear, toLinear3) where

import Linear.Common
import qualified Unsafe.Linear as Unsafe

-- these may need be generalized later

{-    @ assume toLinear :: f:_ -> { g:_ | f == g} @-}
{-@ assume toLinear :: f:(a->b) -> x:a -> { v:b | v == f x} @-}
toLinear :: (a -> b) -. (a -. b)
--toLinear :: (a -> (b,a)) -> (a %1-> (b,a))
toLinear f = Unsafe.toLinear f

{-@ assume toLinear3 :: f:_ -> x:_ -> y:_ -> z:_ -> { v:d | v == f x y z } @-}
toLinear3 :: (a -> b -> c -> d) -> (a -. (b -> c -> d))
toLinear3 f = Unsafe.toLinear3 f
