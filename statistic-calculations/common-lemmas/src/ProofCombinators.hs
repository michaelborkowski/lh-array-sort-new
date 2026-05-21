
module ProofCombinators ((?){-}, pleUnfold-}, ur, unur, Ur(..) ) where

import Linear.Common
import Linear.Unsafe as Unsafe (toLinear)
import Language.Haskell.Liquid.ProofCombinators (Proof)

-- half-monomorphic ? operator with linear type signature
{-@ (?) :: x:a -> Proof -> { v:a | v = x } @-}
(?) :: a -. (Proof -> a)
(?) x _ = x

{- @ reflect pleUnfold @- }
pleUnfold :: a %1-> a
pleUnfold x = x -}

{-@ data Ur a where
        Ur :: a -> Ur a @-}
data Ur a where
  Ur :: a -> Ur a

{-# INLINE unur #-}
{-@ measure unur @-}
{- @ assume unur :: forall <p :: a -> Bool>.
        Ur (a<p>) -> a<p> @-} -- a{v : p(v)}
unur :: Ur a -. a
unur (Ur a) = a

{-# INLINE ur #-}
{-@ reflect ur @-}
{- @ assume ur :: forall <p :: a -> Bool>. a<p> -> Ur (a<p>) @-}
ur :: a -. Ur a
ur a = Unsafe.toLinear Ur a
