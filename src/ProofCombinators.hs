

module ProofCombinators ((?){-}, pleUnfold-}, ur, unur, Ur(..) ) where

import Linear.Common
import qualified Unsafe.Linear as Unsafe
import Language.Haskell.Liquid.ProofCombinators (Proof)

import Data.Unrestricted.Linear (Ur(..))

-- half-monomorphic ? operator with linear type signature
{-@ (?) :: x:a -> Proof -> { v:a | v = x } @-}
(?) :: a -. (Proof -> a)
(?) x _ = x

{- @ reflect pleUnfold @- }
pleUnfold :: a %1-> a 
pleUnfold x = x -}

{-# INLINE unur #-}
{-@ measure unur @-}
unur :: Ur a -. a
unur (Ur a) = a

{-# INLINE ur #-}
{-@ assume ur :: a -> Ur a @-}
ur :: a -. Ur a
ur a = Unsafe.toLinear Ur a
