

module ProofCombinators ((?){-}, pleUnfold-}, ur, unur, Ur(..) ) where

import Linear.Common
import Language.Haskell.Liquid.ProofCombinators (Proof)

import Data.Unrestricted.Linear (Ur(..))

-- half-monomorphic ? operator with linear type signature
{-@ (?) :: x:a -> Proof -> { v:a | v = x } @-}
(?) :: a -. (Proof -> a)
(?) x _ = x

{- @ reflect pleUnfold @- }
pleUnfold :: a %1-> a 
pleUnfold x = x -}

{-@ measure unur @-}
unur :: Ur a -. a
unur (Ur a) = a

{-@ assume ur :: a -> Ur a @-}
ur :: a -. Ur a
ur a = Ur a
