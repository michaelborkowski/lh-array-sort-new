module ProofCombinators ((?)) where

import Language.Haskell.Liquid.ProofCombinators (Proof)

-- half-monomorphic ? operator
{-@ (?) :: x:a -> Proof -> { v:a | v = x } @-}
(?) :: a -> Proof -> a
(?) x _ = x
