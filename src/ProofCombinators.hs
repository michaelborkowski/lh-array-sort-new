{-# LANGUAGE LinearTypes   #-}

module ProofCombinators ((?){-}, pleUnfold-}) where

import Language.Haskell.Liquid.ProofCombinators (Proof)

-- half-monomorphic ? operator with linear type signature
{-@ (?) :: x:a -> Proof -> { v:a | v = x } @-}
(?) :: a %1-> Proof -> a
(?) x _ = x

{- @ reflect pleUnfold @- }
pleUnfold :: a %1-> a 
pleUnfold x = x -}