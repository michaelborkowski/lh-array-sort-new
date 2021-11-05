{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BagTest where

import Language.Haskell.Liquid.Bag as B
import Language.Haskell.Liquid.ProofCombinators

{-@ lem_size :: x:Int -> { pf:_ | put x empty == fromList [x] } @-}
lem_size :: Int -> Proof
lem_size n = () 
