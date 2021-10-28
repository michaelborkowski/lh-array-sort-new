{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}


-- {-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Equivalence where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified Data.Set as S
import           Array



toSet :: Array a -> Int -> Int -> S.Set a
toSet xs n m = undefined


equal_perm :: Array a -> Array a -> Bool
equal_perm xs ys = (toSet xs) == (toSet ys)
