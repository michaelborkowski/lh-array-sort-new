{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}


-- {-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Equivalence where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import qualified Data.Set as S
-- import           Expressions 
import           Imp 
import           BigStep
import           Array



equal_perm :: Array a -> Array a -> Bool