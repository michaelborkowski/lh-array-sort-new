{-# LANGUAGE CPP           #-}
-- We don't have any cyclic module dependencies. This file serves the role of
-- an ML-like signature file for the Array API.

{-@ LIQUID "--exact-data-cons" @-}

module Array
  (
    -- * Array type
  Array

    -- * Construction and querying
  , alloc, make, size, get, set, slice, append

    -- * Linear versions
  , size2, get2, slice2, copy2

    -- * Convert to/from lists
  , fromList, toList

    -- * Parallel tuple operator
--  , (.||.)

    -- * LiqidHaskell lemmas
  , lma_gs, lma_gns, lem_slice_append, lem_get_slice

  ) where

import ProofCombinators (Ur(..))
import Language.Haskell.Liquid.ProofCombinators (Proof)

import Linear.Common
#ifdef MUTABLE_ARRAYS
import           Array.Mutable (Array, HasPrim(..))
#else
import           Array.List    (Array, HasPrim(..))
#endif

--------------------------------------------------------------------------------

-- type Array a = A.Array a

alloc    :: HasPrim a => Int -> a -> (Array a -. Ur b) -. Ur b
make     :: Int -> a -> Array a
size     :: Array a -> Int
get      :: Array a -> Int -> a
set      :: Array a -> Int -> a -> Array a
slice    :: Array a -> Int -> Int -> Array a
append   :: Array a -> Array a -> Array a
--splitMid :: Array a -> (Array a, Array a) -- not in TCB
--swap :: Array a -> Int -> Int -> Array a  -- not in TCB
size2    :: Array a -. (Int, Array a)
get2     :: Array a -> Int -> (a, Array a)
slice2   :: Array a -> Int -> Int -> (Array a, Array a)
copy2    :: Array a -> Int -> Array a -> Int -> Int -> (Array a, Array a)
fromList :: [a] -> Array a
toList   :: Array a -> [a]

-- TODO:
-- size2 :: Array a -. (Ur Int, Array a)
-- get2 :: Array a -. Int -> (Ur a, Array a)


-- This doesn't belong here, and GHC insists it cannot go here because it's not 
--   defined in Array.hs
-- Parallel tuple combinator.
-- (.||.) :: a -> b -> (a,b)

--------------------------------------------------------------------------------

lma_gs           :: HasPrim a => Array a -> Int -> a -> Proof
lma_gns          :: HasPrim a => Array a -> Int -> Int -> a -> Proof
lem_slice_append :: Array a -> Array a -> Proof
lem_get_slice    :: Array a -> Int -> Int -> Int -> Proof
