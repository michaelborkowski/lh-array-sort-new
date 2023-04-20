{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE UnboxedTuples    #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE LinearTypes      #-}

module Array.Mutable.Unlifted where

import qualified GHC.Exts as GHC

--------------------------------------------------------------------------------
-- Mutable, unlifted array API
--------------------------------------------------------------------------------

-- | A mutable array holding @a@s
newtype Array# a = Array# (GHC.MutableArray# GHC.RealWorld a)

-- The NOINLINE pragmas prevent the runRW# effect from being reordered.

{-# NOINLINE make# #-}
make# :: GHC.Int# -> a -> Array# a
make# len elt =
  case GHC.runRW# (GHC.newArray# len elt) of
    (# _, arr #) -> Array# arr


{-# NOINLINE get# #-}
get# :: Array# a -> GHC.Int# -> a
get# (Array# !arr) i =
  case GHC.runRW# (GHC.readArray# arr i) of
    (# _, !ret #) -> ret


{-# NOINLINE set# #-}
set# :: Array# a -> GHC.Int# -> a -> Array# a
set# (Array# !arr) i !a =
  case GHC.runRW# (GHC.writeArray# arr i a) of
    _ -> Array# arr

{-# NOINLINE copy# #-}
copy# :: Array# a -> GHC.Int# -> Array# a -> GHC.Int# -> GHC.Int# -> Array# a
copy# (Array# !src) src_offset (Array# !dst) dst_offset n =
  case GHC.runRW# (GHC.copyMutableArray# src src_offset dst dst_offset n) of
    _ -> Array# dst

size# :: Array# a -> GHC.Int#
size# (Array# arr) = GHC.sizeofMutableArray# arr
