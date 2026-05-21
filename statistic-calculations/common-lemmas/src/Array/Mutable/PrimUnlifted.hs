{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE UnboxedTuples    #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE BangPatterns     #-}


module Array.Mutable.PrimUnlifted where

import qualified GHC.Exts as GHC
import qualified Data.Primitive.Types as P

--------------------------------------------------------------------------------
-- Mutable, unlifted array API only for primitive types
--------------------------------------------------------------------------------

newtype Array# a = Array# (GHC.MutableByteArray# GHC.RealWorld)

{-# INLINABLE make# #-}
make# :: P.Prim a => GHC.Int# -> a -> Array# a
make# len elt =
  case GHC.runRW# (GHC.newByteArray# nbytes) of
    (# _, arr #) -> Array# (fill# arr len elt)
  where
    nbytes = (P.sizeOf# elt) GHC.*# len


{-# INLINABLE fill# #-}
fill# :: P.Prim a => GHC.MutableByteArray# GHC.RealWorld -> GHC.Int# -> a -> GHC.MutableByteArray# GHC.RealWorld
fill# arr len elt =
  case GHC.runRW# (P.setByteArray# arr 0# (len GHC.-# 1#) elt) of
    _ -> arr

{-# INLINABLE makeNoFill# #-}
makeNoFill# :: P.Prim a => GHC.Int# -> a -> Array# a
makeNoFill# len elt =
  case GHC.runRW# (GHC.newByteArray# nbytes) of
    (# _, arr #) -> Array# arr
  where
    nbytes = (P.sizeOf# elt) GHC.*# len

{-# INLINABLE get# #-}
get# :: P.Prim a => Array# a -> GHC.Int# -> a
get# (Array# !arr) i =
  case GHC.runRW# (P.readByteArray# arr i) of
    (# _, !ret #) -> ret

{-# INLINABLE set# #-}
set# :: P.Prim a => Array# a -> GHC.Int# -> a -> Array# a
set# (Array# !arr) i !a =
  case GHC.runRW# (P.writeByteArray# arr i a) of
    _ -> Array# arr

{-# INLINABLE copy# #-}
copy# :: P.Prim a => a -> Array# a -> GHC.Int# -> Array# a -> GHC.Int# -> GHC.Int# -> Array# a
copy# elt (Array# !src) src_offset (Array# !dst) dst_offset n =
  case GHC.runRW# (GHC.copyMutableByteArray# src src_offset_bytes dst dst_offset_bytes n_bytes) of
    _ -> Array# dst
  where
    src_offset_bytes = (P.sizeOf# elt) GHC.*# src_offset
    dst_offset_bytes = (P.sizeOf# elt) GHC.*# dst_offset
    n_bytes          = (P.sizeOf# elt) GHC.*# n

{-# INLINABLE size# #-}
size# :: Array# a -> GHC.Int#
size# (Array# arr) =
  case GHC.runRW# (GHC.getSizeofMutableByteArray# arr) of
    (# _, !sz #) -> sz
