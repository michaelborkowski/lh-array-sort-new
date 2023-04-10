{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict       #-}

module Fib where

import           Control.Monad.Par
import           Data.Int ( Int64 )

import           Microbench ( seqfib )
--------------------------------------------------------------------------------

{-# NOINLINE seqfib1 #-}
seqfib1 :: Int64 -> Int64
seqfib1 !n | n < 2 = 1
seqfib1 !n = seqfib1 (n-1) + seqfib1 (n-2)

-- Par monad version, with threshold:
parfib1 :: Int64 -> Par Int64
parfib1 !n | n <= 32 = return $ seqfib n
parfib1 !n = do
    xf <- spawn_$ parfib1 (n-1)
    y  <-         parfib1 (n-2)
    x  <- get xf
    return (x+y)
