{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}

{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Microbench where

import           GHC.Conc ( par, pseq )
import           Data.Int ( Int64 )
import qualified Array as A
import           Par
import           Control.Monad.Par as P

import qualified Data.Primitive.Types as P


--------------------------------------------------------------------------------

type HasPrimNum a =
#ifdef PRIM_MUTABLE_ARRAYS
  (P.Prim a, Num a)
#else
  (Num a)
#endif

{-@ sumArray :: xs:_ -> a @-}
sumArray :: HasPrimNum a => A.Array a -> a
sumArray arr = go 0 0 (A.size arr)
  where
    {-@ go :: _ -> i:Nat -> { n:Nat | i <= n && n == A.size arr } 
                -> _ / [n-i] @-}
    go !acc !idx !n =
      if idx == n
      then acc
      else go (acc + A.get arr idx) (idx+1) n

{-@ ignore sumArray_par @-}
sumArray_par :: HasPrimNum a => Int -> A.Array a -> a
sumArray_par cutoff = go
  where
    go arr =
      let n = A.size arr in
        if n <= cutoff
        then sumArray arr
        else let half = n `div` 2
                 !(left,right) = A.splitAt half arr
                 x = go left
                 y = go right
             in x `par` y `pseq` x+y

{-@ ignore fillArray @-}
fillArray ::
#ifdef PRIM_MUTABLE_ARRAYS
  (P.Prim a) =>
#endif
  (Int, a) -> A.Array a
fillArray (sz, val) = A.make sz val

{-# NOINLINE seqfib #-}
seqfib :: Int64 -> Int64
seqfib !n | n < 2 = 1
seqfib !n = seqfib (n-1) + seqfib (n-2)

parfib :: Int64 -> Int64
parfib !n | n <= 32 = seqfib n
parfib !n =
  x `par` y `pseq` (x+y)
  where
    x = parfib (n-1)
    y = parfib (n-2)

-- Par monad version, with threshold:
parfib1 :: Int64 -> Par Int64
parfib1 !n | n <= 32 = return $ seqfib n
parfib1 !n = do
    xf <- spawn_$ parfib1 (n-1)
    !y  <-        parfib1 (n-2)
    !x  <- get xf
    return (x+y)
