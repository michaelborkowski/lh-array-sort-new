{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Array (Array, make, get, set, size, fromList, lma_gs, lma_gns) where

import           ProofCombinators



type Array a = [a]


{-@ reflect fromList @-}
{-@ fromList :: xs:_ -> ys:{size ys == size xs} @-}
fromList :: [a] -> Array a
fromList xs = xs


{-@ reflect make @-}
{-@ make :: n:Nat -> x:_ -> xs:{(size xs) = n} @-}
make :: Int -> a -> Array a
make 0 x = []
make n x = (x:(make (n-1) x))

{-@ measure size @-}
-- {-@ reflect size @-}
{-@ size :: xs:_ -> Nat @-}
size :: Array a -> Int
size [] = 0
size (_:xs) = 1 + (size xs)

{-@ reflect get @-}
{-@ get :: xs:_ -> {n:Nat | n < size xs } -> x:_ @-}
get :: Array a -> Int -> a
get (x:_) 0 = x
get (_:xs) n = get xs (n-1)

{-@ reflect set @-}
{-@ set :: xs:_ -> {n:Nat | n < size xs } -> x:_ -> nxs:{(size nxs) = (size xs)} @-}
set :: Array a -> Int -> a -> Array a
set (x:xs) 0 y = (y:xs)
set (x:xs) n y = x:(set xs (n-1) y)

{-@ reflect insert @-}
{-@ insert :: xs:_ -> {n:Nat | n < size xs } -> x:_ -> nxs:_ @-}
insert :: Array a -> Int -> a -> Array a
insert (x:xs) 0 y = (y:x:xs)
insert (x:xs) n y = x:(insert xs (n-1) y)

-- proof

-- lemma showing that get n from set n xs x is x
{-@ lma_gs :: xs:_ -> n:{v:Nat | v < size xs } -> x:_ 
      -> {get (set xs n x) n = x} @-}
lma_gs :: Array a -> Int -> a -> Proof
lma_gs (x:xs) 0 x' 
  = get (set (x:xs) 0 x') 0 
  -- === get (x':xs) 0
  === x'
  *** QED
lma_gs (x:xs) n x' 
  =  get (set (x:xs) n x') n
  -- === get (x:(set xs (n-1) x')) n
  -- === get (set xs (n-1) x') (n-1)
    ? lma_gs xs (n-1) x'
  === x'
  *** QED

-- lemma showing that get n from set m xs x is 
{-@ lma_gns :: xs:_ -> n:{v:Nat | v < size xs } -> m:{v:Nat | v /= n && v < size xs} -> x:_ 
      -> {get (set xs n x) m = get xs m} @-}
lma_gns :: Array a -> Int -> Int -> a -> Proof
lma_gns (x:xs) 0 m x'
  = get (set (x:xs) 0 x') m
  -- === get (x':xs) m
  -- === get xs (m-1)
  === get (x:xs) m
  *** QED

lma_gns (x:xs) n 0 x'
  = get (set (x:xs) n x') 0
  -- === get (x:(set xs (n-1) x')) 0
  -- === x
  === get (x:xs) 0
  *** QED

lma_gns (x:xs) n m x'
  = get (set (x:xs) n x') m
  -- === get (x:(set xs (n-1) x')) m
  -- === get (set xs (n-1) x') (m-1)
    ? lma_gns xs (n-1) (m-1) x'
  -- === get xs (m-1)
  === get (x:xs) m
  *** QED