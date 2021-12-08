{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

-- TODO: cannot only exposing certain functions otherwise LH complains 
module Array where -- works
-- module Array (Array, make, set, size, lma_gs, lma_gns) where -- won't work if uncomment

import           Language.Haskell.Liquid.ProofCombinators

{-@ data Array a = Arr {  lst   :: _
                        , left  :: {v: Nat | v <= (len lst) }
                        , right :: {v: Nat | v >= left && v <= (len lst)}
                        }
  @-}

data Array a = Arr { lst   :: [a] 
                   , left  :: Int 
                   , right :: Int}

{-@ reflect make @-}
{-@ make :: n:Nat -> x:_ -> xs:{(size xs) = n} @-}
make :: Int -> a -> Array a
make 0 x = Arr [] 0 0
make n x = let Arr lst l r = make (n-1) x in Arr (x:lst) l (r+1)

{-@ measure size @-}
{-@ size :: xs:_ -> Nat @-}
size :: Array a -> Int
size (Arr _ l r) = r-l

{-@ reflect getList @-}
{-@ getList :: xs:_ -> {n:Nat | n < len xs } -> x:_ @-}
getList :: [a] -> Int -> a
getList (x:_) 0 = x
getList (_:xs) n = getList xs (n-1)

{-@ reflect get @-}
{-@ get :: xs:_ -> {n:Nat | n < size xs } -> x:_ @-}
get :: Array a -> Int -> a
get (Arr lst l r) n = getList lst (l+n)

{-@ reflect setList @-}
{-@ setList :: xs:_ -> {n:Nat | n < len xs } -> x:_ -> nxs:{(len nxs) = (len xs)} @-}
setList :: [a] -> Int -> a -> [a]
setList (x:xs) 0 y = (y:xs)
setList (x:xs) n y = x:(setList xs (n-1) y)

{-@ reflect set @-}
{-@ set :: xs:_ -> {n:Nat | n < size xs } -> x:_ -> nxs:{(size nxs) = (size xs)} @-}
set :: Array a -> Int -> a -> Array a
set (Arr lst l r) n y = Arr (setList lst (l+n) y) l r

{-@ reflect slice @-}
{-@ slice :: xs:_ -> {l:Nat | l <= size xs } -> {r:Nat | r <= size xs && l <= r} -> ys:{size ys = r-l} @-}
slice :: Array a -> Int -> Int -> Array a 
slice (Arr lst l r) l' r' = Arr lst (l+l') (l+r')

--------------------------------------------------------------------------------
-- | Proofs
--------------------------------------------------------------------------------

-- lemma showing that get n from set n xs x is x
{-@ lma_gs_list :: xs:_ -> n:{v:Nat | v < len xs } -> x:_ 
      -> {getList (setList xs n x) n = x} @-}
lma_gs_list :: [a] -> Int -> a -> Proof
lma_gs_list (x:xs) 0 x' 
  = getList (setList (x:xs) 0 x') 0 
  -- === getList (x':xs) 0
  === x'
  *** QED
lma_gs_list (x:xs) n x' 
  =  getList (setList (x:xs) n x') n
  -- === getList (x:(setList xs (n-1) x')) n
  -- === getList (setList xs (n-1) x') (n-1)
    ? lma_gs_list xs (n-1) x'
  === x'
  *** QED

{-@ lma_gs :: xs:_ -> n:{v:Nat | v < size xs } -> x:_ 
      -> {get (set xs n x) n = x} @-}
lma_gs :: Array a -> Int -> a -> Proof
lma_gs (Arr lst l r) n x = lma_gs_list lst (l+n) x

-- lemma showing that get n from set m xs x is 
{-@ lma_gns_list :: xs:_ -> n:{v:Nat | v < len xs } -> m:{v:Nat | v /= n && v < len xs} -> x:_ 
      -> {getList (setList xs n x) m = getList xs m} @-}
lma_gns_list :: [a] -> Int -> Int -> a -> Proof
lma_gns_list (x:xs) 0 m x'
  = getList (setList (x:xs) 0 x') m
  -- === getList (x':xs) m
  -- === getList xs (m-1)
  === getList (x:xs) m
  *** QED

lma_gns_list (x:xs) n 0 x'
  = getList (setList (x:xs) n x') 0
  -- === getList (x:(setList xs (n-1) x')) 0
  -- === x
  === getList (x:xs) 0
  *** QED

lma_gns_list (x:xs) n m x'
  = getList (setList (x:xs) n x') m
  -- === getList (x:(setList xs (n-1) x')) m
  -- === getList (setList xs (n-1) x') (m-1)
    ? lma_gns_list xs (n-1) (m-1) x'
  -- === getList xs (m-1)
  === getList (x:xs) m
  *** QED

{-@ lma_gns :: xs:_ -> n:{v:Nat | v < size xs } -> m:{v:Nat | v /= n && v < size xs} -> x:_ 
      -> {get (set xs n x) m = get xs m} @-}
lma_gns :: Array a -> Int -> Int -> a -> Proof
lma_gns (Arr lst l r) n m x = lma_gns_list lst (l+n) (l+m) x