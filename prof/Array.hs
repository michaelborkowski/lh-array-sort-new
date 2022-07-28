{-# LANGUAGE GADTs           #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE ConstraintKinds #-}


module Array (Array(..), ArrayElt, make, size, get, set, slice, fromList) where

import           Prelude
import           GHC.Generics ( Generic )
import           Control.DeepSeq ( NFData )

-- import qualified Data.Vector.Unboxed as V

--------------------------------------------------------------------------------

data Array a = Arr { lst   :: [a]
                   , left  :: Int
                   , right :: Int}
               deriving (Show, Generic)

instance NFData a => NFData (Array a)

type ArrayElt a = (Ord a, NFData a)

make :: Int -> a -> Array a
make 0 x = Arr [] 0 0
make n x = let Arr lst l r = make (n-1) x in Arr (x:lst) l (r+1)

size :: Array a -> Int
size (Arr _ l r) = r-l

getList :: [a] -> Int -> a
getList (x:_) 0 = x
getList (_:xs) n = getList xs (n-1)

get :: Array a -> Int -> a
get (Arr lst l r) n = getList lst (l+n)

setList :: [a] -> Int -> a -> [a]
setList (x:xs) 0 y = (y:xs)
setList (x:xs) n y = x:(setList xs (n-1) y)

set :: Array a -> Int -> a -> Array a
set (Arr lst l r) n y = Arr (setList lst (l+n) y) l r

slice :: Array a -> Int -> Int -> Array a
slice (Arr lst l r) l' r' = Arr lst (l+l') (l+r')

--append :: Array a -> Array a -> Array a
--append = (++)

fromList :: [a] -> Array a
fromList ls = Arr ls 0 (length ls)


--------------------------------------------------------------------------------

-- type ArrayElt a = (Ord a, NFData a, V.Unbox a)

-- data Array a =  MkArray (V.Vector a)
--   deriving (Show, Generic)

-- instance NFData a => NFData (Array a)

-- make :: V.Unbox a => Int -> a -> Array a
-- make n x = MkArray $ V.generate n (const x)

-- size :: V.Unbox a => Array a -> Int
-- size (MkArray xs) = V.length xs

-- get :: V.Unbox a => Array a -> Int -> a
-- get (MkArray xs) i = xs V.! i

-- set :: V.Unbox a => Array a -> Int -> a -> Array a
-- set (MkArray xs) i y = MkArray $ V.unsafeUpd xs [(i,y)]

-- slice :: V.Unbox a => Array a -> Int -> Int -> Array a
-- slice (MkArray xs) l' r' = MkArray $ V.unsafeSlice l' (r'-l') xs

-- -- --append :: Array a -> Array a -> Array a
-- -- --append = (++)

-- fromList :: V.Unbox a => [a] -> Array a
-- fromList ls = MkArray $ V.fromList ls
