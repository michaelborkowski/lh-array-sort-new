{-# LANGUAGE CPP #-}

{-@ LIQUID "--higherorder" @-}

module Par where

import           Linear.Common
import qualified Unsafe.Linear as Unsafe
import           Control.DeepSeq ( NFData(..) )
import           GHC.Conc ( par, pseq )
import qualified Control.Monad.Par as P

--------------------------------------------------------------------------------

-- | Parallel tuple combinators.
--   The top level one should be .|*|. which rseqs before return
--   but .||. can be used to get more than 2 way parallelism

infixr 1 .||.

#ifdef MUTABLE_ARRAYS

{-# INLINE tuple2 #-}
tuple2 :: (a -> b) -> a -> (c -> d) -> c -> (b, d)
tuple2 f1 x f2 y = p `par` q `pseq` (p,q)
  where
    p = f1 x
    q = f2 y

{-# INLINE tuple4 #-}
tuple4 :: (NFData a, NFData b) => (a -> b) -> a -> (c -> d) -> c
                               -> (e -> f) -> e -> (g -> h) -> g
                               -> ((b, d), (f, h))
tuple4 f1 x f2 y f3 z f4 a  = p `par` q `par` r `par` s `pseq` ((p,q), (r,s))
  where
    p = f1 x
    q = f2 y
    r = f3 z
    s = f4 a

{-# INLINABLE (.||.) #-}
(.||.) :: (NFData a) => a -. a -. (a,a)
--(.||.) = Unsafe.toLinear (\a -> Unsafe.toLinear (\b -> (a `par` b `pseq` (a,b))))
(.||.) = Unsafe.toLinear (\a -> Unsafe.toLinear (\b -> P.runPar $ do
                    i <- P.new
                    j <- P.new
                    P.fork (P.put_ i a)
                    P.fork (P.put_ j b)
                    a' <- P.get i 
                    b' <- P.get j
                    return (a', b') 
  ))


(.||||.) :: (NFData a) => a -. a -. a -. a -. ((a,a),(a,a))  
(.||||.) = Unsafe.toLinear (\a -> 
                Unsafe.toLinear (\b -> 
                    Unsafe.toLinear (\c -> 
                        Unsafe.toLinear (\d -> P.runPar $ do
                            i <- P.new
                            j <- P.new
                            k <- P.new
                            l <- P.new
                            P.fork (P.put_ i a)
                            P.fork (P.put_ j b)
                            P.fork (P.put_ k c)
                            P.fork (P.put_ l d)
                            a' <- P.get i 
                            b' <- P.get j
                            c' <- P.get k
                            d' <- P.get l
                            return ((a', b'), (c', d')) 
  ))))

{-
tuple2 :: (NFData a, NFData b) => (a -> b) -> a -> (a -> b) -> a -> (b, b)
tuple2 f x g y = P.runPar $ do
                     fx  <- P.spawn_ $ return (f x)
                     gy  <- P.spawn_ $ return (g y)
                     fx' <- P.get fx
                     gy' <- P.get gy
                     return (fx', gy')

tuple4 :: (NFData a, NFData b) => (a -> b) -> a -> (a -> b) -> a
                               -> (a -> b) -> a -> (a -> b) -> a -> ((b, b), (b, b))
tuple4 f x g y h z j w = P.runPar $ do
                             fx  <- P.spawn_ $ return (f x)
                             gy  <- P.spawn_ $ return (g y)
                             hz  <- P.spawn_ $ return (h z)
                             jw  <- P.spawn_ $ return (j w)
                             fx' <- P.get fx
                             gy' <- P.get gy
                             hz' <- P.get hz
                             jw' <- P.get jw
                             return ((fx', gy'), (hz', jw'))

(.||.) :: (NFData a, NFData b) => a -> b -> (a,b)
{-  this is what we want to use, but doesn't run quite yet -}
a .||. b = P.runPar $ do          -- or P.spawn_ ?
               a'  <- P.spawnP a
               b'  <- P.spawnP b
               a'' <- P.get a'
               b'' <- P.get b'
               return (a'', b'')
-}

#else
{-@ tuple2 :: f:_ -> x:a -> g:_ -> y:a -> { tup:_ | fst tup == f x && snd tup == g y } @-}
tuple2 :: (a -> b) -> a -> (a -> b) -> a -> (b, b)
tuple2 f x g y = (f x, g y)

{-@ tuple4 :: f:_ -> x:a -> g:_ -> y:a -> h:_ -> z:a -> j:_ -> w:a
                  -> { tup:_ | fst (fst tup) == f x && snd (fst tup) == g y &&
                               fst (snd tup) == h z && snd (snd tup) == j w } @-}
tuple4 :: (a -> b) -> a -> (a -> b) -> a
       -> (a -> b) -> a -> (a -> b) -> a -> ((b, b), (b, b))
tuple4 f x g y h z j w = ((f x, g y), (h z, j w))

{-@ (.||.) :: x:a -> y:b -> { tup:_ | x == fst tup && y = snd tup } @-}
(.||.) :: a -. b -. (a,b)
a .||. b = (a,b)

{-@ (.||||.) :: x:a -> y:a -> z:a -> w:a 
                    -> { tup:_ | x == fst (fst tup) && y == snd (fst tup) &&
                                 z == fst (snd tup) && w == snd (snd tup) } @-}
(.||||.) :: a -. a -. a -. a -. ((a,a),(a,a))  
(.||||.) a b c d = ((a, b), (c, d)) 
#endif
