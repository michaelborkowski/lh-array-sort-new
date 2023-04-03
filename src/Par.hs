{-# LANGUAGE CPP #-}

module Par where

import           Control.DeepSeq ( NFData(..) )

--------------------------------------------------------------------------------

-- | Parallel tuple combinators.
--   The top level one should be .|*|. which rseqs before return
--   but .||. can be used to get more than 2 way parallelism

infixr 1 .||.

#ifdef MUTABLE_ARRAYS

tuple2 :: (NFData a, NFData b) => (a -> b) -> a -> (a -> b) -> a -> (b, b)
tuple2 = _todo

tuple4 :: (NFData a, NFData b) => (a -> b) -> a -> (a -> b) -> a
                               -> (a -> b) -> a -> (a -> b) -> a -> ((b, b), (b, b))
tuple4 = _todo

(.||.) :: (NFData a, NFData b) => a -> b -> (a,b)
a .||. b = _todo

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
(.||.) :: a -> b -> (a,b)
a .||. b = (a,b)
#endif
